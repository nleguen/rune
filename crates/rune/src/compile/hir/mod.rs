use crate::ast::{Span, Spanned};
use crate::collections::{HashMap, HashSet};
use crate::compile::ast;
use crate::compile::{
    CompileError, CompileErrorKind, CompileResult, Item, Meta, MetaKind, UnitBuilder,
};
use crate::parse::{Id, Resolve};
use crate::query::Named;
use crate::runtime::TypeCheck;
use crate::{Context, Hash};

mod scopes;
pub(crate) use self::scopes::{Scope, ScopeGuard, Scopes, Variable};

mod loops;
pub(crate) use self::loops::{Loop, Loops};

pub(crate) trait Assembler<T> {
    /// Resolve an identifier.
    fn resolve<'a, V>(&'a self, value: &V) -> CompileResult<V::Output>
    where
        V: Resolve<'a>;

    /// Lookup meta in the assembler.
    fn lookup_meta(&mut self, spanned: Span, item: &Item) -> CompileResult<Meta>;

    /// Access the context of the assembler.
    fn context(&self) -> &Context;

    /// Convert path.
    fn convert_path(&mut self, path: &ast::Path) -> CompileResult<Named>;

    /// Access mutable query.
    fn unit_mut(&mut self) -> &mut UnitBuilder;

    /// Try to get the given variable.
    fn try_get_var(&mut self, name: &str, span: Span) -> CompileResult<Option<T>>;

    /// Try to lookup meta.
    fn try_lookup_meta(&mut self, spanned: Span, item: &Item) -> CompileResult<Option<Meta>>;

    /// Emit diagnostics that tuple call parenthesis can be removed.
    fn remove_tuple_call_parens(&mut self, span: Span, tuple: Span);
}

pub(crate) enum Binding<'a> {
    Binding(Span, Box<str>, &'a ast::Pat),
    Ident(Span, Box<str>),
}

impl Binding<'_> {
    fn key(&self) -> &str {
        match self {
            Self::Binding(_, key, _) => key.as_ref(),
            Self::Ident(_, key) => key.as_ref(),
        }
    }
}

impl Spanned for Binding<'_> {
    fn span(&self) -> Span {
        match self {
            Self::Binding(span, _, _) => *span,
            Self::Ident(span, _) => *span,
        }
    }
}

pub(crate) struct PatObject<'a> {
    pub(crate) bindings: Vec<Binding<'a>>,
    pub(crate) type_check: TypeCheck,
    pub(crate) has_rest: bool,
    pub(crate) string_slots: Vec<usize>,
    pub(crate) keys: usize,
}

/// High-level processing of object patterns.
pub(crate) fn pat_object<'a, T>(
    ast: &'a ast::PatObject,
    c: &mut impl Assembler<T>,
) -> CompileResult<PatObject<'a>> {
    let span = ast.span();

    let mut string_slots = Vec::new();

    let mut keys_dup = HashMap::new();
    let mut keys = Vec::new();

    let mut bindings = Vec::new();
    let (has_rest, count) = pat_items_count(&ast.items)?;

    for (pat, _) in ast.items.iter().take(count) {
        let span = pat.span();

        let key = match pat {
            ast::Pat::PatBinding(binding) => {
                let key = c.resolve(&binding.key)?;
                bindings.push(Binding::Binding(
                    binding.span(),
                    key.as_ref().into(),
                    &*binding.pat,
                ));
                key.into_owned()
            }
            ast::Pat::PatPath(path) => {
                let ident = match path.path.try_as_ident() {
                    Some(ident) => ident,
                    None => {
                        return Err(CompileError::new(
                            span,
                            CompileErrorKind::UnsupportedPatternExpr,
                        ));
                    }
                };

                let key = c.resolve(ident)?;
                bindings.push(Binding::Ident(path.span(), key.into()));
                key.to_owned()
            }
            _ => {
                return Err(CompileError::new(
                    span,
                    CompileErrorKind::UnsupportedPatternExpr,
                ));
            }
        };

        string_slots.push(c.unit_mut().new_static_string(span, &key)?);

        if let Some(existing) = keys_dup.insert(key.clone(), span) {
            return Err(CompileError::new(
                span,
                CompileErrorKind::DuplicateObjectKey {
                    existing,
                    object: ast.span(),
                },
            ));
        }

        keys.push(key);
    }

    let keys = c.unit_mut().new_static_object_keys_iter(span, &keys[..])?;

    let type_check = match &ast.ident {
        ast::ObjectIdent::Named(path) => {
            let span = path.span();

            let named = c.convert_path(path)?;
            let meta = c.lookup_meta(span, &named.item)?;

            let (object, type_check) = match &meta.kind {
                MetaKind::Struct {
                    object, type_hash, ..
                } => {
                    let type_check = TypeCheck::Type(*type_hash);
                    (object, type_check)
                }
                MetaKind::StructVariant {
                    object, type_hash, ..
                } => {
                    let type_check = TypeCheck::Variant(*type_hash);
                    (object, type_check)
                }
                _ => {
                    return Err(CompileError::expected_meta(
                        span,
                        meta,
                        "type that can be used in an object pattern",
                    ));
                }
            };

            let fields = &object.fields;

            for binding in &bindings {
                if !fields.contains(binding.key()) {
                    return Err(CompileError::new(
                        span,
                        CompileErrorKind::LitObjectNotField {
                            field: binding.key().into(),
                            item: meta.item.item.clone(),
                        },
                    ));
                }
            }

            type_check
        }
        ast::ObjectIdent::Anonymous(..) => TypeCheck::Object,
    };

    Ok(PatObject {
        bindings,
        type_check,
        has_rest,
        string_slots,
        keys,
    })
}

/// Kind of call.
pub(crate) enum Call<T> {
    Var {
        /// The variable slot being called.
        var: T,
        /// The name of the variable being called.
        name: Box<str>,
    },
    Instance {
        /// Hash of the fn being called.
        hash: Hash,
    },
    Meta {
        /// Meta being called.
        meta: Meta,
        /// The hash of the meta thing being called.
        hash: Hash,
    },
    /// An expression being called.
    Expr,
    /// A constant function call.
    ConstFn {
        /// Meta of the constand function.
        meta: Meta,
        /// The identifier of the constant function.
        id: Id,
    },
}

/// High-level processing of call expressions.
pub(crate) fn expr_call<T>(
    ast: &ast::ExprCall,
    c: &mut impl Assembler<T>,
) -> CompileResult<Call<T>> {
    let span = ast.span();

    match &ast.expr {
        ast::Expr::Path(path) => {
            let named = c.convert_path(path)?;

            if let Some(name) = named.as_local() {
                let local = c.try_get_var(name, path.span())?;

                if let Some(var) = local {
                    return Ok(Call::Var {
                        var,
                        name: name.into(),
                    });
                }
            }

            let meta = c.lookup_meta(path.span(), &named.item)?;

            match &meta.kind {
                MetaKind::UnitStruct { .. } | MetaKind::UnitVariant { .. } => {
                    if !ast.args.is_empty() {
                        return Err(CompileError::new(
                            span,
                            CompileErrorKind::UnsupportedArgumentCount {
                                meta: meta.clone(),
                                expected: 0,
                                actual: ast.args.len(),
                            },
                        ));
                    }
                }
                MetaKind::TupleStruct { tuple, .. } | MetaKind::TupleVariant { tuple, .. } => {
                    if tuple.args != ast.args.len() {
                        return Err(CompileError::new(
                            span,
                            CompileErrorKind::UnsupportedArgumentCount {
                                meta: meta.clone(),
                                expected: tuple.args,
                                actual: ast.args.len(),
                            },
                        ));
                    }

                    if tuple.args == 0 {
                        let tuple = path.span();
                        c.remove_tuple_call_parens(span, tuple);
                    }
                }
                MetaKind::Function { .. } => (),
                MetaKind::ConstFn { id, .. } => {
                    let id = *id;
                    return Ok(Call::ConstFn { meta, id });
                }
                _ => {
                    return Err(CompileError::expected_meta(
                        span,
                        meta,
                        "something that can be called as a function",
                    ));
                }
            };

            let hash = Hash::type_hash(&meta.item.item);
            return Ok(Call::Meta { meta, hash });
        }
        ast::Expr::FieldAccess(access) => {
            if let ast::ExprFieldAccess {
                expr_field: ast::ExprField::Path(path),
                ..
            } = &**access
            {
                if let Some(ident) = path.try_as_ident() {
                    let ident = c.resolve(ident)?;
                    let hash = Hash::instance_fn_name(ident);
                    return Ok(Call::Instance { hash });
                }
            }
        }
        _ => {}
    };

    Ok(Call::Expr)
}

pub(crate) struct PatTuple {
    pub(crate) type_check: TypeCheck,
    pub(crate) len: usize,
    pub(crate) has_rest: bool,
}

/// High-level processing of tuple patterns.
pub(crate) fn pat_tuple<T>(
    ast: &ast::PatTuple,
    c: &mut impl Assembler<T>,
) -> CompileResult<PatTuple> {
    let span = ast.span();

    let (has_rest, len) = pat_items_count(&ast.items)?;

    let type_check = if let Some(path) = &ast.path {
        let named = c.convert_path(path)?;
        let meta = c.lookup_meta(path.span(), &named.item)?;

        let (args, type_check) = match meta.as_tuple() {
            Some((args, type_check)) => (args, type_check),
            None => {
                return Err(CompileError::expected_meta(
                    span,
                    meta,
                    "type that can be used in a tuple pattern",
                ));
            }
        };

        if !(args == len || len < args && has_rest) {
            return Err(CompileError::new(
                span,
                CompileErrorKind::UnsupportedArgumentCount {
                    meta,
                    expected: args,
                    actual: len,
                },
            ));
        }

        c.context()
            .type_check_for(&meta.item.item)
            .unwrap_or(type_check)
    } else {
        TypeCheck::Tuple
    };

    Ok(PatTuple {
        type_check,
        len,
        has_rest,
    })
}

pub(crate) enum AssignTarget<'a> {
    /// <target> = <value>
    Ident(&'a ast::Ident),
    /// <target>.<field> = <value>
    ObjectField(&'a ast::Expr, &'a ast::Ident),
    /// <target>.<number> = <value>
    TupleField(&'a ast::Expr, &'a ast::LitNumber),
    /// <target>[<expr>] = <value>
    ExprIndex(&'a ast::ExprIndex),
}

/// High-level processing of assign targets.
pub(crate) fn expr_assign_target<'a>(ast: &'a ast::ExprAssign) -> CompileResult<AssignTarget<'a>> {
    match &ast.lhs {
        ast::Expr::Path(path) => {
            if let Some(ident) = path.try_as_ident() {
                return Ok(AssignTarget::Ident(ident));
            }
        }
        ast::Expr::FieldAccess(e) => match &e.expr_field {
            ast::ExprField::Path(path) => {
                if let Some(ident) = path.try_as_ident() {
                    return Ok(AssignTarget::ObjectField(&e.expr, ident));
                }
            }
            ast::ExprField::LitNumber(n) => {
                return Ok(AssignTarget::TupleField(&e.expr, n));
            }
        },
        ast::Expr::Index(e) => {
            return Ok(AssignTarget::ExprIndex(e));
        }
        _ => {}
    };

    Err(CompileError::new(
        ast.span(),
        CompileErrorKind::UnsupportedAssignExpr,
    ))
}

/// Test if the given pattern is open or not.
pub(crate) fn pat_items_count<'a, I: 'a, U: 'a>(items: I) -> Result<(bool, usize), CompileError>
where
    I: IntoIterator<Item = &'a (ast::Pat, U)>,
    I::IntoIter: DoubleEndedIterator,
{
    let mut it = items.into_iter();

    let (has_rest, mut count) = match it.next_back() {
        Some((pat, _)) => {
            if matches!(pat, ast::Pat::PatRest(..)) {
                (true, 0)
            } else {
                (false, 1)
            }
        }
        None => return Ok((false, 0)),
    };

    for (pat, _) in it {
        if let ast::Pat::PatRest(rest) = pat {
            return Err(CompileError::new(
                rest,
                CompileErrorKind::UnsupportedPatternRest,
            ));
        }

        count += 1;
    }

    Ok((has_rest, count))
}

pub(crate) fn check_object_fields(
    fields: &HashSet<Box<str>>,
    check_keys: Vec<(Box<str>, Span)>,
    span: Span,
    item: &Item,
) -> CompileResult<()> {
    let mut fields = fields.clone();

    for (field, span) in check_keys {
        if !fields.remove(&field) {
            return Err(CompileError::new(
                span,
                CompileErrorKind::LitObjectNotField {
                    field,
                    item: item.clone(),
                },
            ));
        }
    }

    if let Some(field) = fields.into_iter().next() {
        return Err(CompileError::new(
            span,
            CompileErrorKind::LitObjectMissingField {
                field,
                item: item.clone(),
            },
        ));
    }

    Ok(())
}

pub(crate) enum Path<T> {
    /// Path resolves to a `self` value.
    SelfValue,
    /// Path resolved to a variable.
    Var(T, Box<str>),
    /// A no-argument meta.
    Meta(Meta),
}

pub(crate) fn path<T>(
    ast: &ast::Path,
    c: &mut impl Assembler<T>,
    value: bool,
) -> CompileResult<Path<T>> {
    let span = ast.span();

    if let Some(ast::PathKind::SelfValue) = ast.as_kind() {
        return Ok(Path::SelfValue);
    }

    let named = c.convert_path(ast)?;

    if value {
        if let Some(local) = named.as_local() {
            if let Some(var) = c.try_get_var(local, span)? {
                return Ok(Path::Var(var, local.into()));
            }
        }
    }

    if let Some(m) = c.try_lookup_meta(span, &named.item)? {
        return Ok(Path::Meta(m));
    }

    if let (true, Some(local)) = (value, named.as_local()) {
        // light heuristics, treat it as a type error in case the
        // first character is uppercase.
        if !local.starts_with(char::is_uppercase) {
            return Err(CompileError::new(
                span,
                CompileErrorKind::MissingLocal {
                    name: local.to_owned(),
                },
            ));
        }
    };

    Err(CompileError::new(
        span,
        CompileErrorKind::MissingItem {
            item: named.item.clone(),
        },
    ))
}
