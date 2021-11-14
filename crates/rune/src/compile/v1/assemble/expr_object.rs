use crate::collections::{HashMap, HashSet};
use crate::compile::v1::assemble::prelude::*;

/// Compile a literal object.
impl Assemble for ast::ExprObject {
    fn assemble(&self, c: &mut Compiler<'_, '_>, needs: Needs) -> CompileResult<Asm> {
        let span = self.span();
        let guard = c.scopes.push_child(span)?;

        log::trace!(
            "ExprObject => {:?} {:?}",
            c.q.sources.source(c.source_id, span),
            needs
        );

        let mut keys = Vec::<Box<str>>::new();
        let mut check_keys = Vec::new();
        let mut keys_dup = HashMap::new();

        for (assign, _) in &self.assignments {
            let span = assign.span();
            let key = assign.key.resolve(c.q.storage(), c.q.sources)?;
            keys.push(key.as_ref().into());
            check_keys.push((key.as_ref().into(), assign.key.span()));

            if let Some(existing) = keys_dup.insert(key.into_owned(), span) {
                return Err(CompileError::new(
                    span,
                    CompileErrorKind::DuplicateObjectKey {
                        existing,
                        object: span,
                    },
                ));
            }
        }

        for (assign, _) in &self.assignments {
            let span = assign.span();

            if let Some((_, expr)) = &assign.assign {
                expr.assemble(c, Needs::Value)?.apply(c)?;
            } else {
                let key = assign.key.resolve(&c.q.storage, c.q.sources)?;
                let var = c.scopes.get_var(c.q.visitor, &*key, c.source_id, span)?;
                var.copy(&mut c.asm, span, format!("name `{}`", key));
            }
            c.scopes.decl_anon(span)?;
        }

        let slot = c.q.unit.new_static_object_keys_iter(span, &keys)?;

        match &self.ident {
            ast::ObjectIdent::Named(path) => {
                let named = c.convert_path_to_named(path)?;
                let meta = c.lookup_meta(path.span(), &named.item)?;

                match &meta.kind {
                    MetaKind::UnitStruct { .. } => {
                        check_object_fields(&HashSet::new(), check_keys, span, &meta.item.item)?;

                        let hash = Hash::type_hash(&meta.item.item);
                        c.asm.push(Inst::UnitStruct { hash }, span);
                    }
                    MetaKind::Struct { object, .. } => {
                        check_object_fields(&object.fields, check_keys, span, &meta.item.item)?;

                        let hash = Hash::type_hash(&meta.item.item);
                        c.asm.push(Inst::Struct { hash, slot }, span);
                    }
                    MetaKind::StructVariant { object, .. } => {
                        check_object_fields(&object.fields, check_keys, span, &meta.item.item)?;

                        let hash = Hash::type_hash(&meta.item.item);
                        c.asm.push(Inst::StructVariant { hash, slot }, span);
                    }
                    _ => {
                        return Err(CompileError::new(
                            span,
                            CompileErrorKind::UnsupportedLitObject { meta },
                        ));
                    }
                };
            }
            ast::ObjectIdent::Anonymous(..) => {
                c.asm.push(Inst::Object { slot }, span);
            }
        }

        // No need to encode an object since the value is not needed.
        if !needs.value() {
            c.diagnostics.not_used(c.source_id, span, c.context());
            c.asm.push(Inst::Pop, span);
        }

        c.scopes.pop(guard, span)?;
        Ok(Asm::top(span))
    }
}

fn check_object_fields(
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