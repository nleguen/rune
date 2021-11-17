use crate::ast::{self, Span, Spanned};
use crate::compile::hir::{self, Loops, ScopeGuard, Scopes, Variable};
use crate::compile::{
    Assembly, CompileError, CompileErrorKind, CompileResult, IrBudget, IrCompiler, IrInterpreter,
    Item, ItemMeta, Meta, Options, UnitBuilder,
};
use crate::parse::Resolve;
use crate::query::{Named, Query, QueryConstFn, Used};
use crate::runtime::{ConstValue, Inst};
use crate::{Context, Diagnostics, SourceId};

/// A needs hint for an expression.
/// This is used to contextually determine what an expression is expected to
/// produce.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Needs {
    Type,
    Value,
    None,
}

impl Needs {
    /// Test if any sort of value is needed.
    pub(crate) fn value(self) -> bool {
        matches!(self, Self::Type | Self::Value)
    }
}

pub(crate) struct Assembler<'a> {
    /// The source id of the source.
    pub(crate) source_id: SourceId,
    /// The context we are compiling for.
    pub(crate) context: &'a Context,
    /// Query system to compile required items.
    pub(crate) q: Query<'a>,
    /// The assembly we are generating.
    pub(crate) asm: &'a mut Assembly,
    /// Scopes defined in the compiler.
    pub(crate) scopes: Scopes<Var>,
    /// Context for which to emit warnings.
    pub(crate) contexts: Vec<Span>,
    /// The nesting of loop we are currently in.
    pub(crate) loops: Loops,
    /// Enabled optimizations.
    pub(crate) options: &'a Options,
    /// Compilation warnings.
    pub(crate) diagnostics: &'a mut Diagnostics,
}

impl<'a> Assembler<'a> {
    /// Access the meta for the given language item.
    pub fn try_lookup_meta(&mut self, span: Span, item: &Item) -> CompileResult<Option<Meta>> {
        log::trace!("lookup meta: {:?}", item);

        if let Some(meta) = self.q.query_meta(span, item, Default::default())? {
            log::trace!("found in query: {:?}", meta);
            self.q.visitor.visit_meta(self.source_id, &meta, span);
            return Ok(Some(meta));
        }

        if let Some(meta) = self.context.lookup_meta(item) {
            log::trace!("found in context: {:?}", meta);
            self.q.visitor.visit_meta(self.source_id, &meta, span);
            return Ok(Some(meta));
        }

        Ok(None)
    }

    /// Access the meta for the given language item.
    pub fn lookup_meta(&mut self, spanned: Span, item: &Item) -> CompileResult<Meta> {
        if let Some(meta) = self.try_lookup_meta(spanned, item)? {
            return Ok(meta);
        }

        Err(CompileError::new(
            spanned,
            CompileErrorKind::MissingItem { item: item.clone() },
        ))
    }

    /// Pop locals by simply popping them.
    pub(crate) fn locals_pop(&mut self, total_var_count: usize, span: Span) {
        match total_var_count {
            0 => (),
            1 => {
                self.asm.push(Inst::Pop, span);
            }
            count => {
                self.asm.push(Inst::PopN { count }, span);
            }
        }
    }

    /// Clean up local variables by preserving the value that is on top and
    /// popping the rest.
    ///
    /// The clean operation will preserve the value that is on top of the stack,
    /// and pop the values under it.
    pub(crate) fn locals_clean(&mut self, total_var_count: usize, span: Span) {
        match total_var_count {
            0 => (),
            count => {
                self.asm.push(Inst::Clean { count }, span);
            }
        }
    }

    /// Convert an [ast::Path] into a [Named] item.
    pub(crate) fn convert_path(&mut self, path: &ast::Path) -> CompileResult<Named> {
        self.q.convert_path(self.context, path)
    }

    /// Clean the last scope.
    pub(crate) fn clean_last_scope(
        &mut self,
        span: Span,
        expected: ScopeGuard,
        needs: Needs,
    ) -> CompileResult<()> {
        let scope = self.scopes.pop(expected, span)?;

        if needs.value() {
            self.locals_clean(scope.local_var_count, span);
        } else {
            self.locals_pop(scope.local_var_count, span);
        }

        Ok(())
    }

    /// Get the latest relevant warning context.
    pub(crate) fn context(&self) -> Option<Span> {
        self.contexts.last().copied()
    }

    /// Calling a constant function by id and return the resuling value.
    pub(crate) fn call_const_fn<S>(
        &mut self,
        spanned: S,
        meta: &Meta,
        from: &ItemMeta,
        query_const_fn: &QueryConstFn,
        args: &[(ast::Expr, Option<T![,]>)],
    ) -> Result<ConstValue, CompileError>
    where
        S: Copy + Spanned,
    {
        if query_const_fn.ir_fn.args.len() != args.len() {
            return Err(CompileError::new(
                spanned,
                CompileErrorKind::UnsupportedArgumentCount {
                    meta: meta.clone(),
                    expected: query_const_fn.ir_fn.args.len(),
                    actual: args.len(),
                },
            ));
        }

        let mut compiler = IrCompiler { q: self.q.borrow() };

        let mut compiled = Vec::new();

        // TODO: precompile these and fetch using opaque id?
        for ((a, _), name) in args.iter().zip(&query_const_fn.ir_fn.args) {
            compiled.push((compiler.compile(a)?, name));
        }

        let mut interpreter = IrInterpreter {
            budget: IrBudget::new(1_000_000),
            scopes: Default::default(),
            module: from.module.clone(),
            item: from.item.clone(),
            q: self.q.borrow(),
        };

        for (ir, name) in compiled {
            let value = interpreter.eval_value(&ir, Used::Used)?;
            interpreter.scopes.decl(name, value, spanned)?;
        }

        interpreter.module = query_const_fn.item.module.clone();
        interpreter.item = query_const_fn.item.item.clone();
        let value = interpreter.eval_value(&query_const_fn.ir_fn.ir, Used::Used)?;
        Ok(value.into_const(spanned)?)
    }
}

impl hir::Assembler<Var> for Assembler<'_> {
    fn resolve<'a, V>(&'a self, value: &V) -> CompileResult<V::Output>
    where
        V: Resolve<'a>,
    {
        Ok(value.resolve(&self.q.storage, self.q.sources)?)
    }

    fn lookup_meta(&mut self, spanned: Span, item: &Item) -> CompileResult<Meta> {
        Assembler::lookup_meta(self, spanned, item)
    }

    fn context(&self) -> &Context {
        &self.context
    }

    fn convert_path(&mut self, path: &ast::Path) -> CompileResult<Named> {
        Assembler::convert_path(self, path)
    }

    fn unit_mut(&mut self) -> &mut UnitBuilder {
        self.q.unit
    }

    fn try_get_var(&mut self, name: &str, span: Span) -> CompileResult<Option<Var>> {
        self.scopes
            .try_get_var(self.q.visitor, name, self.source_id, span)
    }

    fn remove_tuple_call_parens(&mut self, span: Span, tuple: Span) {
        self.diagnostics
            .remove_tuple_call_parens(self.source_id, span, tuple, self.context());
    }

    fn try_lookup_meta(&mut self, span: Span, item: &Item) -> CompileResult<Option<Meta>> {
        Assembler::try_lookup_meta(self, span, item)
    }
}

/// A locally declared variable, its calculated stack offset and where it was
/// declared in its source file.
#[derive(Debug, Clone, Copy)]
pub struct Var {
    /// Slot offset from the current stack frame.
    pub(crate) offset: usize,
    /// Token assocaited with the variable.
    span: Span,
    /// Variable has been taken at the given position.
    moved_at: Option<Span>,
}

impl Var {
    /// Copy the declared variable.
    pub(crate) fn copy<C>(&self, c: &mut Assembler<'_>, span: Span, comment: C)
    where
        C: AsRef<str>,
    {
        c.asm.push_with_comment(
            Inst::Copy {
                offset: self.offset,
            },
            span,
            comment,
        );
    }

    /// Move the declared variable.
    pub(crate) fn do_move<C>(&self, asm: &mut Assembly, span: Span, comment: C)
    where
        C: AsRef<str>,
    {
        asm.push_with_comment(
            Inst::Move {
                offset: self.offset,
            },
            span,
            comment,
        );
    }
}

impl Spanned for Var {
    fn span(&self) -> Span {
        self.span
    }
}

impl Variable for Var {
    fn new(offset: usize, span: Span) -> Self {
        Self {
            offset,
            span,
            moved_at: None,
        }
    }

    fn moved_at(&self) -> Option<Span> {
        self.moved_at
    }

    fn mark_as_moved(&mut self, span: Span) -> Option<Span> {
        if let Some(moved) = self.moved_at {
            return Some(moved);
        }

        self.moved_at = Some(span);
        None
    }
}
