use crate::ast::{Span, Spanned};
use crate::collections::HashMap;
use crate::compile::{CompileError, CompileErrorKind, CompileResult, CompileVisitor};
use crate::SourceId;
use std::fmt;

pub(crate) trait Variable: fmt::Debug + Copy + Spanned {
    /// Construct a new variable at the given offset.
    fn new(offset: usize, span: Span) -> Self;

    /// Get the span where the variable was moved.
    fn moved_at(&self) -> Option<Span>;

    /// Mark the variable as moved. Returns `None` if the variable wasn't already moved.
    fn mark_as_moved(&mut self, span: Span) -> Option<Span>;
}

#[derive(Debug, Clone)]
pub(crate) struct Scope<T> {
    /// Named variables.
    locals: HashMap<String, T>,
    /// The number of variables.
    pub(crate) total_var_count: usize,
    /// The number of variables local to this scope.
    pub(crate) local_var_count: usize,
}

impl<T> Scope<T>
where
    T: Variable,
{
    /// Construct a new locals handlers.
    fn new() -> Self {
        Self {
            locals: HashMap::new(),
            total_var_count: 0,
            local_var_count: 0,
        }
    }

    /// Construct a new child scope.
    fn child(&self) -> Self {
        Self {
            locals: HashMap::new(),
            total_var_count: self.total_var_count,
            local_var_count: 0,
        }
    }

    /// Insert a new local, and return the old one if there's a conflict.
    fn new_var(&mut self, name: &str, span: Span) -> CompileResult<usize> {
        let offset = self.total_var_count;

        let local = T::new(offset, span);

        self.total_var_count += 1;
        self.local_var_count += 1;

        if let Some(old) = self.locals.insert(name.to_owned(), local) {
            return Err(CompileError::new(
                span,
                CompileErrorKind::VariableConflict {
                    name: name.to_owned(),
                    existing_span: old.span(),
                },
            ));
        }

        Ok(offset)
    }

    /// Insert a new local, and return the old one if there's a conflict.
    fn decl_var(&mut self, name: &str, span: Span) -> usize {
        let offset = self.total_var_count;

        log::trace!("decl {} => {}", name, offset);

        self.locals.insert(name.to_owned(), T::new(offset, span));

        self.total_var_count += 1;
        self.local_var_count += 1;
        offset
    }

    /// Declare an anonymous variable.
    ///
    /// This is used if cleanup is required in the middle of an expression.
    fn decl_anon(&mut self, _span: Span) -> usize {
        let offset = self.total_var_count;
        self.total_var_count += 1;
        self.local_var_count += 1;
        offset
    }

    /// Undeclare the last anonymous variable.
    pub(crate) fn undecl_anon(&mut self, span: Span, n: usize) -> CompileResult<()> {
        self.total_var_count = self
            .total_var_count
            .checked_sub(n)
            .ok_or_else(|| CompileError::msg(&span, "totals out of bounds"))?;

        self.local_var_count = self
            .local_var_count
            .checked_sub(n)
            .ok_or_else(|| CompileError::msg(&span, "locals out of bounds"))?;

        Ok(())
    }

    /// Access the variable with the given name.
    fn get(&self, name: &str, span: Span) -> CompileResult<Option<T>> {
        if let Some(var) = self.locals.get(name) {
            if let Some(moved_at) = var.moved_at() {
                return Err(CompileError::new(
                    span,
                    CompileErrorKind::VariableMoved { moved_at },
                ));
            }

            return Ok(Some(*var));
        }

        Ok(None)
    }

    /// Access the variable with the given name.
    fn take(&mut self, name: &str, span: Span) -> CompileResult<Option<T>> {
        if let Some(var) = self.locals.get_mut(name) {
            if let Some(moved_at) = var.mark_as_moved(span) {
                return Err(CompileError::new(
                    span,
                    CompileErrorKind::VariableMoved { moved_at },
                ));
            }

            return Ok(Some(*var));
        }

        Ok(None)
    }
}

/// A guard returned from [push][Scopes::push].
///
/// This should be provided to a subsequent [pop][Scopes::pop] to allow it to be
/// sanity checked.
#[must_use]
pub(crate) struct ScopeGuard(usize);

pub(crate) struct Scopes<T> {
    scopes: Vec<Scope<T>>,
}

impl<T> Scopes<T>
where
    T: Variable,
{
    /// Construct a new collection of scopes.
    pub(crate) fn new() -> Self {
        Self {
            scopes: vec![Scope::new()],
        }
    }

    /// Try to get the local with the given name. Returns `None` if it's
    /// missing.
    pub(crate) fn try_get_var(
        &self,
        visitor: &mut dyn CompileVisitor,
        name: &str,
        source_id: SourceId,
        span: Span,
    ) -> CompileResult<Option<T>> {
        log::trace!("get var: {}", name);

        for scope in self.scopes.iter().rev() {
            if let Some(var) = scope.get(name, span)? {
                log::trace!("found var: {} => {:?}", name, var);
                visitor.visit_variable_use(source_id, var.span(), span);
                return Ok(Some(var));
            }
        }

        Ok(None)
    }

    /// Try to take the local with the given name. Returns `None` if it's
    /// missing.
    pub(crate) fn try_take_var(
        &mut self,
        visitor: &mut dyn CompileVisitor,
        name: &str,
        source_id: SourceId,
        span: Span,
    ) -> CompileResult<Option<T>> {
        log::trace!("get var: {}", name);

        for scope in self.scopes.iter_mut().rev() {
            if let Some(var) = scope.take(name, span)? {
                log::trace!("found var: {} => {:?}", name, var);
                visitor.visit_variable_use(source_id, var.span(), span);
                return Ok(Some(var));
            }
        }

        Ok(None)
    }

    /// Get the local with the given name.
    pub(crate) fn get_var(
        &self,
        visitor: &mut dyn CompileVisitor,
        name: &str,
        source_id: SourceId,
        span: Span,
    ) -> CompileResult<T> {
        match self.try_get_var(visitor, name, source_id, span)? {
            Some(var) => Ok(var),
            None => Err(CompileError::new(
                span,
                CompileErrorKind::MissingLocal {
                    name: name.to_owned(),
                },
            )),
        }
    }

    /// Take the local with the given name.
    pub(crate) fn take_var(
        &mut self,
        visitor: &mut dyn CompileVisitor,
        name: &str,
        source_id: SourceId,
        span: Span,
    ) -> CompileResult<T> {
        match self.try_take_var(visitor, name, source_id, span)? {
            Some(var) => Ok(var),
            None => Err(CompileError::new(
                span,
                CompileErrorKind::MissingLocal {
                    name: name.to_owned(),
                },
            )),
        }
    }

    /// Construct a new variable.
    pub(crate) fn new_var(&mut self, name: &str, span: Span) -> CompileResult<usize> {
        self.last_mut(span)?.new_var(name, span)
    }

    /// Declare the given variable.
    pub(crate) fn decl_var(&mut self, name: &str, span: Span) -> CompileResult<usize> {
        Ok(self.last_mut(span)?.decl_var(name, span))
    }

    /// Declare an anonymous variable.
    pub(crate) fn decl_anon(&mut self, span: Span) -> CompileResult<usize> {
        Ok(self.last_mut(span)?.decl_anon(span))
    }

    /// Declare an anonymous variable.
    pub(crate) fn undecl_anon(&mut self, span: Span, n: usize) -> CompileResult<()> {
        self.last_mut(span)?.undecl_anon(span, n)
    }

    /// Push a scope and return an index.
    pub(crate) fn push(&mut self, scope: Scope<T>) -> ScopeGuard {
        self.scopes.push(scope);
        ScopeGuard(self.scopes.len())
    }

    /// Pop the last scope and compare with the expected length.
    pub(crate) fn pop(&mut self, expected: ScopeGuard, span: Span) -> CompileResult<Scope<T>> {
        let ScopeGuard(expected) = expected;

        if self.scopes.len() != expected {
            return Err(CompileError::msg(
                &span,
                "the number of scopes do not match",
            ));
        }

        self.pop_unchecked(span)
    }

    /// Pop the last of the scope.
    pub(crate) fn pop_last(&mut self, span: Span) -> CompileResult<Scope<T>> {
        self.pop(ScopeGuard(1), span)
    }

    /// Pop the last scope and compare with the expected length.
    pub(crate) fn pop_unchecked(&mut self, span: Span) -> CompileResult<Scope<T>> {
        let scope = self
            .scopes
            .pop()
            .ok_or_else(|| CompileError::msg(&span, "missing parent scope"))?;

        Ok(scope)
    }

    /// Construct a new child scope and return its guard.
    pub(crate) fn push_child(&mut self, span: Span) -> CompileResult<ScopeGuard> {
        let scope = self.last(span)?.child();
        Ok(self.push(scope))
    }

    /// Construct a new child scope.
    pub(crate) fn child(&mut self, span: Span) -> CompileResult<Scope<T>> {
        Ok(self.last(span)?.child())
    }

    /// Get the local var count of the top scope.
    pub(crate) fn local_var_count(&self, span: Span) -> CompileResult<usize> {
        Ok(self.last(span)?.local_var_count)
    }

    /// Get the total var count of the top scope.
    pub(crate) fn total_var_count(&self, span: Span) -> CompileResult<usize> {
        Ok(self.last(span)?.total_var_count)
    }

    /// Get the local with the given name.
    fn last(&self, span: Span) -> CompileResult<&Scope<T>> {
        self.scopes
            .last()
            .ok_or_else(|| CompileError::msg(&span, "missing head of locals"))
    }

    /// Get the last locals scope.
    fn last_mut(&mut self, span: Span) -> CompileResult<&mut Scope<T>> {
        self.scopes
            .last_mut()
            .ok_or_else(|| CompileError::msg(&span, "missing head of locals"))
    }
}
