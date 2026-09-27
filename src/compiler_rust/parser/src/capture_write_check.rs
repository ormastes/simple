//! Static check: a nested `fn` or lambda must not assign to a local of an
//! enclosing function, lambda or colon-block.
//!
//! Language rule (`.claude/rules/language.md:22`, owner ruling 2026-09-27):
//! nested closures capture by value and are READ-ONLY. Before this check such
//! a write was silently lost: the nested body wrote a copy (or minted a fresh
//! local) and the enclosing binding kept its old value. The ruling makes that
//! a loud compile error. Module-level globals are not captures and stay
//! writable from any nested body.
//!
//! Scope model: one frame per function body, lambda body, colon-block and
//! `DoBlock`. Function and lambda frames (`fn` declarations, `\x:`, `fn():`)
//! are capture BOUNDARIES. Colon-blocks (`describe "x":`, `it "y":`,
//! `after_each:`, marked `MoveMode::ColonBlock`) and bare `DoBlock`s are
//! scopes but NOT boundaries: the ruling covers nested fns and lambdas, and
//! the runtime gives some colon-blocks explicit write-back (`after_each`
//! hooks; test/01_unit/std/feature_validation/after_each_capture_writeback_spec.spl).
//! A local declared inside a colon-block is still a local, so a nested `fn`
//! in an `it` block writing an `it`-block `var` is reported.
//! `if`/`for`/`while`/`match` bodies share
//! their enclosing frame, which can only widen what counts as "local to the
//! current function" and therefore never manufactures an error.
//!
//! The walk covers statements and the expression forms that can carry a
//! nested body (calls, method calls, lambdas, colon-blocks, `if`/`match`
//! expressions, operators, literals). Other expression forms are not
//! descended into, so the check can miss a write but never invents one.

use std::collections::HashSet;

use crate::ast::{Argument, Block, Expr, FunctionDef, MatchArm, Module, MoveMode, Node, Pattern};

/// One rejected write: the captured name and the nested body's name
/// (`"<closure>"` for lambdas and colon-blocks).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaptureWrite {
    pub name: String,
    pub in_fn: String,
    pub line: usize,
}

impl CaptureWrite {
    /// The diagnostic text shared by every engine that reports this error.
    pub fn message(&self) -> String {
        let site = if self.in_fn == "<closure>" {
            "a closure".to_string()
        } else {
            format!("nested fn `{}`", self.in_fn)
        };
        format!(
            "cannot assign to captured variable `{}` inside {} (line {}): closures capture enclosing locals by value and are read-only; return the new value or use a module-level `var`",
            self.name, site, self.line
        )
    }
}

struct Frame {
    names: HashSet<String>,
    boundary: bool,
    module: bool,
}

struct Checker {
    frames: Vec<Frame>,
    fn_names: Vec<String>,
    pending_fn: Option<String>,
    found: Vec<CaptureWrite>,
}

/// Returns every assignment in `module` that writes a captured enclosing
/// local from a nested `fn` or lambda, in source order.
pub fn find_captured_local_writes(module: &Module) -> Vec<CaptureWrite> {
    let mut checker = Checker {
        frames: vec![Frame {
            names: HashSet::new(),
            boundary: false,
            module: true,
        }],
        fn_names: Vec::new(),
        pending_fn: None,
        found: Vec::new(),
    };
    for item in &module.items {
        checker.node(item);
    }
    checker.found
}

fn pattern_names(pattern: &Pattern, out: &mut Vec<String>) {
    match pattern {
        Pattern::Identifier(n) | Pattern::MutIdentifier(n) | Pattern::MoveIdentifier(n) => out.push(n.clone()),
        Pattern::Tuple(ps) | Pattern::Array(ps) | Pattern::Or(ps) => ps.iter().for_each(|p| pattern_names(p, out)),
        Pattern::Struct { fields, .. } => fields.iter().for_each(|(_, p)| pattern_names(p, out)),
        Pattern::Enum { payload: Some(ps), .. } => ps.iter().for_each(|p| pattern_names(p, out)),
        Pattern::Typed { pattern, .. } => pattern_names(pattern, out),
        _ => {}
    }
}

impl Checker {
    fn declare(&mut self, name: &str) {
        if let Some(frame) = self.frames.last_mut() {
            frame.names.insert(name.to_string());
        }
    }

    fn declare_pattern(&mut self, pattern: &Pattern) {
        let mut names = Vec::new();
        pattern_names(pattern, &mut names);
        for n in names {
            self.declare(&n);
        }
    }

    /// `None` = not bound anywhere; `Some(true)` = a captured enclosing local.
    fn is_captured_local(&self, name: &str) -> Option<bool> {
        let mut crossed = false;
        for frame in self.frames.iter().rev() {
            if frame.names.contains(name) {
                return Some(crossed && !frame.module);
            }
            if frame.boundary {
                crossed = true;
            }
        }
        None
    }

    fn with_frame(&mut self, boundary: bool, fn_name: Option<String>, f: impl FnOnce(&mut Self)) {
        self.frames.push(Frame {
            names: HashSet::new(),
            boundary,
            module: false,
        });
        let pushed_name = fn_name.is_some();
        if let Some(n) = fn_name {
            self.fn_names.push(n);
        }
        f(self);
        if pushed_name {
            self.fn_names.pop();
        }
        self.frames.pop();
    }

    fn function(&mut self, def: &FunctionDef) {
        self.with_frame(true, Some(def.name.clone()), |c| {
            for p in &def.params {
                c.declare(&p.name);
                if let Some(d) = &p.default {
                    c.expr(d);
                }
            }
            c.block(&def.body);
        });
    }

    fn block(&mut self, block: &Block) {
        for s in &block.statements {
            self.node(s);
        }
    }

    fn nodes(&mut self, nodes: &[Node]) {
        for s in nodes {
            self.node(s);
        }
    }

    fn arms(&mut self, arms: &[MatchArm]) {
        for arm in arms {
            self.declare_pattern(&arm.pattern);
            if let Some(g) = &arm.guard {
                self.expr(g);
            }
            self.block(&arm.body);
        }
    }

    fn node(&mut self, node: &Node) {
        match node {
            Node::Function(def) => {
                self.declare(&def.name);
                self.function(def);
            }
            Node::Class(c) => c.methods.iter().for_each(|m| self.function(m)),
            Node::Struct(s) => s.methods.iter().for_each(|m| self.function(m)),
            Node::Impl(i) => i.methods.iter().for_each(|m| self.function(m)),
            Node::Trait(t) => t.methods.iter().for_each(|m| self.function(m)),
            Node::Mixin(m) => m.methods.iter().for_each(|f| self.function(f)),
            Node::Actor(a) => a.methods.iter().for_each(|m| self.function(m)),
            Node::Let(l) => {
                if let Some(v) = &l.value {
                    // `val f = \x: ...` names the closure `f`, matching the
                    // pure-Simple twin (which desugars `fn f(...)` the same way).
                    if let (Pattern::Identifier(n) | Pattern::MutIdentifier(n), Expr::Lambda { move_mode, .. }) =
                        (&l.pattern, v)
                    {
                        if *move_mode != MoveMode::ColonBlock {
                            self.pending_fn = Some(n.clone());
                        }
                    }
                    self.expr(v);
                    self.pending_fn = None;
                }
                self.declare_pattern(&l.pattern);
            }
            Node::Assignment(a) => {
                self.expr(&a.value);
                if let Expr::Identifier(name) = &a.target {
                    match self.is_captured_local(name) {
                        Some(true) => {
                            let in_fn = self.fn_names.last().cloned().unwrap_or_else(|| "<closure>".to_string());
                            self.found.push(CaptureWrite {
                                name: name.clone(),
                                in_fn,
                                line: a.span.line,
                            });
                        }
                        Some(false) => {}
                        // First assignment declares a local (implicit declaration).
                        None => self.declare(name),
                    }
                } else {
                    self.expr(&a.target);
                }
            }
            Node::Return(r) => {
                if let Some(v) = &r.value {
                    self.expr(v);
                }
            }
            Node::If(i) => {
                if let Some(p) = &i.let_pattern {
                    self.declare_pattern(p);
                }
                self.expr(&i.condition);
                self.block(&i.then_block);
                for (p, cond, b) in &i.elif_branches {
                    if let Some(p) = p {
                        self.declare_pattern(p);
                    }
                    self.expr(cond);
                    self.block(b);
                }
                if let Some(b) = &i.else_block {
                    self.block(b);
                }
            }
            Node::Match(m) => {
                self.expr(&m.subject);
                self.arms(&m.arms);
            }
            Node::For(f) => {
                self.expr(&f.iterable);
                self.declare_pattern(&f.pattern);
                self.block(&f.body);
            }
            Node::While(w) => {
                if let Some(p) = &w.let_pattern {
                    self.declare_pattern(p);
                }
                self.expr(&w.condition);
                self.block(&w.body);
            }
            Node::Loop(l) => self.block(&l.body),
            Node::Expression(e) => self.expr(e),
            _ => {}
        }
    }

    fn args(&mut self, args: &[Argument]) {
        for a in args {
            self.expr(&a.value);
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            // A colon-block is a scope, not a capture boundary (see module doc).
            Expr::Lambda {
                body,
                move_mode: MoveMode::ColonBlock,
                ..
            } => self.with_frame(false, None, |c| c.expr(body)),
            Expr::Lambda { params, body, .. } => {
                let name = self.pending_fn.take().unwrap_or_else(|| "<closure>".to_string());
                self.with_frame(true, Some(name), |c| {
                    for p in params {
                        c.declare(&p.name);
                    }
                    c.expr(body);
                })
            }
            Expr::DoBlock(nodes) => self.with_frame(false, None, |c| c.nodes(nodes)),
            Expr::UnsafeBlock(nodes, _) => self.nodes(nodes),
            Expr::Call { callee, args } => {
                self.expr(callee);
                self.args(args);
            }
            Expr::MethodCall { receiver, args, .. } => {
                self.expr(receiver);
                self.args(args);
            }
            Expr::If {
                let_pattern,
                condition,
                then_branch,
                else_branch,
            } => {
                if let Some(p) = let_pattern {
                    self.declare_pattern(p);
                }
                self.expr(condition);
                self.expr(then_branch);
                if let Some(e) = else_branch {
                    self.expr(e);
                }
            }
            Expr::Match { subject, arms } => {
                self.expr(subject);
                self.arms(arms);
            }
            Expr::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            Expr::Unary { operand, .. } => self.expr(operand),
            Expr::Array(items) | Expr::Tuple(items) => items.iter().for_each(|e| self.expr(e)),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::find_captured_local_writes;
    use crate::Parser;

    fn writes(src: &str) -> Vec<(String, String)> {
        let module = Parser::new(src).parse().expect("parse");
        find_captured_local_writes(&module)
            .into_iter()
            .map(|w| (w.name, w.in_fn))
            .collect()
    }

    #[test]
    fn nested_fn_write_to_enclosing_local_is_reported() {
        let src = "fn outer() -> i64:\n    var n = 0\n    fn bump():\n        n = n + 1\n    bump()\n    n\n";
        assert_eq!(writes(src), vec![("n".to_string(), "bump".to_string())]);
    }

    #[test]
    fn nested_fn_write_to_enclosing_param_is_reported() {
        let src = "fn outer(total: i64) -> i64:\n    fn reset():\n        total = 0\n    reset()\n    total\n";
        assert_eq!(writes(src), vec![("total".to_string(), "reset".to_string())]);
    }

    #[test]
    fn block_lambda_write_to_enclosing_local_is_reported() {
        let src = "fn outer() -> i64:\n    var n = 0\n    val f = \\x:\n        n = n + x\n    f(2)\n    n\n";
        assert_eq!(writes(src), vec![("n".to_string(), "f".to_string())]);
    }

    #[test]
    fn it_block_local_written_by_nested_fn_is_reported() {
        let src = "describe \"g\":\n    it \"x\":\n        var total = 0\n        fn bump(k: i64):\n            total = total + k\n        bump(5)\n";
        assert_eq!(writes(src), vec![("total".to_string(), "bump".to_string())]);
    }

    #[test]
    fn module_global_write_from_nested_fn_is_allowed() {
        let src = "var g = 0\nfn outer():\n    fn setg():\n        g = 5\n    setg()\n";
        assert!(writes(src).is_empty());
    }

    #[test]
    fn nested_fn_own_locals_and_params_are_allowed() {
        let src = "fn outer() -> i64:\n    var n = 1\n    fn inner(k: i64) -> i64:\n        var m = k\n        m = m + 1\n        k = k * 2\n        fresh = 3\n        fresh = fresh + 1\n        m + k + fresh\n    n = inner(n)\n    n\n";
        assert!(writes(src).is_empty());
    }

    #[test]
    fn same_function_loops_and_blocks_are_allowed() {
        let src = "fn outer() -> i64:\n    var n = 0\n    for x in [1, 2]:\n        n = n + x\n    if n > 0:\n        n = n * 2\n    n\n";
        assert!(writes(src).is_empty());
    }

    #[test]
    fn colon_block_write_to_enclosing_local_is_not_a_capture() {
        // Colon-blocks are out of the ruling's scope (nested fn / lambda).
        let src = "describe \"g\":\n    var count = 0\n    after_each:\n        count = count + 1\n    it \"x\":\n        count = count + 1\n";
        assert!(writes(src).is_empty());
    }

    #[test]
    fn anonymous_closure_argument_is_reported_as_a_closure() {
        let src = "fn outer() -> i64:\n    var total = 0\n    [1, 2].each(\\x:\n        total = total + x\n    )\n    total\n";
        let module = Parser::new(src).parse().expect("parse");
        let found = find_captured_local_writes(&module);
        assert_eq!(found.len(), 1);
        assert_eq!(
            found[0].message(),
            "cannot assign to captured variable `total` inside a closure (line 4): closures capture enclosing locals by value and are read-only; return the new value or use a module-level `var`"
        );
    }

    #[test]
    fn paramless_backslash_lambda_is_still_a_boundary() {
        let src = "fn outer() -> i64:\n    var n = 0\n    val f = \\:\n        n = n + 9\n    f()\n    n\n";
        assert_eq!(writes(src), vec![("n".to_string(), "f".to_string())]);
    }

    #[test]
    fn module_global_write_from_colon_block_is_allowed() {
        let src = "var hits = 0\ndescribe \"g\":\n    it \"x\":\n        hits = hits + 1\n";
        assert!(writes(src).is_empty());
    }

    #[test]
    fn colon_block_own_locals_are_allowed() {
        let src = "describe \"g\":\n    it \"x\":\n        var n = 0\n        n = n + 1\n        for x in [1]:\n            n = n + x\n";
        assert!(writes(src).is_empty());
    }
}
