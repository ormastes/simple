//! Static enumeration of decision/condition coverage sites.
//!
//! Probes only record sites that execute, so without this a function that is
//! never called, an `elif` that is never reached, or an if-expression simply
//! did not exist in the report — the denominator rewarded *not* running code.
//! When coverage is enabled, every module's items are walked once at load and
//! each site is registered with zero counts under exactly the key the runtime
//! probe uses (see the site table in `coverage_helpers.rs`).
//!
//! The walk must mirror the interpreter: file = owner of the function (the
//! same resolution `execute_function_body` feeds `current_coverage_file`),
//! expression-site anchor = that function's span.

use simple_parser::ast::{Block, DeferBody, Expr, FStringPart, FunctionDef, MatchArm, Node, SkipBody};

use super::coverage_helpers::{
    coverage_file_for_owner, decision_condition_count, expr_site_sub, is_and_or, site_decision_id, sub_elif, SUB_GUARD,
    SUB_STMT, TAG_AND_OR, TAG_IF_EXPR,
};
use super::FLATTEN_MODULE_OWNER_ATTR_PREFIX;

/// Register every decision/condition site in `items`. `default_owner` is the
/// module owner key of these items (`"<entry>"` for the entry script); a
/// function carrying a flatten owner attribute uses that owner instead.
pub(crate) fn register_module_sites(items: &[Node], default_owner: Option<&str>) {
    let mut walker = SiteWalker {
        default_owner: default_owner.map(str::to_string),
        file: coverage_file_for_owner(default_owner),
        anchor: (0, 0),
        stmt_line: 0,
    };
    for item in items {
        walker.node(item);
    }
}

struct SiteWalker {
    default_owner: Option<String>,
    file: String,
    anchor: (u32, u32),
    stmt_line: u32,
}

fn flatten_owner(f: &FunctionDef) -> Option<String> {
    f.attributes.iter().find_map(|a| {
        a.name.strip_prefix(FLATTEN_MODULE_OWNER_ATTR_PREFIX).map(|raw| {
            crate::interpreter::normalize_path_key(std::path::Path::new(raw))
                .to_string_lossy()
                .to_string()
        })
    })
}

impl SiteWalker {
    fn register(&self, line: u32, column: u32, sub: u64, display_line: u32, conditions: u32) {
        let id = site_decision_id(&self.file, line, column, sub);
        simple_runtime::coverage::coverage_register_site(id, &self.file, line, column, display_line, conditions);
    }

    fn function(&mut self, f: &FunctionDef) {
        let owner = flatten_owner(f).or_else(|| self.default_owner.clone());
        let saved_file = std::mem::replace(&mut self.file, coverage_file_for_owner(owner.as_deref()));
        let saved_anchor = self.anchor;
        // Mirrors execute_function_body: the anchor follows the function only
        // when it has an owner (lambdas inherit their caller's).
        if owner.is_some() {
            self.anchor = (f.span.line as u32, f.span.column as u32);
        }
        for p in &f.params {
            if let Some(d) = &p.default {
                self.expr(d);
            }
        }
        self.block(&f.body);
        self.anchor = saved_anchor;
        self.file = saved_file;
    }

    fn block(&mut self, b: &Block) {
        for n in &b.statements {
            self.node(n);
        }
    }

    fn methods(&mut self, methods: &[FunctionDef]) {
        for m in methods {
            self.function(m);
        }
    }

    /// A decision condition: the `and`/`or` tree itself is this decision's
    /// conditions, so only its leaves are walked for nested sites.
    fn cond(&mut self, e: &Expr) {
        match e {
            Expr::Binary { left, right, .. } if is_and_or(e) => {
                self.cond(left);
                self.cond(right);
            }
            _ => self.expr(e),
        }
    }

    fn guard_arms(&mut self, arms: &[MatchArm]) {
        for arm in arms {
            if let Some(g) = &arm.guard {
                let (l, c) = (arm.span.line as u32, arm.span.column as u32);
                self.register(l, c, SUB_GUARD, l, decision_condition_count(g));
                self.cond(g);
            }
            self.block(&arm.body);
        }
    }

    fn node(&mut self, node: &Node) {
        match node {
            Node::Function(f) => self.function(f),
            Node::Class(c) => self.methods(&c.methods),
            Node::Struct(s) => self.methods(&s.methods),
            Node::Enum(e) => self.methods(&e.methods),
            Node::Impl(i) => self.methods(&i.methods),
            Node::Trait(t) => self.methods(&t.methods),
            Node::Mixin(m) => self.methods(&m.methods),
            Node::Actor(a) => self.methods(&a.methods),
            Node::Expression(e) => self.expr(e),
            Node::Let(s) => {
                self.stmt_line = s.span.line as u32;
                if let Some(v) = &s.value {
                    self.expr(v);
                }
            }
            Node::Const(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.value);
            }
            Node::Static(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.value);
            }
            Node::Assignment(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.target);
                self.expr(&s.value);
            }
            Node::Return(s) => {
                self.stmt_line = s.span.line as u32;
                if let Some(v) = &s.value {
                    self.expr(v);
                }
            }
            Node::Break(s) => {
                self.stmt_line = s.span.line as u32;
                if let Some(v) = &s.value {
                    self.expr(v);
                }
            }
            Node::Assert(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.condition);
            }
            Node::If(s) => {
                let (l, c) = (s.span.line as u32, s.span.column as u32);
                self.stmt_line = l;
                if s.let_pattern.is_some() {
                    self.register(l, c, SUB_STMT, l, 0);
                    self.expr(&s.condition);
                } else {
                    self.register(l, c, SUB_STMT, l, decision_condition_count(&s.condition));
                    self.cond(&s.condition);
                }
                self.block(&s.then_block);
                for (idx, (pattern, cond, blk)) in s.elif_branches.iter().enumerate() {
                    // An elif has no span; its block starts on the line after the
                    // `elif` (display only — the key is the parent `if` + index).
                    let display = (blk.span.line as u32).saturating_sub(1).max(l);
                    self.stmt_line = display;
                    if pattern.is_some() {
                        self.register(l, c, sub_elif(idx), display, 0);
                        self.expr(cond);
                    } else {
                        self.register(l, c, sub_elif(idx), display, decision_condition_count(cond));
                        self.cond(cond);
                    }
                    self.block(blk);
                }
                if let Some(b) = &s.else_block {
                    self.block(b);
                }
            }
            Node::While(s) => {
                let (l, c) = (s.span.line as u32, s.span.column as u32);
                self.stmt_line = l;
                if s.let_pattern.is_some() {
                    self.register(l, c, SUB_STMT, l, 0);
                    self.expr(&s.condition);
                } else {
                    self.register(l, c, SUB_STMT, l, decision_condition_count(&s.condition));
                    self.cond(&s.condition);
                }
                self.block(&s.body);
            }
            Node::For(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.iterable);
                self.block(&s.body);
            }
            Node::Loop(s) => self.block(&s.body),
            Node::With(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.resource);
                self.block(&s.body);
            }
            Node::Context(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.context);
                self.block(&s.body);
            }
            Node::Defer(s) => match &s.body {
                DeferBody::Expr(e) => self.expr(e),
                DeferBody::Block(b) => self.block(b),
            },
            Node::ErrDefer(s) => match &s.body {
                DeferBody::Expr(e) => self.expr(e),
                DeferBody::Block(b) => self.block(b),
            },
            Node::Match(s) => {
                self.stmt_line = s.span.line as u32;
                self.expr(&s.subject);
                self.guard_arms(&s.arms);
            }
            Node::Skip(s) => {
                if let SkipBody::Block(b) = &s.body {
                    self.block(b);
                }
            }
            _ => {}
        }
    }

    fn exprs<'e>(&mut self, items: impl IntoIterator<Item = &'e Expr>) {
        for e in items {
            self.expr(e);
        }
    }

    fn expr(&mut self, e: &Expr) {
        match e {
            Expr::Binary { left, right, .. } => {
                if is_and_or(e) {
                    let (l, c) = self.anchor;
                    self.register(
                        l,
                        c,
                        expr_site_sub(TAG_AND_OR, e),
                        self.stmt_line,
                        decision_condition_count(e),
                    );
                    self.cond(e);
                } else {
                    self.expr(left);
                    self.expr(right);
                }
            }
            Expr::If {
                let_pattern,
                condition,
                then_branch,
                else_branch,
            } => {
                let (l, c) = self.anchor;
                let sub = expr_site_sub(TAG_IF_EXPR, condition);
                if let_pattern.is_some() {
                    self.register(l, c, sub, self.stmt_line, 0);
                    self.expr(condition);
                } else {
                    self.register(l, c, sub, self.stmt_line, decision_condition_count(condition));
                    self.cond(condition);
                }
                self.expr(then_branch);
                if let Some(b) = else_branch {
                    self.expr(b);
                }
            }
            Expr::Match { subject, arms } => {
                self.expr(subject);
                self.guard_arms(arms);
            }
            Expr::Lambda { body, .. } => self.expr(body),
            Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes, _) => {
                for n in nodes {
                    self.node(n);
                }
            }
            Expr::Unary { operand, .. } => self.expr(operand),
            Expr::Call { callee, args } => {
                self.expr(callee);
                self.exprs(args.iter().map(|a| &a.value));
            }
            Expr::KernelLaunch {
                kernel,
                grid,
                block,
                args,
            } => {
                self.exprs([kernel.as_ref(), grid.as_ref(), block.as_ref()]);
                self.exprs(args.iter().map(|a| &a.value));
            }
            Expr::MethodCall { receiver, args, .. } | Expr::OptionalMethodCall { receiver, args, .. } => {
                self.expr(receiver);
                self.exprs(args.iter().map(|a| &a.value));
            }
            Expr::FunctionalUpdate { target, args, .. } => {
                self.expr(target);
                self.exprs(args.iter().map(|a| &a.value));
            }
            Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => self.expr(receiver),
            Expr::Index { receiver, index } => self.exprs([receiver.as_ref(), index.as_ref()]),
            Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => self.exprs(items.iter()),
            Expr::LabeledTuple(fields) => self.exprs(fields.iter().map(|f| &f.value)),
            Expr::ArrayRepeat { value, count } => self.exprs([value.as_ref(), count.as_ref()]),
            Expr::Dict(pairs) => {
                for (k, v) in pairs {
                    self.expr(k);
                    self.expr(v);
                }
            }
            Expr::ListComprehension {
                expr,
                iterable,
                condition,
                ..
            } => {
                self.exprs([expr.as_ref(), iterable.as_ref()]);
                if let Some(c) = condition {
                    self.expr(c);
                }
            }
            Expr::DictComprehension {
                key,
                value,
                iterable,
                condition,
                ..
            } => {
                self.exprs([key.as_ref(), value.as_ref(), iterable.as_ref()]);
                if let Some(c) = condition {
                    self.expr(c);
                }
            }
            Expr::Slice {
                receiver,
                start,
                end,
                step,
            } => {
                self.expr(receiver);
                for x in [start, end, step].into_iter().flatten() {
                    self.expr(x);
                }
            }
            Expr::Range { start, end, .. } => {
                for x in [start, end].into_iter().flatten() {
                    self.expr(x);
                }
            }
            Expr::StructInit { fields, spread, .. } => {
                self.exprs(fields.iter().map(|(_, v)| v));
                if let Some(s) = spread {
                    self.expr(s);
                }
            }
            Expr::Go { args, body, .. } => {
                self.exprs(args.iter());
                self.expr(body);
            }
            Expr::Yield(Some(x)) => self.expr(x),
            Expr::Spread(x)
            | Expr::DictSpread(x)
            | Expr::StructSpread(x)
            | Expr::Spawn(x)
            | Expr::Await(x)
            | Expr::Try(x)
            | Expr::ForceUnwrap(x)
            | Expr::ExistsCheck(x)
            | Expr::ContractOld(x) => self.expr(x),
            Expr::New { expr, .. }
            | Expr::Cast { expr, .. }
            | Expr::CastOrReturn { expr, .. }
            | Expr::OptionalChain { expr, .. } => self.expr(expr),
            Expr::UnwrapOr { expr, default }
            | Expr::UnwrapOrReturn { expr, default }
            | Expr::CastOr { expr, default, .. }
            | Expr::Coalesce { expr, default } => self.exprs([expr.as_ref(), default.as_ref()]),
            Expr::UnwrapElse { expr, fallback_fn } | Expr::CastElse { expr, fallback_fn, .. } => {
                self.exprs([expr.as_ref(), fallback_fn.as_ref()])
            }
            Expr::Forall { range, predicate, .. } | Expr::Exists { range, predicate, .. } => {
                self.exprs([range.as_ref(), predicate.as_ref()])
            }
            Expr::FString { parts, .. } => {
                for p in parts {
                    match p {
                        FStringPart::Expr(x) | FStringPart::ExprWithFormat(x, _) => self.expr(x),
                        FStringPart::Literal(_) => {}
                    }
                }
            }
            Expr::I18nTemplate { args, .. } => self.exprs(args.iter().map(|(_, v)| v)),
            _ => {}
        }
    }
}
