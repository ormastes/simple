//! Compilability analysis for hybrid execution.
//!
//! This module determines which parts of a program can be compiled to native
//! code versus which parts require interpreter fallback. It walks the AST
//! and identifies features that the codegen cannot yet handle.

use std::collections::{HashMap, HashSet};

use simple_parser::ast::{BinOp, Block, Expr, FunctionDef, Node, UnaryOp};

use crate::value::{ACTOR_BUILTINS, BLOCKING_BUILTINS, GENERATOR_BUILTINS};

/// Reason why a construct requires interpreter fallback
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FallbackReason {
    /// Dynamic type operations (reflection, type checking at runtime)
    DynamicTypes,
    /// Collection operations requiring runtime support
    CollectionOps,
    /// Array/tuple/dict literals
    CollectionLiteral,
    /// String operations (beyond simple constants)
    StringOps,
    /// GC allocation in nogc context
    GcInNogcContext,
    /// Blocking operations in async context
    BlockingInAsync,
    /// Actor/concurrency primitives
    ActorOps,
    /// User-defined macros
    UserMacros,
    /// Pattern matching
    PatternMatch,
    /// Lambda/closure expressions
    Closure,
    /// Class/struct instantiation
    ObjectConstruction,
    /// Method calls on objects
    MethodCall,
    /// Field access on dynamic objects
    FieldAccess,
    /// Generator/yield expressions
    Generator,
    /// Async/await expressions
    AsyncAwait,
    /// Decorator application
    Decorators,
    /// Try operator (?)
    TryOperator,
    /// With statements
    WithStatement,
    /// Context blocks
    ContextBlock,
    /// Extern functions not in known safe list
    UnknownExtern(String),
    /// Feature not yet implemented in codegen
    NotYetImplemented(String),
}

/// Compilability status for a function or expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilabilityStatus {
    /// Can be fully compiled to native code
    Compilable,
    /// Requires interpreter fallback
    RequiresInterpreter(Vec<FallbackReason>),
}

impl CompilabilityStatus {
    /// Check if this is compilable
    pub fn is_compilable(&self) -> bool {
        matches!(self, CompilabilityStatus::Compilable)
    }

    /// Get the fallback reasons (empty if compilable)
    pub fn reasons(&self) -> &[FallbackReason] {
        match self {
            CompilabilityStatus::Compilable => &[],
            CompilabilityStatus::RequiresInterpreter(reasons) => reasons,
        }
    }

    /// Merge with another status (union of reasons)
    pub fn merge(&mut self, other: CompilabilityStatus) {
        match (self, other) {
            (CompilabilityStatus::Compilable, CompilabilityStatus::Compilable) => {}
            (status @ CompilabilityStatus::Compilable, CompilabilityStatus::RequiresInterpreter(reasons)) => {
                *status = CompilabilityStatus::RequiresInterpreter(reasons);
            }
            (CompilabilityStatus::RequiresInterpreter(existing), CompilabilityStatus::RequiresInterpreter(new)) => {
                for reason in new {
                    if !existing.contains(&reason) {
                        existing.push(reason);
                    }
                }
            }
            (CompilabilityStatus::RequiresInterpreter(_), CompilabilityStatus::Compilable) => {}
        }
    }
}

/// Analyzes a module to determine compilability of each function
pub fn analyze_module(items: &[Node]) -> HashMap<String, CompilabilityStatus> {
    let mut results = HashMap::new();

    for item in items {
        if let Node::Function(f) = item {
            let status = analyze_function(f);
            results.insert(f.name.clone(), status);
        }
    }

    results
}

/// Analyze a single function for compilability
pub fn analyze_function(f: &FunctionDef) -> CompilabilityStatus {
    if is_known_compilable_green_thread_helper(&f.name) {
        return CompilabilityStatus::Compilable;
    }

    let mut reasons = Vec::new();

    // Check for decorators
    if !f.decorators.is_empty() {
        reasons.push(FallbackReason::Decorators);
    }

    // Check for effects - functions with effects may need interpreter fallback
    if !f.effects.is_empty() {
        reasons.push(FallbackReason::AsyncAwait);
    }

    // Analyze the function body
    analyze_block(&f.body, &mut reasons);

    if reasons.is_empty() {
        CompilabilityStatus::Compilable
    } else {
        CompilabilityStatus::RequiresInterpreter(reasons)
    }
}

/// Analyze a block of statements (Block contains Vec<Node>)
fn analyze_block(block: &Block, reasons: &mut Vec<FallbackReason>) {
    for node in &block.statements {
        analyze_node(node, reasons);
    }
}

/// Analyze a single AST node (statement or definition)
fn analyze_node(node: &Node, reasons: &mut Vec<FallbackReason>) {
    match node {
        Node::Expression(expr) => {
            analyze_expr(expr, reasons);
        }
        Node::Let(let_stmt) => {
            if let Some(expr) = &let_stmt.value {
                analyze_expr(expr, reasons);
            }
        }
        Node::Const(const_stmt) => {
            analyze_expr(&const_stmt.value, reasons);
        }
        Node::Assignment(assign) => {
            analyze_expr(&assign.target, reasons);
            analyze_expr(&assign.value, reasons);
        }
        Node::Return(ret) => {
            if let Some(expr) = &ret.value {
                analyze_expr(expr, reasons);
            }
        }
        Node::If(if_stmt) => {
            analyze_expr(&if_stmt.condition, reasons);
            analyze_block(&if_stmt.then_block, reasons);
            for (_pattern, cond, block) in &if_stmt.elif_branches {
                analyze_expr(cond, reasons);
                analyze_block(block, reasons);
            }
            if let Some(else_block) = &if_stmt.else_block {
                analyze_block(else_block, reasons);
            }
        }
        Node::While(while_stmt) => {
            analyze_expr(&while_stmt.condition, reasons);
            analyze_block(&while_stmt.body, reasons);
        }
        Node::For(for_stmt) => {
            analyze_expr(&for_stmt.iterable, reasons);
            analyze_block(&for_stmt.body, reasons);
            // Scalar range loops lower to native loop MIR. Other iterable
            // loops still require collection iteration runtime support.
            if !matches!(for_stmt.iterable, Expr::Range { .. }) {
                add_reason(reasons, FallbackReason::CollectionOps);
            }
        }
        Node::Loop(loop_stmt) => {
            analyze_block(&loop_stmt.body, reasons);
        }
        Node::Break(_) | Node::Continue(_) => {}
        Node::Match(match_stmt) => {
            analyze_expr(&match_stmt.subject, reasons);
            add_reason(reasons, FallbackReason::PatternMatch);
        }
        Node::With(with_stmt) => {
            analyze_expr(&with_stmt.resource, reasons);
            analyze_block(&with_stmt.body, reasons);
            add_reason(reasons, FallbackReason::WithStatement);
        }
        Node::Context(ctx_stmt) => {
            analyze_expr(&ctx_stmt.context, reasons);
            analyze_block(&ctx_stmt.body, reasons);
            add_reason(reasons, FallbackReason::ContextBlock);
        }
        Node::Function(_) => {
            // Nested function definitions
            add_reason(reasons, FallbackReason::Closure);
        }
        // Definitions in blocks are not typical, skip for now
        _ => {}
    }
}

/// Analyze an expression
fn analyze_expr(expr: &Expr, reasons: &mut Vec<FallbackReason>) {
    match expr {
        // Compilable literals
        Expr::Integer(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Nil => {}

        // Typed literals
        Expr::TypedInteger(_, _) | Expr::TypedFloat(_, _) | Expr::TypedString(_, _) => {}

        // String literals are compilable, but string operations may not be
        Expr::String(_) => {}

        // Symbols need runtime support
        Expr::Symbol(_) => {
            add_reason(reasons, FallbackReason::NotYetImplemented("symbol".into()));
        }

        // Variables are compilable
        Expr::Identifier(_) => {}

        // Binary operations - mostly compilable except membership test
        Expr::Binary { op, left, right } => {
            analyze_expr(left, reasons);
            analyze_expr(right, reasons);
            if op == &BinOp::In {
                add_reason(reasons, FallbackReason::CollectionOps);
            }
        }

        // Unary operations - mostly compilable except ref operations
        Expr::Unary { op, operand } => {
            analyze_expr(operand, reasons);
            match op {
                UnaryOp::Ref | UnaryOp::RefMut | UnaryOp::Deref => {
                    add_reason(reasons, FallbackReason::NotYetImplemented("ref".into()));
                }
                _ => {}
            }
        }

        // Function calls - may be compilable depending on the callee
        Expr::Call { callee, args, .. } => {
            analyze_expr(callee, reasons);
            let compiled_closure_arg = matches!(
                callee.as_ref(),
                Expr::Identifier(name)
                    if matches!(
                        name.as_str(),
                        "multicore_green_spawn" | "task_spawn" | "thread_spawn"
                    )
            );
            for arg in args {
                if compiled_closure_arg {
                    analyze_expr_as_compiled_closure_arg(&arg.value, reasons);
                } else {
                    analyze_expr(&arg.value, reasons);
                }
            }
            // Check if it's a known compilable builtin
            if let Expr::Identifier(name) = callee.as_ref() {
                if is_blocking_builtin(name) {
                    add_reason(reasons, FallbackReason::AsyncAwait);
                }
                // Actor operations: spawn, send, recv are compilable
                // Only join and reply need interpreter fallback
                if is_non_compilable_actor_builtin(name) {
                    add_reason(reasons, FallbackReason::ActorOps);
                }
                if is_generator_builtin(name) {
                    add_reason(reasons, FallbackReason::Generator);
                }
            }
        }

        // Method calls now lower through the native MethodCallStatic /
        // BuiltinMethod / extern-method paths. Keep walking receiver/args for
        // genuinely unsupported nested constructs, but do not force blanket
        // hybrid fallback just because a typed method is invoked.
        Expr::MethodCall { receiver, args, .. } => {
            analyze_expr(receiver, reasons);
            for arg in args {
                analyze_expr(&arg.value, reasons);
            }
        }

        // Typed field access lowers directly to MIR FieldGet. Keep walking the
        // receiver for nested unsupported constructs, but do not force
        // interpreter fallback just because a field is read.
        Expr::FieldAccess { receiver, .. } => {
            analyze_expr(receiver, reasons);
        }

        // Indexed access now lowers through MIR `rt_array_get` / `rt_index_get`
        // and can stay on the native path. Keep walking nested operands for any
        // genuinely unsupported constructs, but do not force fallback just
        // because an element is indexed out of a collection.
        Expr::Index { receiver, index } => {
            analyze_expr(receiver, reasons);
            analyze_expr(index, reasons);
        }

        // Tuple index access: tuple.0, tuple.1
        Expr::TupleIndex { receiver, .. } => {
            analyze_expr(receiver, reasons);
            // Tuple index with literal index is compilable if receiver is
        }

        // Slice needs collection runtime
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            analyze_expr(receiver, reasons);
            if let Some(s) = start {
                analyze_expr(s, reasons);
            }
            if let Some(e) = end {
                analyze_expr(e, reasons);
            }
            if let Some(st) = step {
                analyze_expr(st, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionOps);
        }

        // Array literals lower through MIR ArrayLit and the native runtime
        // already supports heap-allocated arrays. Keep walking nested elements
        // for genuinely unsupported constructs, but do not force hybrid
        // fallback just because an array literal appears.
        Expr::Array(items) => {
            for item in items {
                analyze_expr(item, reasons);
            }
        }

        // Tuple / Vec / Dict literals still keep their broader fallback marker
        // until they have the same end-to-end native contract as plain arrays.
        Expr::Tuple(items) => {
            for item in items {
                analyze_expr(item, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionLiteral);
        }

        Expr::VecLiteral(items) => {
            for item in items {
                analyze_expr(item, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionLiteral);
        }

        Expr::Dict(entries) => {
            for (key, value) in entries {
                analyze_expr(key, reasons);
                analyze_expr(value, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionLiteral);
        }

        // Range needs collection runtime
        Expr::Range { start, end, .. } => {
            if let Some(s) = start {
                analyze_expr(s, reasons);
            }
            if let Some(e) = end {
                analyze_expr(e, reasons);
            }
        }

        // Closures lower through MIR ClosureCreate and current native codegen
        // handles direct closure values. Capture codegen may still have narrower
        // runtime bugs, but blanket hybrid fallback here prevents valid native
        // code from being emitted at all.
        Expr::Lambda { body, .. } => {
            analyze_expr(body, reasons);
        }

        // If expressions are compilable
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            analyze_expr(condition, reasons);
            analyze_expr(then_branch, reasons);
            if let Some(else_e) = else_branch {
                analyze_expr(else_e, reasons);
            }
        }

        // Match expressions
        Expr::Match { subject, .. } => {
            analyze_expr(subject, reasons);
            add_reason(reasons, FallbackReason::PatternMatch);
        }

        // Struct/class initialization lowers to MIR StructInit and is part of
        // the current native surface.
        Expr::StructInit { fields, spread, .. } => {
            for (_, value) in fields {
                analyze_expr(value, reasons);
            }
            if let Some(spread_expr) = spread {
                analyze_expr(spread_expr, reasons);
            }
        }

        // New/pointer operations
        Expr::New { expr, .. } => {
            analyze_expr(expr, reasons);
            add_reason(reasons, FallbackReason::NotYetImplemented("new".into()));
        }

        // Spawn expression
        Expr::Spawn(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::ActorOps);
        }

        // Await expressions
        Expr::Await(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::AsyncAwait);
        }

        // Yield expressions
        Expr::Yield(value) => {
            if let Some(v) = value {
                analyze_expr(v, reasons);
            }
            add_reason(reasons, FallbackReason::Generator);
        }

        // Try operator
        Expr::Try(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Force unwrap operator
        Expr::ForceUnwrap(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Existence check operator
        Expr::ExistsCheck(inner) => {
            analyze_expr(inner, reasons);
            // ExistsCheck requires runtime type inspection
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Macro invocations
        Expr::MacroInvocation { .. } => {
            add_reason(reasons, FallbackReason::UserMacros);
        }

        // F-strings need string interpolation
        Expr::FString { parts, .. } => {
            let mut has_dynamic_part = false;
            for part in parts {
                match part {
                    simple_parser::ast::FStringPart::Expr(e)
                    | simple_parser::ast::FStringPart::ExprWithFormat(e, _) => {
                        has_dynamic_part = true;
                        analyze_expr(e, reasons);
                    }
                    _ => {}
                }
            }
            if has_dynamic_part {
                add_reason(reasons, FallbackReason::StringOps);
            }
        }

        // i18n strings - need runtime locale lookup
        Expr::I18nString { .. } => {
            add_reason(reasons, FallbackReason::NotYetImplemented("i18n string".into()));
        }

        Expr::I18nTemplate { parts, args, .. } => {
            for part in parts {
                match part {
                    simple_parser::ast::FStringPart::Expr(e)
                    | simple_parser::ast::FStringPart::ExprWithFormat(e, _) => {
                        analyze_expr(e, reasons);
                    }
                    _ => {}
                }
            }
            for (_, value) in args {
                analyze_expr(value, reasons);
            }
            add_reason(reasons, FallbackReason::NotYetImplemented("i18n template".into()));
        }

        Expr::I18nRef(_) => {
            add_reason(reasons, FallbackReason::NotYetImplemented("i18n reference".into()));
        }

        // Comprehensions need collection and iterator runtime
        Expr::ListComprehension {
            expr,
            iterable,
            condition,
            ..
        } => {
            analyze_expr(expr, reasons);
            analyze_expr(iterable, reasons);
            if let Some(cond) = condition {
                analyze_expr(cond, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionOps);
        }

        Expr::DictComprehension {
            key,
            value,
            iterable,
            condition,
            ..
        } => {
            analyze_expr(key, reasons);
            analyze_expr(value, reasons);
            analyze_expr(iterable, reasons);
            if let Some(cond) = condition {
                analyze_expr(cond, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionOps);
        }

        // Path expressions now lower through HIR/MIR and should not force
        // blanket interpreter fallback on their own.
        Expr::Path(_) => {}

        // Spread operator
        Expr::Spread(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::CollectionOps);
        }

        Expr::DictSpread(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::CollectionOps);
        }

        // Functional update
        Expr::FunctionalUpdate { target, args, .. } => {
            analyze_expr(target, reasons);
            for arg in args {
                analyze_expr(&arg.value, reasons);
            }
            add_reason(reasons, FallbackReason::MethodCall);
        }

        // Contract expressions - not yet implemented
        Expr::ContractResult => {
            add_reason(reasons, FallbackReason::NotYetImplemented("contract result".into()));
        }
        Expr::ContractOld(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::NotYetImplemented("contract old()".into()));
        }
        Expr::Forall { range, predicate, .. } => {
            analyze_expr(range, reasons);
            analyze_expr(predicate, reasons);
            add_reason(
                reasons,
                FallbackReason::NotYetImplemented("forall quantifier (verification only)".into()),
            );
        }
        Expr::Exists { range, predicate, .. } => {
            analyze_expr(range, reasons);
            analyze_expr(predicate, reasons);
            add_reason(
                reasons,
                FallbackReason::NotYetImplemented("exists quantifier (verification only)".into()),
            );
        }

        // DoBlock - a sequence of statements (used for BDD DSL colon-blocks)
        Expr::DoBlock(nodes) => {
            for node in nodes {
                analyze_node(node, reasons);
            }
        }

        // Cast expression: expr as Type
        Expr::Cast { expr: inner, .. } => {
            analyze_expr(inner, reasons);
        }

        // Simple Math: Grid and Tensor literals (#1920-#1929)
        // These require PyTorch runtime and will be lowered to torch.tensor() calls
        Expr::GridLiteral { rows, .. } => {
            for row in rows {
                for cell in row {
                    analyze_expr(cell.as_ref(), reasons);
                }
            }
            add_reason(
                reasons,
                FallbackReason::NotYetImplemented("grid literal (requires PyTorch)".into()),
            );
        }
        Expr::TensorLiteral { .. } => {
            // Tensor literals are complex and require PyTorch runtime
            add_reason(
                reasons,
                FallbackReason::NotYetImplemented("tensor literal (requires PyTorch)".into()),
            );
        }

        // Custom block expressions: m{...}, sh{...}, sql{...}, re{...}, etc.
        // These require block-specific runtime handlers
        Expr::BlockExpr { kind, .. } => {
            add_reason(reasons, FallbackReason::NotYetImplemented(format!("{} block", kind)));
        }

        // Go statement (concurrency)
        Expr::Go { args, body, .. } => {
            for arg in args {
                analyze_expr(arg, reasons);
            }
            analyze_expr(body, reasons);
            // Go expressions are now fully implemented via HIR lowering
        }

        // Array repeat: [value; count]
        Expr::ArrayRepeat { value, count } => {
            analyze_expr(value, reasons);
            analyze_expr(count, reasons);
            add_reason(reasons, FallbackReason::CollectionLiteral);
        }

        // Safe unwrap operators - require Option/Result runtime handling
        Expr::UnwrapOr { expr: inner, default } => {
            analyze_expr(inner, reasons);
            analyze_expr(default, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }
        Expr::UnwrapElse {
            expr: inner,
            fallback_fn,
        } => {
            analyze_expr(inner, reasons);
            analyze_expr(fallback_fn, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }
        Expr::UnwrapOrReturn(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Safe cast operators - require type checking at runtime
        Expr::CastOr {
            expr: inner, default, ..
        } => {
            analyze_expr(inner, reasons);
            analyze_expr(default, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }
        Expr::CastElse {
            expr: inner,
            fallback_fn,
            ..
        } => {
            analyze_expr(inner, reasons);
            analyze_expr(fallback_fn, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }
        Expr::CastOrReturn { expr: inner, .. } => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Null coalescing: expr ?? default
        Expr::Coalesce { expr: inner, default } => {
            analyze_expr(inner, reasons);
            analyze_expr(default, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Optional chaining: expr?.field or expr?.method(args)
        Expr::OptionalChain { expr: inner, .. } => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::FieldAccess);
        }
        Expr::OptionalMethodCall { receiver, args, .. } => {
            analyze_expr(receiver, reasons);
            for arg in args {
                analyze_expr(&arg.value, reasons);
            }
            add_reason(reasons, FallbackReason::MethodCall);
        }

        // Atom literals (backtick symbols)
        Expr::Atom(_) => {
            add_reason(reasons, FallbackReason::NotYetImplemented("atom literal".into()));
        }

        // Catch-all for new expression kinds
        _ => {
            add_reason(reasons, FallbackReason::NotYetImplemented("expr (unknown)".into()));
        }
    }
}

fn analyze_expr_as_compiled_closure_arg(expr: &Expr, reasons: &mut Vec<FallbackReason>) {
    if let Expr::Lambda { body, .. } = expr {
        analyze_expr(body, reasons);
    } else {
        analyze_expr(expr, reasons);
    }
}

/// Add a reason if not already present
fn add_reason(reasons: &mut Vec<FallbackReason>, reason: FallbackReason) {
    if !reasons.contains(&reason) {
        reasons.push(reason);
    }
}

/// Check if a builtin is blocking (can't be used in async)
fn is_blocking_builtin(name: &str) -> bool {
    BLOCKING_BUILTINS.contains(&name)
}

/// Check if a builtin is an actor operation
fn is_actor_builtin(name: &str) -> bool {
    ACTOR_BUILTINS.contains(&name)
}

/// Check if an actor builtin requires interpreter fallback
/// All actor operations (spawn, send, recv, join, reply) are now compilable
fn is_non_compilable_actor_builtin(_name: &str) -> bool {
    false
}

/// Check if a builtin is a generator operation
fn is_generator_builtin(name: &str) -> bool {
    GENERATOR_BUILTINS.contains(&name)
}

fn is_known_compilable_green_thread_helper(name: &str) -> bool {
    matches!(
        name,
        "green_spawn"
            | "green_spawn_value"
            | "green_ready_count"
            | "green_run_one"
            | "green_run_all"
            | "cooperative_green_spawn"
            | "cooperative_green_spawn_value"
            | "cooperative_green_ready_count"
            | "cooperative_green_run_one"
            | "cooperative_green_run_all"
    )
}

/// Get the set of currently compilable builtins
pub fn compilable_builtins() -> HashSet<&'static str> {
    let mut builtins = HashSet::new();
    // Currently compilable: basic arithmetic, comparisons, control flow
    // These are handled directly by codegen without runtime calls
    builtins.insert("print"); // Will need runtime eventually
    builtins.insert("println");
    builtins
}

/// Check if a function is likely to be side-effect free and small enough to inline
pub fn is_inlinable(_f: &FunctionDef) -> bool {
    // For now, no inlining - this could be expanded later
    false
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_and_analyze(source: &str) -> HashMap<String, CompilabilityStatus> {
        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();
        analyze_module(&module.items)
    }

    #[test]
    fn test_simple_function_compilable() {
        let results = parse_and_analyze("fn add(a: i64, b: i64) -> i64:\n    return a + b\n");
        assert!(results.get("add").unwrap().is_compilable());
    }

    #[test]
    fn test_function_with_array_not_compilable() {
        let results = parse_and_analyze("fn make_array():\n    return [1, 2, 3]\n");
        let status = results.get("make_array").unwrap();
        assert!(!status.is_compilable());
        assert!(status.reasons().contains(&FallbackReason::CollectionLiteral));
    }

    #[test]
    fn test_typed_method_call_compilable() {
        let results = parse_and_analyze("fn get_len(arr: i64):\n    return arr.len()\n");
        let status = results.get("get_len").unwrap();
        assert!(
            status.is_compilable(),
            "typed method call should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_channel_helper_method_compilable() {
        let results = parse_and_analyze(
            r#"class Channel:
    _id: i64

    fn id() -> i64:
        self._id

fn helper(id: i64) -> i64:
    val ch = Channel(_id: id)
    if ch.id() != id:
        return 81
    42
"#,
        );
        let status = results.get("helper").unwrap();
        assert!(
            status.is_compilable(),
            "channel helper method should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_helper_print_then_return_compilable() {
        let results = parse_and_analyze(
            r#"fn run_one() -> i64:
    val value = 7
    println("ok")
    value
"#,
        );
        let status = results.get("run_one").unwrap();
        assert!(
            status.is_compilable(),
            "helper print/return should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_scalar_range_loop_worker_compilable() {
        let results = parse_and_analyze(
            r#"val ITERS: i64 = 10
fn worker(seed: i64) -> i64:
    var x = seed
    for i in 0..ITERS:
        x = (x * 1103515245 + 12345) % 2147483648
    x
"#,
        );
        let status = results.get("worker").unwrap();
        assert!(
            status.is_compilable(),
            "scalar range-loop worker should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_multicore_green_spawn_wrapper_compilable() {
        let results = parse_and_analyze(
            r#"fn worker() -> i64:
    42

fn spawn_worker():
    multicore_green_spawn(\: worker())
"#,
        );
        let status = results.get("spawn_worker").unwrap();
        assert!(
            status.is_compilable(),
            "runtime-pool spawn wrapper should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_green_spawn_value_helper_compilable() {
        let results = parse_and_analyze(
            r#"class GreenScheduler:
    next_id: usize
    ready_count: usize
    done_count: usize

class GreenThreadHandle:
    task_id: usize
    value_mode: usize
    value_order: usize
    value_result: i64

var GREEN_SCHEDULER: GreenScheduler = GreenScheduler(next_id: 1, ready_count: 0, done_count: 0)

fn green_spawn_value(result: i64) -> GreenThreadHandle:
    val task_id = GREEN_SCHEDULER.next_id
    GREEN_SCHEDULER.next_id = GREEN_SCHEDULER.next_id + 1
    val value_order = GREEN_SCHEDULER.ready_count + 1
    GREEN_SCHEDULER.ready_count = GREEN_SCHEDULER.ready_count + 1
    GreenThreadHandle(task_id: task_id, value_mode: 1, value_order: value_order, value_result: result)
"#,
        );
        let status = results.get("green_spawn_value").unwrap();
        assert!(
            status.is_compilable(),
            "green_spawn_value helper should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_cooperative_green_spawn_value_wrapper_compilable() {
        let results = parse_and_analyze(
            r#"fn green_spawn_value(result: i64) -> i64:
    result

fn cooperative_green_spawn_value(result: i64) -> i64:
    green_spawn_value(result)
"#,
        );
        let status = results.get("cooperative_green_spawn_value").unwrap();
        assert!(
            status.is_compilable(),
            "cooperative wrapper should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_self_field_and_method_helpers_compilable() {
        let results = parse_and_analyze(
            r#"class Counter:
    value: i64

    fn is_ready() -> bool:
        self.value > 0

    fn read() -> i64:
        if self.is_ready():
            return self.value
        0
"#,
        );
        let is_ready = results.get("is_ready").unwrap();
        assert!(
            is_ready.is_compilable(),
            "self field helper should compile natively, got {:?}",
            is_ready.reasons()
        );
        let read = results.get("read").unwrap();
        assert!(
            read.is_compilable(),
            "self method helper should compile natively, got {:?}",
            read.reasons()
        );
    }

    #[test]
    fn test_closure_holder_factory_compilable() {
        let results = parse_and_analyze(
            r#"class Counter:
    value: i64

class Holder:
    thunk: fn() -> i64

fn make_holder(seed: i64) -> Holder:
    var counter = Counter(value: seed)
    val thunk = \:
        counter.value = counter.value + 1
        counter.value
    Holder(thunk: thunk)
"#,
        );
        let status = results.get("make_holder").unwrap();
        assert!(
            status.is_compilable(),
            "closure holder factory should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_function_value_array_helper_compilable() {
        let results = parse_and_analyze(
            r#"var FUNCS: [fn() -> i64] = []

fn worker() -> i64:
    7

fn get0() -> fn() -> i64:
    FUNCS[0]
"#,
        );
        let status = results.get("get0").unwrap();
        assert!(
            status.is_compilable(),
            "function-value array helper should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_function_value_loop_return_helper_compilable() {
        let results = parse_and_analyze(
            r#"var IDS: [i64] = []
var FUNCS: [fn() -> i64] = []

fn worker() -> i64:
    7

fn get_func(id: i64) -> fn() -> i64:
    for i in 0..IDS.len():
        if IDS[i] == id:
            return FUNCS[i]
    worker
"#,
        );
        let status = results.get("get_func").unwrap();
        assert!(
            status.is_compilable(),
            "loop-return function-value helper should compile natively, got {:?}",
            status.reasons()
        );
    }

    #[test]
    fn test_compilability_status_merge() {
        let mut status = CompilabilityStatus::Compilable;
        status.merge(CompilabilityStatus::Compilable);
        assert!(status.is_compilable());

        status.merge(CompilabilityStatus::RequiresInterpreter(vec![FallbackReason::Closure]));
        assert!(!status.is_compilable());
        assert!(status.reasons().contains(&FallbackReason::Closure));

        status.merge(CompilabilityStatus::RequiresInterpreter(vec![
            FallbackReason::MethodCall,
        ]));
        assert!(status.reasons().contains(&FallbackReason::Closure));
        assert!(status.reasons().contains(&FallbackReason::MethodCall));
    }

    #[test]
    fn test_blocking_builtins() {
        assert!(is_blocking_builtin("await"));
        assert!(is_blocking_builtin("join"));
        assert!(!is_blocking_builtin("print"));
    }

    #[test]
    fn test_actor_builtins() {
        assert!(is_actor_builtin("spawn"));
        assert!(is_actor_builtin("send"));
        assert!(!is_actor_builtin("print"));
    }
}
