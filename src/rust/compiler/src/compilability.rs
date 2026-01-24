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
            for (cond, block) in &if_stmt.elif_branches {
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
            // For loops require collection iteration - needs runtime support
            add_reason(reasons, FallbackReason::CollectionOps);
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
            match op {
                BinOp::In => {
                    add_reason(reasons, FallbackReason::CollectionOps);
                }
                _ => {}
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
            for arg in args {
                analyze_expr(&arg.value, reasons);
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

        // Method calls need runtime dispatch
        Expr::MethodCall { receiver, args, .. } => {
            analyze_expr(receiver, reasons);
            for arg in args {
                analyze_expr(&arg.value, reasons);
            }
            add_reason(reasons, FallbackReason::MethodCall);
        }

        // Field access needs runtime support for dynamic objects
        Expr::FieldAccess { receiver, .. } => {
            analyze_expr(receiver, reasons);
            add_reason(reasons, FallbackReason::FieldAccess);
        }

        // Index access needs collection runtime
        Expr::Index { receiver, index } => {
            analyze_expr(receiver, reasons);
            analyze_expr(index, reasons);
            add_reason(reasons, FallbackReason::CollectionOps);
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

        // Collection literals need heap allocation
        Expr::Array(items) => {
            for item in items {
                analyze_expr(item, reasons);
            }
            add_reason(reasons, FallbackReason::CollectionLiteral);
        }

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
            add_reason(reasons, FallbackReason::CollectionOps);
        }

        // Lambdas/closures need environment capture
        Expr::Lambda { body, .. } => {
            analyze_expr(body, reasons);
            add_reason(reasons, FallbackReason::Closure);
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

        // Struct initialization needs runtime
        Expr::StructInit { fields, .. } => {
            for (_, value) in fields {
                analyze_expr(value, reasons);
            }
            add_reason(reasons, FallbackReason::ObjectConstruction);
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
            for part in parts {
                if let simple_parser::ast::FStringPart::Expr(e) = part {
                    analyze_expr(&e, reasons);
                }
            }
            add_reason(reasons, FallbackReason::StringOps);
        }

        // i18n strings - need runtime locale lookup
        Expr::I18nString { .. } => {
            add_reason(reasons, FallbackReason::NotYetImplemented("i18n string".into()));
        }

        Expr::I18nTemplate { parts, args, .. } => {
            for part in parts {
                if let simple_parser::ast::FStringPart::Expr(e) = part {
                    analyze_expr(e, reasons);
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

        // Path expressions (enum variants)
        Expr::Path(_) => {
            add_reason(reasons, FallbackReason::NotYetImplemented("path".into()));
        }

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
        Expr::UnwrapElse { expr: inner, fallback_fn } => {
            analyze_expr(inner, reasons);
            analyze_expr(fallback_fn, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }
        Expr::UnwrapOrReturn(inner) => {
            analyze_expr(inner, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }

        // Safe cast operators - require type checking at runtime
        Expr::CastOr { expr: inner, default, .. } => {
            analyze_expr(inner, reasons);
            analyze_expr(default, reasons);
            add_reason(reasons, FallbackReason::TryOperator);
        }
        Expr::CastElse { expr: inner, fallback_fn, .. } => {
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
    fn test_function_with_method_call_not_compilable() {
        let results = parse_and_analyze("fn get_len(arr: i64):\n    return arr.len()\n");
        let status = results.get("get_len").unwrap();
        assert!(!status.is_compilable());
        assert!(status.reasons().contains(&FallbackReason::MethodCall));
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
