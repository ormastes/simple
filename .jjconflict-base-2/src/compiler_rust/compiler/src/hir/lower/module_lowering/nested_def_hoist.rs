// Nested type-definition hoisting for HIR module lowering.
//
// HIR rejects type definitions (`class`, `struct`, `enum`, `impl`, `trait`,
// `type` alias, `mixin`, `bitfield`) appearing as statements inside a function
// body — see `stmt_lowering.rs`. Specs in the SPipe DSL frequently define
// helper classes inside `it`/`describe` lambda blocks, e.g.:
//
//     describe "X":
//         it "uses a Point":
//             class Point:
//                 x: i32
//                 y: i32
//             val p = Point(x: 1, y: 2)
//             expect p.x == 1
//
// Without preprocessing those definitions get silently dropped (lenient mode)
// or rejected outright (strict mode), leaving downstream code with
// unresolved type names like `Point`.
//
// This pass walks the AST before any HIR pass runs and lifts every nested
// type definition up to module scope, matching the line-based hoisting that
// `preprocess_spipe_for_smf` does for `*_spec.spl` files. The walker handles
// arbitrary nesting depth, including BDD-style `it`/`describe` blocks
// (`Expr::Call` with a `Lambda { body: DoBlock(..) }` argument).
//
// Name-collision policy: first occurrence wins. If the same nested name
// appears multiple times (e.g. `class IP` redefined per `it` block), only
// the first body is hoisted; later ones are dropped.

use std::collections::HashSet;

use simple_parser::{ast, Expr, Module, Node};

/// Returns true for AST nodes that are type definitions which the HIR
/// requires to live at module scope.
fn is_hoistable_def(node: &Node) -> bool {
    matches!(
        node,
        Node::Class(_)
            | Node::Struct(_)
            | Node::Enum(_)
            | Node::Trait(_)
            | Node::Impl(_)
            | Node::Mixin(_)
            | Node::TypeAlias(_)
            | Node::ClassAlias(_)
            | Node::Bitfield(_)
    )
}

/// Returns the canonical hoist key for a node, or `None` if the node is not
/// hoistable. The key is used to detect duplicate hoists across multiple
/// nested sites.
fn hoist_key(node: &Node) -> Option<String> {
    match node {
        Node::Class(c) => Some(format!("class::{}", c.name)),
        Node::Struct(s) => Some(format!("struct::{}", s.name)),
        Node::Enum(e) => Some(format!("enum::{}", e.name)),
        Node::Trait(t) => Some(format!("trait::{}", t.name)),
        Node::Mixin(m) => Some(format!("mixin::{}", m.name)),
        Node::TypeAlias(a) => Some(format!("alias::{}", a.name)),
        Node::ClassAlias(a) => Some(format!("class_alias::{}", a.name)),
        Node::Bitfield(b) => Some(format!("bitfield::{}", b.name)),
        Node::Impl(i) => {
            // For impls, the key is the trait+target signature so distinct
            // impl blocks for the same target type can both be hoisted while
            // structurally identical duplicates collapse.
            let target = match &i.target_type {
                ast::Type::Simple(name) => name.clone(),
                ast::Type::Generic { name, .. } => name.clone(),
                _ => "<other>".to_string(),
            };
            let trait_name = i.trait_name.clone().unwrap_or_default();
            Some(format!("impl::{}::for::{}", trait_name, target))
        }
        _ => None,
    }
}

/// Returns the module-scope name a node would register, when applicable.
/// Used to seed the dedup set so a nested `class Foo` is dropped if the
/// module already declares a top-level `Foo`.
fn module_scope_name(node: &Node) -> Option<String> {
    match node {
        Node::Class(c) => Some(format!("class::{}", c.name)),
        Node::Struct(s) => Some(format!("struct::{}", s.name)),
        Node::Enum(e) => Some(format!("enum::{}", e.name)),
        Node::Trait(t) => Some(format!("trait::{}", t.name)),
        Node::Mixin(m) => Some(format!("mixin::{}", m.name)),
        Node::TypeAlias(a) => Some(format!("alias::{}", a.name)),
        Node::ClassAlias(a) => Some(format!("class_alias::{}", a.name)),
        Node::Bitfield(b) => Some(format!("bitfield::{}", b.name)),
        Node::Impl(i) => {
            let target = match &i.target_type {
                ast::Type::Simple(name) => name.clone(),
                ast::Type::Generic { name, .. } => name.clone(),
                _ => "<other>".to_string(),
            };
            let trait_name = i.trait_name.clone().unwrap_or_default();
            Some(format!("impl::{}::for::{}", trait_name, target))
        }
        _ => None,
    }
}

/// State accumulator for the recursive walker.
struct Hoister {
    seen: HashSet<String>,
    out: Vec<Node>,
}

impl Hoister {
    fn try_record(&mut self, node: &Node) -> bool {
        if let Some(key) = hoist_key(node) {
            if self.seen.insert(key) {
                self.out.push(node.clone());
                return true;
            }
        }
        false
    }
}

/// Recursively walk a function body looking for nested type definitions.
/// Each definition is recorded once (first-occurrence wins via `seen`),
/// then the walker continues into the definition's own methods so deeply
/// nested specs (e.g. `class` containing `fn` containing nested `class`)
/// also get lifted.
fn walk_block(block: &ast::Block, h: &mut Hoister) {
    for node in &block.statements {
        walk_node(node, h);
    }
}

fn walk_node(node: &Node, h: &mut Hoister) {
    // Record first if hoistable; either way, recurse into anything that
    // could contain further definitions.
    if is_hoistable_def(node) {
        h.try_record(node);
    }

    match node {
        Node::Function(f) => walk_block(&f.body, h),
        Node::Class(c) => {
            for m in &c.methods {
                walk_block(&m.body, h);
            }
        }
        Node::Struct(s) => {
            for m in &s.methods {
                walk_block(&m.body, h);
            }
        }
        Node::Impl(i) => {
            for m in &i.methods {
                walk_block(&m.body, h);
            }
        }
        Node::Trait(t) => {
            for m in &t.methods {
                walk_block(&m.body, h);
            }
        }
        Node::Mixin(m_def) => {
            for m in &m_def.methods {
                walk_block(&m.body, h);
            }
        }
        Node::Expression(e) => walk_expr(e, h),
        Node::Let(l) => {
            if let Some(v) = &l.value {
                walk_expr(v, h);
            }
        }
        Node::Assignment(a) => walk_expr(&a.value, h),
        Node::Return(r) => {
            if let Some(v) = &r.value {
                walk_expr(v, h);
            }
        }
        Node::If(s) => {
            walk_expr(&s.condition, h);
            walk_block(&s.then_block, h);
            for (_pat, cond, blk) in &s.elif_branches {
                walk_expr(cond, h);
                walk_block(blk, h);
            }
            if let Some(b) = &s.else_block {
                walk_block(b, h);
            }
        }
        Node::While(s) => {
            walk_expr(&s.condition, h);
            walk_block(&s.body, h);
        }
        Node::For(s) => {
            walk_expr(&s.iterable, h);
            walk_block(&s.body, h);
        }
        Node::Loop(s) => walk_block(&s.body, h),
        Node::With(s) => {
            walk_expr(&s.resource, h);
            walk_block(&s.body, h);
        }
        Node::Defer(s) => match &s.body {
            ast::DeferBody::Expr(e) => walk_expr(e, h),
            ast::DeferBody::Block(b) => walk_block(b, h),
        },
        Node::ErrDefer(s) => match &s.body {
            ast::DeferBody::Expr(e) => walk_expr(e, h),
            ast::DeferBody::Block(b) => walk_block(b, h),
        },
        Node::Match(s) => {
            walk_expr(&s.subject, h);
            for arm in &s.arms {
                if let Some(g) = &arm.guard {
                    walk_expr(g, h);
                }
                walk_block(&arm.body, h);
            }
        }
        Node::Skip(s) => {
            if let ast::SkipBody::Block(b) = &s.body {
                walk_block(b, h);
            }
        }
        // Other node variants don't carry blocks/exprs that could nest a
        // type definition in spec-style code. If a future variant adds a
        // nested function body or DoBlock, extend this match.
        _ => {}
    }
}

fn walk_expr(expr: &Expr, h: &mut Hoister) {
    match expr {
        // BDD blocks: `it "..." : <body>` parses as `Call { args: [<name>, Lambda { body: DoBlock(...) }] }`
        Expr::Call { callee, args } => {
            walk_expr(callee, h);
            for arg in args {
                walk_expr(&arg.value, h);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            walk_expr(receiver, h);
            for arg in args {
                walk_expr(&arg.value, h);
            }
        }
        Expr::Lambda { body, .. } => walk_expr(body, h),
        Expr::DoBlock(nodes) => {
            for n in nodes {
                walk_node(n, h);
            }
        }
        Expr::Binary { left, right, .. } => {
            walk_expr(left, h);
            walk_expr(right, h);
        }
        Expr::Unary { operand, .. } => walk_expr(operand, h),
        Expr::Index { receiver, index } => {
            walk_expr(receiver, h);
            walk_expr(index, h);
        }
        Expr::FieldAccess { receiver, .. } => walk_expr(receiver, h),
        Expr::TupleIndex { receiver, .. } => walk_expr(receiver, h),
        Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => {
            for it in items {
                walk_expr(it, h);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            walk_expr(condition, h);
            walk_expr(then_branch, h);
            if let Some(e) = else_branch {
                walk_expr(e, h);
            }
        }
        Expr::Match { subject, arms } => {
            walk_expr(subject, h);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    walk_expr(g, h);
                }
                walk_block(&arm.body, h);
            }
        }
        Expr::Spread(e) | Expr::DictSpread(e) => walk_expr(e, h),
        // Other Expr variants don't carry function-body-shaped children we
        // need to descend into for definition hoisting. If a future Expr
        // variant introduces nested statements, extend this match.
        _ => {}
    }
}

/// Find every nested type definition inside the AST module's function bodies
/// (and BDD lambda bodies) and return them, ready to be prepended to the
/// module's items. Returns an empty `Vec` when the module has no nested
/// definitions.
///
/// Module-scope definitions are seeded into the dedup set first, so a nested
/// `class Foo` is silently dropped when a module-scope `class Foo` already
/// exists. Among multiple equally-named nested definitions, the first one
/// encountered (depth-first, source order) wins.
pub(super) fn collect_hoisted_defs(items: &[Node]) -> Vec<Node> {
    let mut h = Hoister {
        seen: HashSet::new(),
        out: Vec::new(),
    };

    // Seed with existing module-scope definition names so nested duplicates
    // collapse instead of overwriting.
    for item in items {
        if let Some(key) = module_scope_name(item) {
            h.seen.insert(key);
        }
    }

    // Walk every module item's body for nested defs.
    for item in items {
        walk_node(item, &mut h);
    }

    h.out
}

/// If the AST module has any nested type definitions, return an owned Module
/// whose `items` start with the hoisted definitions (registered as if they
/// were authored at module scope). Otherwise return `None`, signaling the
/// caller can keep using the borrowed module unchanged.
pub fn module_with_hoisted_defs(ast_module: &Module) -> Option<Module> {
    let hoisted = collect_hoisted_defs(&ast_module.items);
    if hoisted.is_empty() {
        return None;
    }
    let mut new_items = Vec::with_capacity(hoisted.len() + ast_module.items.len());
    new_items.extend(hoisted);
    new_items.extend(ast_module.items.iter().cloned());
    Some(Module {
        name: ast_module.name.clone(),
        items: new_items,
    })
}
