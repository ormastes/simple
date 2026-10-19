//! Compile-time "move instead of copy" for array values on the JIT lane.
//!
//! Arrays are value types, so `var o = st.output` and `St(output: o)` must not
//! leave two live bindings sharing one heap buffer. The JIT lane has no
//! release mechanism (`MirInst::Drop` is a no-op), so every defensive
//! `rt_array_copy` is retained forever: the round-trip
//! `var o = st.output; o.push(x); st = St(output: o)` kept one full stale copy
//! per iteration (quadratic memory and time — bug
//! `seed_jit_array_copy_never_freed_2026-10-19`).
//!
//! This pass finds the copy sites whose SOURCE is provably uniquely owned and
//! provably dead after the copy, where handing the buffer over is
//! indistinguishable from copying it:
//!
//! * site A — `Let { o, value: Local(s) | FieldAccess { Local(s), .. } }` of
//!   array type: no `rt_array_copy`;
//! * site B — a struct-literal field argument `Local(o)` of a `var` array
//!   local: no `rt_array_copy` (any other `var` argument now IS copied, see
//!   `lowering_expr_struct.rs` and `struct_arg_needs_copy`).
//!
//! Everything it cannot prove keeps the copy. Parameters are never move
//! sources (the caller still owns them). Ownership requires that every write
//! to the local yields a fresh or privately-copied buffer and that every read
//! is one that cannot create a second holder (field projection to a scalar,
//! a non-escaping builtin method receiver, an index base, a copied place
//! initializer, a copied struct-literal argument, the function result).
//! Liveness is a forward scan of the SAME statement list: any later mention,
//! `break`/`continue` at loop depth 0, or falling off a list that does not
//! declare the source keeps the copy; a `return` ends it.

use std::collections::{HashMap, HashSet};

use crate::hir::{HirExpr, HirExprKind, HirFunction, HirStmt, HirType, TypeId, TypeRegistry};

/// Copy sites that may hand the source buffer over instead of copying it.
#[derive(Debug, Default, Clone)]
pub(crate) struct ArrayMoveSites {
    /// Locals whose single array `Let` from a place may move its source.
    pub let_locals: HashSet<usize>,
    /// Array locals whose single struct-literal field use may move them.
    pub struct_field_locals: HashSet<usize>,
    /// Non-parameter `var` locals: the only struct-literal array arguments
    /// lowering copies (or moves). See `struct_arg_needs_copy`.
    pub var_locals: HashSet<usize>,
}

/// True when lowering gives this struct-literal array argument a buffer no
/// other live binding holds: a fresh literal, or a `var` local (copied, or
/// moved when proven dead).
///
/// Projections (`st.data`), parameters, `val` locals, globals and index
/// places are deliberately NOT copied: the functional-update idiom
/// `S(data: st.data, pos: st.pos + 1)` is pervasive (one per bit read in
/// `zstd_bits.spl`), and with no release mechanism a copy there re-creates
/// the leak this pass removes (measured: 128 KiB zstd decode 280 MB -> 2.0 GB).
/// Such arguments keep the base behaviour (the struct field shares the
/// buffer), so they make the struct NOT uniquely owned.
///
/// `array_slot` is the caller's "argument type or declared field type is an
/// array" test; a `var` local only gets a copy in such a slot, so in any other
/// slot (`Any`, generic `T`) it shares its buffer.
pub(crate) fn struct_arg_gets_private_buffer(kind: &HirExprKind, array_slot: bool, sites: &ArrayMoveSites) -> bool {
    match kind {
        HirExprKind::Array(_) | HirExprKind::ArrayRepeat { .. } | HirExprKind::VecLiteral(_) => true,
        HirExprKind::Local(idx) => array_slot && sites.var_locals.contains(idx),
        _ => false,
    }
}

/// True when lowering must emit `rt_array_copy` for this struct-literal
/// argument: a `var` local in an array slot that is not a proven-dead move
/// source. Must stay the copy half of `struct_arg_gets_private_buffer`.
pub(crate) fn struct_arg_needs_copy(kind: &HirExprKind, array_slot: bool, sites: &ArrayMoveSites) -> bool {
    array_slot
        && matches!(kind, HirExprKind::Local(idx)
            if sites.var_locals.contains(idx) && !sites.struct_field_locals.contains(idx))
}

/// Builtin array methods that neither store nor return their receiver.
const NON_ESCAPING_ARRAY_METHODS: &[&str] = &[
    "len", "size", "is_empty", "push", "pop", "get", "contains", "first", "last", "clear", "insert", "remove", "set",
    "index_of",
];

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ctx {
    /// The value may become a second holder.
    Bare,
    /// The expression is a statement; its result is discarded.
    Stmt,
    /// Receiver of a non-escaping builtin array method.
    MethodRecv,
    /// Base of an index or field projection.
    ProjectionBase,
    /// Array place initializer of a `Let` (copied or moved).
    PlaceInit,
    /// `var`-local array argument of a struct literal (copied or moved).
    StructArg,
    /// The function's result. The holder dies with the frame, and any later
    /// statement that could observe a moved buffer is unreachable.
    Return,
}

struct Analysis<'a> {
    registry: &'a TypeRegistry,
    /// `@inject` functions: a struct literal of a type with an `@inject`
    /// `new` lowers to a constructor CALL (`lowering_expr_struct.rs`), which
    /// skips the struct-literal copy entirely.
    inject_functions: &'a HashMap<String, Vec<(TypeId, Option<String>, bool)>>,
    type_value_kinds: &'a HashMap<String, bool>,
    nparams: usize,
    local_tys: Vec<TypeId>,
    disqualified: HashSet<usize>,
    let_counts: HashMap<usize, usize>,
    struct_arg_counts: HashMap<usize, usize>,
    /// Locals mentioned anywhere inside a lambda/generator/future/actor body.
    closure_locals: HashSet<usize>,
    /// `var_locals` only; the other fields stay empty during the analysis.
    var_sites: ArrayMoveSites,
    poisoned: bool,
}

pub(crate) fn compute_array_move_sites(
    func: &HirFunction,
    registry: Option<&TypeRegistry>,
    type_value_kinds: &HashMap<String, bool>,
    inject_functions: &HashMap<String, Vec<(TypeId, Option<String>, bool)>>,
) -> ArrayMoveSites {
    let Some(registry) = registry else {
        // No registry: lowering cannot type the arguments either; still
        // report `var` locals so struct literals copy them.
        return ArrayMoveSites {
            var_locals: var_locals_of(func),
            ..Default::default()
        };
    };
    let mut a = Analysis {
        registry,
        inject_functions,
        type_value_kinds,
        nparams: func.params.len(),
        local_tys: func.params.iter().chain(func.locals.iter()).map(|l| l.ty).collect(),
        disqualified: HashSet::new(),
        let_counts: HashMap::new(),
        struct_arg_counts: HashMap::new(),
        closure_locals: HashSet::new(),
        var_sites: ArrayMoveSites {
            var_locals: var_locals_of(func),
            ..Default::default()
        },
        poisoned: false,
    };
    // The body's trailing expression statement is the implicit return value.
    match func.body.split_last() {
        Some((HirStmt::Expr(tail), rest)) => {
            a.scan_stmts(rest);
            a.scan_expr(tail, Ctx::Return);
        }
        _ => a.scan_stmts(&func.body),
    }
    if a.poisoned {
        return ArrayMoveSites {
            var_locals: a.var_sites.var_locals.clone(),
            ..Default::default()
        };
    }
    let mut sites = ArrayMoveSites {
        var_locals: a.var_sites.var_locals.clone(),
        ..Default::default()
    };
    let mut proven: HashMap<usize, usize> = HashMap::new();
    a.find_sites(&func.body, &mut sites, &mut proven);
    // A struct-literal move is keyed by the local, so EVERY struct-literal
    // use of it must have been proven dead individually.
    for (o, n) in proven {
        if a.struct_arg_counts.get(&o) == Some(&n) {
            sites.struct_field_locals.insert(o);
        }
    }
    sites
}

fn var_locals_of(func: &HirFunction) -> HashSet<usize> {
    let nparams = func.params.len();
    func.locals
        .iter()
        .enumerate()
        .filter(|(_, l)| l.is_mutable())
        .map(|(i, _)| nparams + i)
        .collect()
}

fn is_place(kind: &HirExprKind) -> bool {
    matches!(
        kind,
        HirExprKind::Local(_) | HirExprKind::Global(_) | HirExprKind::FieldAccess { .. } | HirExprKind::Index { .. }
    )
}

fn is_primitive(ty: TypeId) -> bool {
    matches!(
        ty,
        TypeId::VOID
            | TypeId::BOOL
            | TypeId::I8
            | TypeId::I16
            | TypeId::I32
            | TypeId::I64
            | TypeId::U8
            | TypeId::U16
            | TypeId::U32
            | TypeId::U64
            | TypeId::F32
            | TypeId::F64
            | TypeId::STRING
            | TypeId::NIL
    )
}

impl<'a> Analysis<'a> {
    fn is_array(&self, ty: TypeId) -> bool {
        self.registry.get_array_element(ty).is_some()
    }

    /// Mirrors the `is_array_place_alias` type test in `lowering_stmt.rs`
    /// (declared slot type, then initializer type).
    fn let_is_array(&self, local_index: usize, value: &HirExpr) -> bool {
        self.is_array(self.local_ty(local_index)) || self.is_array(value.ty)
    }

    fn is_value_struct(&self, ty: TypeId) -> bool {
        let Some(name) = self.registry.get_type_name(ty) else {
            return false;
        };
        self.type_value_kinds.get(name) == Some(&true) && matches!(self.registry.get(ty), Some(HirType::Struct { .. }))
    }

    /// A literal of this type may lower to an `@inject` constructor call that
    /// stores its arguments uncopied; treat its arguments as escaping.
    fn has_inject_ctor(&self, ty: TypeId) -> bool {
        self.registry
            .get_type_name(ty)
            .is_some_and(|name| self.inject_functions.contains_key(&format!("{name}.new")))
    }

    fn array_slot(&self, struct_ty: TypeId, index: usize, arg: &HirExpr) -> bool {
        self.is_array(arg.ty) || self.struct_field_ty(struct_ty, index).is_some_and(|t| self.is_array(t))
    }

    /// Primitive argument into a primitive (or undeclared) slot: no buffer.
    fn primitive_slot(&self, struct_ty: TypeId, index: usize, arg: &HirExpr) -> bool {
        is_primitive(arg.ty) && self.struct_field_ty(struct_ty, index).map_or(true, is_primitive)
    }

    fn struct_field_ty(&self, struct_ty: TypeId, index: usize) -> Option<TypeId> {
        match self.registry.get(struct_ty) {
            Some(HirType::Struct { fields, .. }) => fields.get(index).map(|(_, t)| *t),
            _ => None,
        }
    }

    fn local_ty(&self, idx: usize) -> TypeId {
        self.local_tys.get(idx).copied().unwrap_or(TypeId::ANY)
    }

    fn disqualify(&mut self, idx: usize) {
        self.disqualified.insert(idx);
    }

    fn owned(&self, idx: usize) -> bool {
        if idx < self.nparams || self.disqualified.contains(&idx) {
            return false;
        }
        let ty = self.local_ty(idx);
        self.is_array(ty) || self.is_value_struct(ty)
    }

    /// A write keeps `idx` uniquely owned only when it produces a fresh or
    /// privately copied buffer.
    fn write_keeps_unique(&self, idx: usize, value: &HirExpr, is_let: bool) -> bool {
        if idx < self.nparams {
            return false;
        }
        let local_is_array = self.is_array(self.local_ty(idx));
        match &value.kind {
            HirExprKind::StructInit { ty, fields } => {
                // Every non-primitive slot must get a private buffer: an
                // `Any`/generic slot can hold an array the literal does not
                // copy, and a nested aggregate is not tracked (accepted loss).
                self.is_value_struct(*ty)
                    && !self.has_inject_ctor(*ty)
                    && fields.iter().enumerate().all(|(i, f)| {
                        self.primitive_slot(*ty, i, f)
                            || struct_arg_gets_private_buffer(&f.kind, self.array_slot(*ty, i, f), &self.var_sites)
                    })
            }
            HirExprKind::Array(_) | HirExprKind::ArrayRepeat { .. } | HirExprKind::VecLiteral(_) => local_is_array,
            // Only a `Let` copies an array place (lowering_stmt.rs); `Assign`
            // stores the handle as is.
            kind if is_place(kind) => is_let && local_is_array,
            _ => false,
        }
    }

    // ---- pass 1: ownership -------------------------------------------------

    fn scan_stmts(&mut self, stmts: &[HirStmt]) {
        for stmt in stmts {
            self.scan_stmt(stmt);
        }
    }

    fn scan_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Let { local_index, value, .. } => {
                *self.let_counts.entry(*local_index).or_insert(0) += 1;
                if let Some(value) = value {
                    if !self.write_keeps_unique(*local_index, value, true) {
                        self.disqualify(*local_index);
                    }
                    let array_place = is_place(&value.kind) && self.let_is_array(*local_index, value);
                    self.scan_expr(value, if array_place { Ctx::PlaceInit } else { Ctx::Bare });
                }
            }
            HirStmt::Assign { target, value } => {
                match &target.kind {
                    HirExprKind::Local(idx) => {
                        if !self.write_keeps_unique(*idx, value, false) {
                            self.disqualify(*idx);
                        }
                    }
                    HirExprKind::FieldAccess { receiver, .. } => {
                        // `s.f = arr` makes `s.f` share `arr`'s buffer.
                        if !is_primitive(value.ty) {
                            if let Some(root) = root_local(receiver) {
                                self.disqualify(root);
                            }
                        }
                        self.scan_expr(receiver, Ctx::ProjectionBase);
                    }
                    HirExprKind::Index { receiver, index } => {
                        self.scan_expr(receiver, Ctx::ProjectionBase);
                        self.scan_expr(index, Ctx::Bare);
                    }
                    _ => self.scan_expr(target, Ctx::Bare),
                }
                self.scan_expr(value, Ctx::Bare);
            }
            HirStmt::Expr(e) => self.scan_expr(e, Ctx::Stmt),
            HirStmt::Return(Some(e)) => self.scan_expr(e, Ctx::Return),
            HirStmt::Return(None) | HirStmt::Break | HirStmt::Continue | HirStmt::ProofHint { .. } => {}
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                self.scan_expr(condition, Ctx::Bare);
                self.scan_stmts(then_block);
                if let Some(else_block) = else_block {
                    self.scan_stmts(else_block);
                }
            }
            HirStmt::While { condition, body, .. } => {
                self.scan_expr(condition, Ctx::Bare);
                self.scan_stmts(body);
            }
            HirStmt::Loop { body, .. } => self.scan_stmts(body),
            HirStmt::For {
                pattern_local,
                iterable,
                body,
                ..
            } => {
                if let Some(idx) = pattern_local {
                    self.disqualify(*idx);
                }
                self.scan_expr(iterable, Ctx::Bare);
                self.scan_stmts(body);
            }
            HirStmt::Assert { condition, .. }
            | HirStmt::Assume { condition, .. }
            | HirStmt::Admit { condition, .. } => self.scan_expr(condition, Ctx::Bare),
            HirStmt::Calc { steps } => {
                for step in steps {
                    self.scan_expr(&step.expr, Ctx::Bare);
                }
            }
            HirStmt::InlineAsm { operands, .. } => {
                for op in operands {
                    self.scan_expr(&op.expr, Ctx::Bare);
                }
            }
            // Deferred code runs at every exit and is not ordered with the
            // forward scan; give up on the whole function.
            HirStmt::Defer { .. } => self.poisoned = true,
        }
    }

    fn scan_expr(&mut self, e: &HirExpr, ctx: Ctx) {
        match &e.kind {
            HirExprKind::Local(idx) => {
                if matches!(ctx, Ctx::Bare | Ctx::Stmt) {
                    self.disqualify(*idx);
                }
            }
            HirExprKind::FieldAccess { receiver, .. } => {
                if let HirExprKind::Local(idx) = &receiver.kind {
                    if matches!(ctx, Ctx::Bare | Ctx::Stmt) && !is_primitive(e.ty) {
                        self.disqualify(*idx);
                    }
                } else {
                    self.scan_expr(receiver, Ctx::ProjectionBase);
                }
            }
            HirExprKind::Index { receiver, index } => {
                self.scan_expr(receiver, Ctx::ProjectionBase);
                self.scan_expr(index, Ctx::Bare);
            }
            HirExprKind::MethodCall {
                receiver, method, args, ..
            } => {
                // `Ctx::Stmt` also reaches the trailing expression statement of
                // a `Block` expression, whose value is NOT discarded. That is
                // safe only because no NON_ESCAPING_ARRAY_METHODS entry returns
                // its receiver; adding one that does (e.g. a chaining `push`)
                // would let `val x = { o.m() }` alias `o` here.
                let non_escaping = self.is_array(receiver.ty)
                    && NON_ESCAPING_ARRAY_METHODS.contains(&method.as_str())
                    && (ctx == Ctx::Stmt || is_primitive(e.ty));
                self.scan_expr(receiver, if non_escaping { Ctx::MethodRecv } else { Ctx::Bare });
                for arg in args {
                    self.scan_expr(arg, Ctx::Bare);
                }
            }
            HirExprKind::StructInit { ty, fields } => {
                let inject_ctor = self.has_inject_ctor(*ty);
                for (i, f) in fields.iter().enumerate() {
                    let array_slot = self.array_slot(*ty, i, f);
                    // Only an argument that gets a private buffer is a
                    // non-escaping read; an uncopied place shares its buffer.
                    if !inject_ctor
                        && array_slot
                        && matches!(f.kind, HirExprKind::Local(_))
                        && struct_arg_gets_private_buffer(&f.kind, array_slot, &self.var_sites)
                    {
                        if let HirExprKind::Local(idx) = &f.kind {
                            *self.struct_arg_counts.entry(*idx).or_insert(0) += 1;
                        }
                        self.scan_expr(f, Ctx::StructArg);
                    } else {
                        self.scan_expr(f, Ctx::Bare);
                    }
                }
            }
            HirExprKind::Lambda { body, captures, .. } => {
                for idx in captures {
                    self.closure_locals.insert(*idx);
                    self.disqualify(*idx);
                }
                self.disqualify_all_in_expr(body);
            }
            HirExprKind::GeneratorCreate { body }
            | HirExprKind::FutureCreate { body }
            | HirExprKind::ActorSpawn { body } => {
                self.poisoned = true;
                self.disqualify_all_in_expr(body);
            }
            HirExprKind::Yield(inner) | HirExprKind::Await(inner) => {
                self.poisoned = true;
                self.scan_expr(inner, Ctx::Bare);
            }
            HirExprKind::Block(stmts) | HirExprKind::UnsafeBlock { statements: stmts, .. } => self.scan_stmts(stmts),
            HirExprKind::LetIn { local_idx, value, body } => {
                self.disqualify(*local_idx);
                self.scan_expr(value, Ctx::Bare);
                self.scan_expr(body, Ctx::Bare);
            }
            _ => {
                let mut children = Vec::new();
                expr_children(e, &mut children);
                for child in children {
                    self.scan_expr(child, Ctx::Bare);
                }
            }
        }
    }

    fn disqualify_all_in_expr(&mut self, e: &HirExpr) {
        let mut locals = HashSet::new();
        collect_locals_expr(e, &mut locals);
        self.closure_locals.extend(locals.iter().copied());
        self.disqualified.extend(locals);
    }

    // ---- pass 2: move sites ------------------------------------------------

    fn find_sites(&self, stmts: &[HirStmt], sites: &mut ArrayMoveSites, proven: &mut HashMap<usize, usize>) {
        for (i, stmt) in stmts.iter().enumerate() {
            // Site A: array `Let` from a place rooted at an owned local.
            if let HirStmt::Let {
                local_index,
                value: Some(value),
                ..
            } = stmt
            {
                let array_let = self.let_is_array(*local_index, value);
                let source = match &value.kind {
                    HirExprKind::Local(s) => Some(*s),
                    HirExprKind::FieldAccess { receiver, .. } => match &receiver.kind {
                        HirExprKind::Local(s) => Some(*s),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(s) = source {
                    if array_let
                        && self.let_counts.get(local_index) == Some(&1)
                        && s != *local_index
                        && !self.closure_locals.contains(local_index)
                        && self.owned(s)
                        && dead_after(stmts, i, s)
                    {
                        sites.let_locals.insert(*local_index);
                    }
                }
            }

            // Site B: struct-literal field argument `Local(o)`.
            // Only statements whose expressions run once per execution; a
            // loop condition re-runs and would hand one buffer to two structs.
            let mut args = Vec::new();
            if matches!(
                stmt,
                HirStmt::Let { .. } | HirStmt::Assign { .. } | HirStmt::Expr(_) | HirStmt::Return(Some(_))
            ) {
                for e in stmt_direct_exprs(stmt) {
                    struct_arg_locals(self, e, &mut args);
                }
            }
            // A `return` ends the frame, so nothing after it can observe `o`.
            let is_return = matches!(stmt, HirStmt::Return(Some(_)));
            for o in args {
                if !self.closure_locals.contains(&o)
                    && self.owned(o)
                    && self.is_array(self.local_ty(o))
                    && count_mentions_stmt(stmt, o) == 1
                    && (is_return || dead_after(stmts, i, o))
                {
                    *proven.entry(o).or_insert(0) += 1;
                }
            }

            // Recurse into nested statement lists.
            match stmt {
                HirStmt::If {
                    then_block, else_block, ..
                } => {
                    self.find_sites(then_block, sites, proven);
                    if let Some(else_block) = else_block {
                        self.find_sites(else_block, sites, proven);
                    }
                }
                HirStmt::While { body, .. } | HirStmt::Loop { body, .. } | HirStmt::For { body, .. } => {
                    self.find_sites(body, sites, proven)
                }
                _ => {}
            }
            for e in stmt_direct_exprs(stmt) {
                self.find_sites_in_expr(e, sites, proven);
            }
        }
    }

    fn find_sites_in_expr(&self, e: &HirExpr, sites: &mut ArrayMoveSites, proven: &mut HashMap<usize, usize>) {
        match &e.kind {
            HirExprKind::Block(stmts) | HirExprKind::UnsafeBlock { statements: stmts, .. } => {
                self.find_sites(stmts, sites, proven)
            }
            HirExprKind::Lambda { .. } => {}
            _ => {
                let mut children = Vec::new();
                expr_children(e, &mut children);
                for child in children {
                    self.find_sites_in_expr(child, sites, proven);
                }
            }
        }
    }
}

/// `Local(o)` struct-literal array arguments reachable from `e` without
/// entering a nested statement list or lambda.
fn struct_arg_locals(a: &Analysis<'_>, e: &HirExpr, out: &mut Vec<usize>) {
    match &e.kind {
        HirExprKind::Block(_) | HirExprKind::UnsafeBlock { .. } | HirExprKind::Lambda { .. } => {}
        HirExprKind::StructInit { ty, fields } => {
            let inject_ctor = a.has_inject_ctor(*ty);
            for (i, f) in fields.iter().enumerate() {
                if let HirExprKind::Local(o) = &f.kind {
                    if !inject_ctor && struct_arg_gets_private_buffer(&f.kind, a.array_slot(*ty, i, f), &a.var_sites) {
                        out.push(*o);
                    }
                } else {
                    struct_arg_locals(a, f, out);
                }
            }
        }
        _ => {
            let mut children = Vec::new();
            expr_children(e, &mut children);
            for child in children {
                struct_arg_locals(a, child, out);
            }
        }
    }
}

/// True when `s` is provably not read again after `stmts[pos]` before being
/// overwritten or going out of scope. Anything unclear answers false.
fn dead_after(stmts: &[HirStmt], pos: usize, s: usize) -> bool {
    for stmt in &stmts[pos + 1..] {
        if let HirStmt::Assign { target, value } = stmt {
            if matches!(target.kind, HirExprKind::Local(t) if t == s) && count_mentions_expr(value, s) == 0 {
                return true;
            }
        }
        if count_mentions_stmt(stmt, s) > 0 || has_loop_exit_at_depth0(stmt) {
            return false;
        }
    }
    // Fell off the list: dead only if this list re-declares (initializes) `s`
    // on every entry.
    stmts
        .iter()
        .any(|st| matches!(st, HirStmt::Let { local_index, value: Some(_), .. } if *local_index == s))
}

fn has_loop_exit_at_depth0(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Break | HirStmt::Continue => true,
        HirStmt::If {
            then_block, else_block, ..
        } => {
            then_block.iter().any(has_loop_exit_at_depth0)
                || else_block
                    .as_ref()
                    .is_some_and(|b| b.iter().any(has_loop_exit_at_depth0))
        }
        // A nested loop owns its own break/continue.
        HirStmt::While { .. } | HirStmt::Loop { .. } | HirStmt::For { .. } => false,
        // A Block expression could hide one; be conservative.
        _ => stmt_direct_exprs(stmt).iter().any(|e| expr_has_block(e)),
    }
}

fn expr_has_block(e: &HirExpr) -> bool {
    match &e.kind {
        HirExprKind::Block(_) | HirExprKind::UnsafeBlock { .. } => true,
        HirExprKind::Lambda { .. } => false,
        _ => {
            let mut children = Vec::new();
            expr_children(e, &mut children);
            children.into_iter().any(expr_has_block)
        }
    }
}

fn root_local(e: &HirExpr) -> Option<usize> {
    match &e.kind {
        HirExprKind::Local(idx) => Some(*idx),
        HirExprKind::FieldAccess { receiver, .. } | HirExprKind::Index { receiver, .. } => root_local(receiver),
        _ => None,
    }
}

fn stmt_direct_exprs(stmt: &HirStmt) -> Vec<&HirExpr> {
    match stmt {
        HirStmt::Let { value: Some(v), .. } => vec![v],
        HirStmt::Assign { target, value } => vec![target, value],
        HirStmt::Expr(e) | HirStmt::Return(Some(e)) => vec![e],
        HirStmt::If { condition, .. } | HirStmt::While { condition, .. } => vec![condition],
        HirStmt::For { iterable, .. } => vec![iterable],
        HirStmt::Assert { condition, .. } | HirStmt::Assume { condition, .. } | HirStmt::Admit { condition, .. } => {
            vec![condition]
        }
        HirStmt::Calc { steps } => steps.iter().map(|s| &s.expr).collect(),
        HirStmt::InlineAsm { operands, .. } => operands.iter().map(|o| &o.expr).collect(),
        _ => Vec::new(),
    }
}

fn count_mentions_stmt(stmt: &HirStmt, s: usize) -> usize {
    let mut locals = Vec::new();
    collect_local_uses_stmt(stmt, &mut locals);
    locals.into_iter().filter(|l| *l == s).count()
}

fn count_mentions_expr(e: &HirExpr, s: usize) -> usize {
    let mut locals = Vec::new();
    collect_local_uses_expr(e, &mut locals);
    locals.into_iter().filter(|l| *l == s).count()
}

fn collect_locals_expr(e: &HirExpr, out: &mut HashSet<usize>) {
    let mut locals = Vec::new();
    collect_local_uses_expr(e, &mut locals);
    out.extend(locals);
}

/// Every local mentioned (read, written, captured, bound) by `stmt`.
fn collect_local_uses_stmt(stmt: &HirStmt, out: &mut Vec<usize>) {
    match stmt {
        HirStmt::Let { local_index, value, .. } => {
            out.push(*local_index);
            if let Some(v) = value {
                collect_local_uses_expr(v, out);
            }
        }
        HirStmt::If {
            condition,
            then_block,
            else_block,
            ..
        } => {
            collect_local_uses_expr(condition, out);
            for s in then_block {
                collect_local_uses_stmt(s, out);
            }
            if let Some(b) = else_block {
                for s in b {
                    collect_local_uses_stmt(s, out);
                }
            }
        }
        HirStmt::While { condition, body, .. } => {
            collect_local_uses_expr(condition, out);
            for s in body {
                collect_local_uses_stmt(s, out);
            }
        }
        HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
            for s in body {
                collect_local_uses_stmt(s, out);
            }
        }
        HirStmt::For {
            pattern_local,
            iterable,
            body,
            ..
        } => {
            if let Some(idx) = pattern_local {
                out.push(*idx);
            }
            collect_local_uses_expr(iterable, out);
            for s in body {
                collect_local_uses_stmt(s, out);
            }
        }
        _ => {
            for e in stmt_direct_exprs(stmt) {
                collect_local_uses_expr(e, out);
            }
        }
    }
}

fn collect_local_uses_expr(e: &HirExpr, out: &mut Vec<usize>) {
    match &e.kind {
        HirExprKind::Local(idx) => out.push(*idx),
        HirExprKind::Lambda {
            body,
            captures,
            param_local_indices,
            ..
        } => {
            out.extend(captures.iter().copied());
            out.extend(param_local_indices.iter().copied());
            collect_local_uses_expr(body, out);
        }
        HirExprKind::LetIn { local_idx, value, body } => {
            out.push(*local_idx);
            collect_local_uses_expr(value, out);
            collect_local_uses_expr(body, out);
        }
        HirExprKind::Block(stmts) | HirExprKind::UnsafeBlock { statements: stmts, .. } => {
            for s in stmts {
                collect_local_uses_stmt(s, out);
            }
        }
        _ => {
            let mut children = Vec::new();
            expr_children(e, &mut children);
            for child in children {
                collect_local_uses_expr(child, out);
            }
        }
    }
}

/// Direct sub-expressions of `e` (statement-list and lambda bodies excluded;
/// callers that need them handle those variants first).
fn expr_children<'e>(e: &'e HirExpr, out: &mut Vec<&'e HirExpr>) {
    match &e.kind {
        HirExprKind::Binary { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        HirExprKind::Unary { operand, .. } => out.push(operand),
        HirExprKind::Call { func, args } => {
            out.push(func);
            out.extend(args.iter());
        }
        HirExprKind::MethodCall { receiver, args, .. } => {
            out.push(receiver);
            out.extend(args.iter());
        }
        HirExprKind::FieldAccess { receiver, .. } => out.push(receiver),
        HirExprKind::Index { receiver, index } => {
            out.push(receiver);
            out.push(index);
        }
        HirExprKind::Tuple(items)
        | HirExprKind::Array(items)
        | HirExprKind::VecLiteral(items)
        | HirExprKind::StructInit { fields: items, .. }
        | HirExprKind::BuiltinCall { args: items, .. }
        | HirExprKind::GpuIntrinsic { args: items, .. } => out.extend(items.iter()),
        HirExprKind::ArrayRepeat { value, count } => {
            out.push(value);
            out.push(count);
        }
        HirExprKind::Dict(pairs) => {
            for (k, v) in pairs {
                out.push(k);
                out.push(v);
            }
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            out.push(condition);
            out.push(then_branch);
            if let Some(b) = else_branch {
                out.push(b);
            }
        }
        HirExprKind::Ref(inner)
        | HirExprKind::Deref(inner)
        | HirExprKind::Yield(inner)
        | HirExprKind::Await(inner)
        | HirExprKind::ContractOld(inner) => out.push(inner),
        HirExprKind::PointerNew { value, .. } => out.push(value),
        HirExprKind::Cast { expr, .. } => out.push(expr),
        HirExprKind::GeneratorCreate { body }
        | HirExprKind::FutureCreate { body }
        | HirExprKind::ActorSpawn { body } => out.push(body),
        HirExprKind::LetIn { value, body, .. } => {
            out.push(value);
            out.push(body);
        }
        HirExprKind::NeighborAccess { array, .. } => out.push(array),
        HirExprKind::Lambda { body, .. } => out.push(body),
        HirExprKind::Integer(_)
        | HirExprKind::Float(_)
        | HirExprKind::String(_)
        | HirExprKind::Bool(_)
        | HirExprKind::Nil
        | HirExprKind::Local(_)
        | HirExprKind::Global(_)
        | HirExprKind::Block(_)
        | HirExprKind::UnsafeBlock { .. }
        | HirExprKind::ContractResult => {}
    }
}
