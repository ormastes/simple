use simple_parser as ast;
use simple_parser::ast::ReferenceCapability;

use crate::hir::lifetime::{ReferenceOrigin, ScopeKind};
use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{
    ConcurrencyMode, FunctionLayoutHint, HirContract, HirFunction, HirStmt, HirType, LayoutAnchor, LayoutPhase,
    LocalVar, PointerKind, TypeId,
};

/// Whether an unannotated function body produces a value at its boundary.
///
/// Missing return annotations are gradual (`Any`), not `()`.  We still keep
/// genuinely procedural bodies void so an omitted annotation on a setter or
/// registration hook does not manufacture a value-returning ABI.
fn body_produces_value(body: &[HirStmt]) -> bool {
    fn stmt_produces_value(stmt: &HirStmt) -> bool {
        match stmt {
            HirStmt::Return(Some(_)) => true,
            HirStmt::Expr(expr) => expr.ty != TypeId::VOID,
            HirStmt::If {
                then_block,
                else_block: Some(else_block),
                ..
            } => body_produces_value(then_block) && body_produces_value(else_block),
            _ => false,
        }
    }

    body.last().is_some_and(stmt_produces_value) || body.iter().any(|stmt| matches!(stmt, HirStmt::Return(Some(_))))
}

fn is_numeric_type(ty: TypeId) -> bool {
    matches!(
        ty,
        TypeId::I8
            | TypeId::I16
            | TypeId::I32
            | TypeId::I64
            | TypeId::U8
            | TypeId::U16
            | TypeId::U32
            | TypeId::U64
            | TypeId::F32
            | TypeId::F64
    )
}

impl Lowerer {
    /// Whether two TypeIds denote the same type for the declared-return
    /// check.
    ///
    /// TypeIds are MODULE-REGISTRY-LOCAL: `TypeRegistry::register` always
    /// allocates a fresh id, and `register_named` interns by name only per
    /// registry (every `HirModule` owns its own registry). The same named
    /// type therefore legitimately carries DIFFERENT TypeIds at its
    /// declaration site and at a body's trailing-expression site -- within
    /// one module via the structural-registration paths, and across modules
    /// via the per-module registries. Raw TypeId equality rejected 542
    /// app files this way the day this check landed (all previously valid
    /// programs). Compare semantically instead.
    ///
    /// A TypeId that does not resolve in this module's registry belongs to
    /// another module's registry; module-local ids are meaningless across
    /// registries, so those comparisons are admitted. The check's sound
    /// scope is intra-module comparisons, which is also where the
    /// native-struct return ABI risk it was added for lives.
    pub(crate) fn hir_types_compatible(&self, expected: TypeId, found: TypeId) -> bool {
        if expected == TypeId::ANY || found == TypeId::ANY || expected == found {
            return true;
        }
        // `nil` is the language's bottom literal: trailing `nil` arms (and
        // `-> T?` declarations) coerce per gradual typing, and both the
        // self-hosted compiler and the interpreter have always admitted them.
        if expected == TypeId::NIL || found == TypeId::NIL {
            return true;
        }
        // `void` is the dual bottom: a `-> unit`-annotated function may end
        // in a value expression, and a value-declared function may end in a
        // void statement call (the interpreter ignores the value slot and
        // the pre-check compiler admitted every such body).
        if expected == TypeId::VOID || found == TypeId::VOID {
            return true;
        }
        if is_numeric_type(expected) && is_numeric_type(found) {
            return true;
        }
        // Truthiness: the seed itself coerces numeric tails in `-> bool`
        // functions (coerce_exists_tail_in_place), and the interpreter
        // accepts any numeric where a predicate is declared.
        if expected == TypeId::BOOL && is_numeric_type(found) {
            return true;
        }
        match (
            self.module.types.get(expected),
            self.module.types.get(found),
        ) {
            (Some(expected_ty), Some(found_ty)) => {
                // Immutable shared references are value-transparent in
                // Simple: a `shared &T` returned where `T` is declared is
                // accepted by the self-hosted reference compiler and the
                // interpreter alike (e.g. text methods invoked on shared
                // receivers). Admit them interchangeably; mutable/unique
                // references keep strict structural equality.
                if let (
                    HirType::Pointer {
                        kind: PointerKind::Shared,
                        capability: ReferenceCapability::Shared,
                        inner,
                    },
                    _,
                ) = (expected_ty, found_ty)
                {
                    if self.type_ids_compatible(*inner, found) {
                        return true;
                    }
                }
                if let (
                    _,
                    HirType::Pointer {
                        kind: PointerKind::Shared,
                        capability: ReferenceCapability::Shared,
                        inner,
                    },
                ) = (expected_ty, found_ty)
                {
                    if self.type_ids_compatible(expected, *inner) {
                        return true;
                    }
                }
                // An array literal `[a, b, c]` coerces to a declared
                // 3-tuple when the elements pairwise match (the self-hosted
                // compiler and the interpreter both accept this spelling).
                if let (
                    HirType::Tuple(expected_elements),
                    HirType::Array {
                        element: found_element,
                        size: Some(found_size),
                    },
                ) = (expected_ty, found_ty)
                {
                    if expected_elements.len() == *found_size
                        && expected_elements
                            .iter()
                            .all(|element| self.type_ids_compatible(*element, *found_element))
                    {
                        return true;
                    }
                }
                let compatible = self.hir_type_variants_compatible(expected_ty, found_ty);
                if !compatible && std::env::var_os("SIMPLE_SEED_RETURN_TYPE_DEBUG").is_some() {
                    eprintln!(
                        "return-type pair rejected: expected={expected:?} {expected_ty:?} found={found:?} {found_ty:?}"
                    );
                }
                compatible
            }
            _ => true,
        }
    }

    /// Whether the seed's static typing is authoritative for a hard error
    /// here. It is, for plain primitive pairs. Aggregate typing in the
    /// gradual corners (trailing `match` arm unification, cross-module
    /// re-registration, ANY-field fallback copies) is KNOWN to diverge from
    /// the self-hosted reference compiler: an aggregate on either side of
    /// an otherwise-incompatible comparison downgrades the check to a
    /// warning instead of rejecting the program (see
    /// validate_declared_return_type).
    fn hir_type_is_plain(ty: &HirType) -> bool {
        matches!(
            ty,
            HirType::Void
                | HirType::Bool
                | HirType::Any
                | HirType::Char
                | HirType::Int { .. }
                | HirType::Float { .. }
                | HirType::String
                | HirType::Nil
                | HirType::Unknown
        )
    }

    fn type_ids_compatible(&self, expected: TypeId, found: TypeId) -> bool {
        self.hir_types_compatible(expected, found)
    }

    /// Structural comparison of two registry-resolved types. Named
    /// aggregates compare by NAME: field layouts legitimately differ between
    /// an ANY-field fallback registration (see `resolve_type`'s
    /// global_struct_defs path) and a fully-typed declaration, and
    /// duplicate-layout names are erased to ANY upstream.
    fn hir_type_variants_compatible(&self, expected: &HirType, found: &HirType) -> bool {
        use HirType::*;
        match (expected, found) {
            (Void, Void) | (Bool, Bool) | (Any, Any) | (Char, Char) | (String, String)
            | (Nil, Nil) | (Unknown, Unknown) => true,
            (
                Int {
                    bits: expected_bits,
                    signedness: expected_sign,
                },
                Int {
                    bits: found_bits,
                    signedness: found_sign,
                },
            ) => expected_bits == found_bits && expected_sign == found_sign,
            (Float { bits: expected_bits }, Float { bits: found_bits }) => expected_bits == found_bits,
            (
                Pointer {
                    kind: expected_kind,
                    capability: expected_cap,
                    inner: expected_inner,
                },
                Pointer {
                    kind: found_kind,
                    capability: found_cap,
                    inner: found_inner,
                },
            ) => {
                expected_kind == found_kind
                    && expected_cap == found_cap
                    && self.type_ids_compatible(*expected_inner, *found_inner)
            }
            (
                Array {
                    element: expected_element,
                    size: expected_size,
                },
                Array {
                    element: found_element,
                    size: found_size,
                },
            ) => {
                // An empty array literal (`[]`) defaults its element type to
                // i32 during inference but coerces to any array type -- the
                // pre-check compiler accepted every trailing `if/else` with
                // an `[]` arm, and the interpreter still does. Otherwise a
                // dynamic array declaration (size None) admits any fixed-size
                // array of the same element (Simple array literals coerce
                // pervasively between fixed and dynamic spellings), while a
                // fixed-size declaration still requires the exact size.
                *expected_size == Some(0)
                    || *found_size == Some(0)
                    || ((expected_size.is_none() || expected_size == found_size)
                        && self.type_ids_compatible(*expected_element, *found_element))
            }
            (
                Simd {
                    lanes: expected_lanes,
                    element: expected_element,
                },
                Simd {
                    lanes: found_lanes,
                    element: found_element,
                },
            ) => {
                expected_lanes == found_lanes
                    && self.type_ids_compatible(*expected_element, *found_element)
            }
            (Tuple(expected_elements), Tuple(found_elements)) => {
                expected_elements.len() == found_elements.len()
                    && expected_elements
                        .iter()
                        .zip(found_elements.iter())
                        .all(|(a, b)| self.type_ids_compatible(*a, *b))
            }
            (LabeledTuple(expected_fields), LabeledTuple(found_fields)) => {
                expected_fields.len() == found_fields.len()
                    && expected_fields
                        .iter()
                        .zip(found_fields.iter())
                        .all(|((expected_name, expected_ty), (found_name, found_ty))| {
                            expected_name == found_name && self.type_ids_compatible(*expected_ty, *found_ty)
                        })
            }
            (
                Dict {
                    key: expected_key,
                    value: expected_value,
                },
                Dict {
                    key: found_key,
                    value: found_value,
                },
            ) => {
                self.type_ids_compatible(*expected_key, *found_key)
                    && self.type_ids_compatible(*expected_value, *found_value)
            }
            (
                Function {
                    params: expected_params,
                    ret: expected_ret,
                },
                Function {
                    params: found_params,
                    ret: found_ret,
                },
            ) => {
                expected_params.len() == found_params.len()
                    && expected_params
                        .iter()
                        .zip(found_params.iter())
                        .all(|(a, b)| self.type_ids_compatible(*a, *b))
                    && self.type_ids_compatible(*expected_ret, *found_ret)
            }
            (Struct { name: expected_name, .. }, Struct { name: found_name, .. }) => {
                expected_name == found_name
            }
            (Enum { name: expected_name, .. }, Enum { name: found_name, .. }) => {
                expected_name == found_name
            }
            (UnitType { name: expected_name, .. }, UnitType { name: found_name, .. }) => {
                expected_name == found_name
            }
            (Union { variants: expected_variants }, Union { variants: found_variants }) => {
                expected_variants.len() == found_variants.len()
                    && expected_variants
                        .iter()
                        .zip(found_variants.iter())
                        .all(|(a, b)| self.type_ids_compatible(*a, *b))
            }
            (Promise { inner: expected_inner }, Promise { inner: found_inner }) => {
                self.type_ids_compatible(*expected_inner, *found_inner)
            }
            (Mixin { name: expected_name, .. }, Mixin { name: found_name, .. }) => {
                expected_name == found_name
            }
            (Bitfield { name: expected_name, .. }, Bitfield { name: found_name, .. }) => {
                expected_name == found_name
            }
            (ExternClass { name: expected_name }, ExternClass { name: found_name }) => {
                expected_name == found_name
            }
            _ => false,
        }
    }

    pub(crate) fn validate_declared_return_type(&self, expected: TypeId, found: TypeId) -> LowerResult<()> {
        if self.hir_types_compatible(expected, found) {
            return Ok(());
        }
        // Aggregate on either side: the seed's aggregate typing in the
        // gradual corners (trailing `match` arm unification, cross-module
        // re-registration, ANY-field fallback copies) diverges from the
        // self-hosted reference compiler, so an aggregate mismatch cannot be
        // a hard error without rejecting valid programs (observed live:
        // 542 files the day this check landed). Downgrade to a warning; the
        // hard-error scope is primitive-vs-primitive pairs, where the seed's
        // typing IS authoritative.
        let downgrade_to_warning = match (
            self.module.types.get(expected),
            self.module.types.get(found),
        ) {
            (Some(expected_ty), Some(found_ty)) => {
                !Self::hir_type_is_plain(expected_ty) || !Self::hir_type_is_plain(found_ty)
            }
            _ => true,
        };
        if downgrade_to_warning {
            eprintln!(
                "warning: declared return type mismatch admitted (seed aggregate typing not authoritative): expected={expected:?} {:?} found={found:?} {:?}",
                self.module.types.get(expected),
                self.module.types.get(found)
            );
            return Ok(());
        }
        if std::env::var_os("SIMPLE_SEED_RETURN_TYPE_DEBUG").is_some() {
            eprintln!(
                "return-type mismatch debug: expected={expected:?} {:?} found={found:?} {:?}",
                self.module.types.get(expected),
                self.module.types.get(found)
            );
        }
        Err(LowerError::TypeMismatch { expected, found })
    }

    fn validate_implicit_return_type(&self, body: &[HirStmt], expected: TypeId) -> LowerResult<()> {
        match body.last() {
            Some(HirStmt::Expr(expr)) => self.validate_declared_return_type(expected, expr.ty),
            Some(HirStmt::If {
                then_block,
                else_block: Some(else_block),
                ..
            }) => {
                self.validate_implicit_return_type(then_block, expected)?;
                self.validate_implicit_return_type(else_block, expected)
            }
            _ => Ok(()),
        }
    }
}

/// Returns true when a Block represents a stub body that auto-synthesis may replace.
///
/// A body is a stub when it is:
/// - Empty (zero statements), OR
/// - A single `pass` statement (`Node::Pass`), OR
/// - A single bare `pass_todo` / `pass_do_nothing` / `pass_dn` identifier expression, OR
/// - A single `pass_todo(...)` / `pass_do_nothing(...)` / `pass_dn(...)` call expression.
///
/// Any real statement (val binding, return, assignment, …) disqualifies the body
/// so that hand-written registrations are never silently overwritten.
fn is_stub_body(body: &ast::Block) -> bool {
    match body.statements.len() {
        0 => true,
        1 => {
            match &body.statements[0] {
                // `pass` keyword as a statement
                ast::Node::Pass(_) => true,
                ast::Node::Expression(expr) => match expr {
                    // pass_todo("…") / pass_do_nothing() / pass_dn() — call form
                    ast::Expr::Call { callee, .. } => {
                        if let ast::Expr::Identifier(name) = callee.as_ref() {
                            matches!(name.as_str(), "pass_todo" | "pass_do_nothing" | "pass_dn" | "todo")
                        } else {
                            false
                        }
                    }
                    // bare `pass_todo` / `pass_do_nothing` / `pass_dn` with no parens
                    ast::Expr::Identifier(name) => {
                        matches!(name.as_str(), "pass_todo" | "pass_do_nothing" | "pass_dn" | "todo")
                    }
                    _ => false,
                },
                _ => false,
            }
        }
        _ => false,
    }
}

fn type_name_hint(ty: &ast::Type) -> Option<String> {
    match ty {
        ast::Type::Simple(name) => Some(name.clone()),
        ast::Type::Generic { name, .. } => Some(name.clone()),
        ast::Type::Capability { inner, .. } => type_name_hint(inner),
        _ => None,
    }
}

fn normalize_gpu_attr_backend_name(value: &str) -> Option<&'static str> {
    match value.trim().to_ascii_lowercase().as_str() {
        "" | "auto" => Some("auto"),
        "cuda" | "ptx" | "nvptx" | "cuda-ptx" => Some("cuda"),
        "opencl" | "opencl-c" | "opencl-spirv" | "cl" => Some("opencl"),
        "hip" | "hip-cpp" | "hipcc" | "rocm" => Some("hip"),
        _ => None,
    }
}

fn gpu_attr_string_value(expr: &ast::Expr) -> Option<&str> {
    match expr {
        ast::Expr::String(value) => Some(value.as_str()),
        ast::Expr::Identifier(value) => Some(value.as_str()),
        _ => None,
    }
}

/// Asm-embedding contract (doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md
/// A.2): `@section("name")` and `@align(n)` carry an argument that the plain
/// name list drops. Encode them as `section=<name>` / `align=<n>` so the LLVM
/// backend can place the symbol without a new MIR field (same convention as
/// `gpu_target_<backend>` above).
pub(crate) fn append_asm_placement_attribute_metadata(attrs: &mut Vec<String>, attr: &ast::Attribute) {
    match attr.name.as_str() {
        "section" => {
            // A double-quoted literal may parse as a one-part FString.
            let name = match attr.args.as_ref().and_then(|args| args.first()) {
                Some(ast::Expr::String(s)) | Some(ast::Expr::Identifier(s)) => Some(s.clone()),
                Some(ast::Expr::FString { parts, .. }) if parts.len() == 1 => match &parts[0] {
                    ast::FStringPart::Literal(s) => Some(s.clone()),
                    _ => None,
                },
                _ => None,
            };
            if let Some(name) = name {
                if !name.is_empty() {
                    attrs.push(format!("section={name}"));
                }
            }
        }
        "align" => {
            if let Some(ast::Expr::Integer(n)) = attr.args.as_ref().and_then(|args| args.first()) {
                attrs.push(format!("align={n}"));
            }
        }
        _ => {}
    }
}

fn append_gpu_attribute_metadata(attrs: &mut Vec<String>, attr: &ast::Attribute) {
    if attr.name != "gpu" {
        return;
    }

    if !attrs.contains(&"gpu_kernel".to_string()) {
        attrs.push("gpu_kernel".to_string());
    }

    if let Some(args) = &attr.args {
        if let Some(first) = args.first().and_then(gpu_attr_string_value) {
            if let Some(normalized) = normalize_gpu_attr_backend_name(first) {
                attrs.push(format!("gpu_target_{normalized}"));
            }
        }
    }

    if let Some(named_args) = &attr.named_args {
        for (name, value) in named_args {
            if name == "target" {
                if let Some(raw) = gpu_attr_string_value(value) {
                    if let Some(normalized) = normalize_gpu_attr_backend_name(raw) {
                        attrs.push(format!("gpu_target_{normalized}"));
                    }
                }
            }
            if name == "backends" {
                if let Some(raw) = gpu_attr_string_value(value) {
                    for backend in raw.split(',') {
                        if let Some(normalized) = normalize_gpu_attr_backend_name(backend) {
                            attrs.push(format!("gpu_backend_{normalized}"));
                        }
                    }
                }
            }
        }
    }
}

fn block_uses_self(body: &ast::Block) -> bool {
    body.statements.iter().any(node_uses_self)
}

fn node_uses_self(node: &ast::Node) -> bool {
    match node {
        ast::Node::Let(stmt) => stmt.value.as_ref().map(expr_uses_self).unwrap_or(false),
        ast::Node::Assignment(stmt) => expr_uses_self(&stmt.target) || expr_uses_self(&stmt.value),
        ast::Node::Return(stmt) => stmt.value.as_ref().map(expr_uses_self).unwrap_or(false),
        ast::Node::If(stmt) => {
            expr_uses_self(&stmt.condition)
                || block_uses_self(&stmt.then_block)
                || stmt
                    .elif_branches
                    .iter()
                    .any(|(_, condition, block)| expr_uses_self(condition) || block_uses_self(block))
                || stmt.else_block.as_ref().map(block_uses_self).unwrap_or(false)
        }
        ast::Node::Match(stmt) => {
            expr_uses_self(&stmt.subject)
                || stmt
                    .arms
                    .iter()
                    .any(|arm| arm.guard.as_ref().map(expr_uses_self).unwrap_or(false) || block_uses_self(&arm.body))
        }
        ast::Node::For(stmt) => expr_uses_self(&stmt.iterable) || block_uses_self(&stmt.body),
        ast::Node::While(stmt) => expr_uses_self(&stmt.condition) || block_uses_self(&stmt.body),
        ast::Node::Loop(stmt) => block_uses_self(&stmt.body),
        ast::Node::Expression(expr) => expr_uses_self(expr),
        _ => false,
    }
}

fn args_use_self(args: &[ast::Argument]) -> bool {
    args.iter().any(|arg| expr_uses_self(&arg.value))
}

fn expr_uses_self(expr: &ast::Expr) -> bool {
    match expr {
        ast::Expr::Identifier(name) => name == "self",
        ast::Expr::FString { parts, .. } => fstring_parts_use_self(parts),
        ast::Expr::I18nTemplate { parts, args, .. } => {
            fstring_parts_use_self(parts) || args.iter().any(|(_, expr)| expr_uses_self(expr))
        }
        ast::Expr::Binary { left, right, .. } => expr_uses_self(left) || expr_uses_self(right),
        ast::Expr::Unary { operand, .. } => expr_uses_self(operand),
        ast::Expr::Cast { expr, .. } => expr_uses_self(expr),
        ast::Expr::Call { callee, args } => expr_uses_self(callee) || args_use_self(args),
        ast::Expr::MethodCall { receiver, args, .. } => expr_uses_self(receiver) || args_use_self(args),
        ast::Expr::FieldAccess { receiver, .. } => expr_uses_self(receiver),
        ast::Expr::Index { receiver, index } => expr_uses_self(receiver) || expr_uses_self(index),
        ast::Expr::TupleIndex { receiver, .. } => expr_uses_self(receiver),
        ast::Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            expr_uses_self(condition)
                || expr_uses_self(then_branch)
                || else_branch.as_ref().map(|expr| expr_uses_self(expr)).unwrap_or(false)
        }
        ast::Expr::Match { subject, arms } => {
            expr_uses_self(subject)
                || arms
                    .iter()
                    .any(|arm| arm.guard.as_ref().map(expr_uses_self).unwrap_or(false) || block_uses_self(&arm.body))
        }
        ast::Expr::Tuple(exprs) | ast::Expr::Array(exprs) | ast::Expr::VecLiteral(exprs) => {
            exprs.iter().any(expr_uses_self)
        }
        ast::Expr::Dict(pairs) => pairs
            .iter()
            .any(|(key, value)| expr_uses_self(key) || expr_uses_self(value)),
        ast::Expr::ArrayRepeat { value, count } => expr_uses_self(value) || expr_uses_self(count),
        ast::Expr::StructInit { fields, spread, .. } => {
            fields.iter().any(|(_, value)| expr_uses_self(value))
                || spread.as_ref().map(|expr| expr_uses_self(expr)).unwrap_or(false)
        }
        ast::Expr::Yield(value) => value.as_ref().map(|expr| expr_uses_self(expr)).unwrap_or(false),
        ast::Expr::Try(expr)
        | ast::Expr::ForceUnwrap(expr)
        | ast::Expr::ExistsCheck(expr)
        | ast::Expr::Await(expr)
        | ast::Expr::Spawn(expr)
        | ast::Expr::ContractOld(expr) => expr_uses_self(expr),
        ast::Expr::UnwrapOrReturn { expr, default } => expr_uses_self(expr) || expr_uses_self(default),
        ast::Expr::DoBlock(nodes) | ast::Expr::UnsafeBlock(nodes, _) => nodes.iter().any(node_uses_self),
        _ => false,
    }
}

fn fstring_parts_use_self(parts: &[ast::FStringPart]) -> bool {
    parts.iter().any(|part| match part {
        ast::FStringPart::Literal(_) => false,
        ast::FStringPart::Expr(expr) => expr_uses_self(expr),
        ast::FStringPart::ExprWithFormat(expr, _) => expr_uses_self(expr),
    })
}

#[cfg(test)]
mod implicit_receiver_tests {
    use super::expr_uses_self;
    use simple_parser::ast::Expr;

    #[test]
    fn dict_literals_retain_implicit_receiver_from_keys_and_values() {
        let self_expr = || Expr::Identifier("self".to_string());
        let literal = |value: &str| Expr::String(value.to_string());

        assert!(expr_uses_self(&Expr::Dict(vec![(self_expr(), literal("value"))])));
        assert!(expr_uses_self(&Expr::Dict(vec![(literal("key"), self_expr())])));
        assert!(!expr_uses_self(&Expr::Dict(vec![(literal("key"), literal("value"))])));
    }
}

fn driver_manifest_attr(attrs: &[ast::Attribute]) -> Option<&ast::Attribute> {
    attrs
        .iter()
        .find(|attr| attr.name == "driver" || attr.name == "native_lib")
}

/// Extract the `ops=<expr>` named argument from a driver manifest attribute.
///
/// Returns `Some(expr)` when `@driver(...)` or `@native_lib(...)` has an
/// `ops` key in its `named_args`. Returns `None` otherwise.
fn driver_ops_arg(attrs: &[ast::Attribute]) -> Option<ast::Expr> {
    let attr = driver_manifest_attr(attrs)?;
    if let Some(named) = &attr.named_args {
        for (key, val) in named {
            if key == "ops" {
                return Some(val.clone());
            }
        }
    }
    None
}

/// Build the synthesized registration body for a manifest attribute with `ops=X`.
///
/// The generated body is semantically equivalent to the hand-written pattern:
///
/// ```spl
/// val m = DriverManifest.for_driver(<name>, <version>, <class>, <vendor>, <device_ids>)
/// val ops = <ops_expr>
/// return register_static_driver(m, ops)
/// ```
///
/// `fn_name` is used verbatim as the manifest name (the function name, not stripped).
/// Future work: add a `name=` named arg to `@driver(...)` so callers can supply an
/// explicit manifest name instead of having it derived from the registration function.
///
/// The manifest args are lifted directly from the `@driver(...)` attribute's
/// `named_args` list, falling back to positional `args` in declaration order:
///   positional[0] = class, [1] = vendor, [2] = device_ids, [3] = version
/// For `@native_lib(...)`, the manifest uses:
///   DriverManifest.for_native_lib(<name>, <version>)
/// The same order is used by the existing Rust-seed text scanner in `compile.rs`.
fn synthesize_driver_registration_body(
    fn_name: &str,
    attrs: &[ast::Attribute],
    ops_expr: ast::Expr,
    span: ast::Span,
) -> ast::Block {
    // Helper: build a zero-span Argument (positional).
    let pos_arg = |value: ast::Expr| ast::Argument {
        name: None,
        value,
        span,
        label: None,
    };

    // Helper: look up a named arg value from the attribute, then fall back to
    // the positional args list at `fallback_idx`.
    let find_arg = |attr: &ast::Attribute, key: &str, fallback_idx: usize| -> Option<ast::Expr> {
        if let Some(named) = &attr.named_args {
            for (k, v) in named {
                if k == key {
                    return Some(v.clone());
                }
            }
        }
        attr.args.as_ref()?.get(fallback_idx).cloned()
    };

    // Locate the @driver/@native_lib attribute (guaranteed present — caller already checked).
    let manifest_attr = driver_manifest_attr(attrs).unwrap();

    // --- Recover manifest args ---
    // version: @driver positional[3], @native_lib positional[1], or named `version`
    let version_fallback_idx = if manifest_attr.name == "native_lib" { 1 } else { 3 };
    let version_expr = find_arg(manifest_attr, "version", version_fallback_idx)
        .unwrap_or_else(|| ast::Expr::String("0.1".to_string()));

    // --- Build: val m = DriverManifest.for_driver/for_native_lib(...) ---
    let manifest_call = if manifest_attr.name == "native_lib" {
        ast::Expr::MethodCall {
            receiver: Box::new(ast::Expr::Identifier("DriverManifest".to_string())),
            method: "for_native_lib".to_string(),
            args: vec![pos_arg(ast::Expr::String(fn_name.to_string())), pos_arg(version_expr)],
            generic_args: vec![],
        }
    } else {
        // class: positional[0] or named `class`/`dclass`
        let class_expr = find_arg(manifest_attr, "class", 0)
            .or_else(|| find_arg(manifest_attr, "dclass", 0))
            .unwrap_or(ast::Expr::Integer(0));

        // vendor: positional[1] or named `vendor`
        let vendor_expr = find_arg(manifest_attr, "vendor", 1).unwrap_or(ast::Expr::Integer(0));

        // device_ids: positional[2] or named `device`/`devices`
        let device_expr = find_arg(manifest_attr, "device", 2)
            .or_else(|| find_arg(manifest_attr, "devices", 2))
            .unwrap_or_else(|| ast::Expr::Array(vec![]));

        ast::Expr::MethodCall {
            receiver: Box::new(ast::Expr::Identifier("DriverManifest".to_string())),
            method: "for_driver".to_string(),
            args: vec![
                pos_arg(ast::Expr::String(fn_name.to_string())),
                pos_arg(version_expr),
                pos_arg(class_expr),
                pos_arg(vendor_expr),
                pos_arg(device_expr),
            ],
            generic_args: vec![],
        }
    };
    let let_m = ast::Node::Let(ast::LetStmt {
        span,
        pattern: ast::Pattern::Identifier("m".to_string()),
        ty: None,
        value: Some(manifest_call),
        mutability: ast::Mutability::Immutable,
        storage_class: ast::StorageClass::Auto,
        is_ghost: false,
        is_suspend: false,
    });

    // --- Build: val ops = <ops_expr> ---
    let let_ops = ast::Node::Let(ast::LetStmt {
        span,
        pattern: ast::Pattern::Identifier("ops".to_string()),
        ty: None,
        value: Some(ops_expr),
        mutability: ast::Mutability::Immutable,
        storage_class: ast::StorageClass::Auto,
        is_ghost: false,
        is_suspend: false,
    });

    // --- Build: return register_static_driver(m, ops) ---
    let register_call = ast::Expr::Call {
        callee: Box::new(ast::Expr::Identifier("register_static_driver".to_string())),
        args: vec![
            pos_arg(ast::Expr::Identifier("m".to_string())),
            pos_arg(ast::Expr::Identifier("ops".to_string())),
        ],
    };
    let return_stmt = ast::Node::Return(ast::ReturnStmt {
        span,
        value: Some(register_call),
    });

    ast::Block {
        span,
        statements: vec![let_m, let_ops, return_stmt],
    }
}

impl Lowerer {
    /// Parse concurrency mode from function attributes
    /// Returns Actor mode (default) if no attribute is found
    fn parse_concurrency_mode(attrs: &[ast::Attribute]) -> ConcurrencyMode {
        for attr in attrs {
            if attr.name == "concurrency_mode" {
                // #[concurrency_mode(lock_base)]
                if let Some(args) = &attr.args {
                    if let Some(ast::Expr::Identifier(mode)) = args.first() {
                        if let Some(cm) = ConcurrencyMode::from_attr_arg(mode) {
                            return cm;
                        }
                    }
                }
            }
        }
        ConcurrencyMode::Actor // Default
    }

    /// Detect if a function is a constructor
    /// Constructors should always check class invariants, even if private
    ///
    /// A function is considered a constructor if:
    /// - It's a method of a class/struct (owner_type is Some)
    /// - It returns an instance of the owner type
    /// - It doesn't take `self` as first parameter (static factory method)
    fn is_constructor(&self, f: &ast::FunctionDef, owner_type: Option<&str>, return_type: TypeId) -> bool {
        // Must be a method of a class/struct
        let Some(type_name) = owner_type else {
            return false;
        };

        // Must not take self (static method)
        let takes_self = f.params.first().map(|p| p.name == "self").unwrap_or(false);
        if takes_self {
            return false;
        }

        // Must return the owner type
        if let Some(owner_type_id) = self.module.types.lookup(type_name) {
            if return_type == owner_type_id {
                return true;
            }
        }

        // Also check common constructor names as a heuristic
        matches!(f.name.as_str(), "new" | "create" | "default" | "init")
            || f.name.starts_with("from_")
            || f.name.starts_with("with_")
    }

    /// Extract layout hint from #[layout(...)] attributes.
    ///
    /// Supports:
    /// - `#[layout(phase="startup")]` - layout phase annotation
    /// - `#[layout(phase="first_frame")]`
    /// - `#[layout(phase="steady")]`
    /// - `#[layout(phase="cold")]`
    /// - `#[layout(anchor="event_loop")]` - anchor annotation
    /// - `#[layout(pin)]` - pinning flag
    fn extract_layout_hint(&self, attributes: &[ast::Attribute]) -> Option<FunctionLayoutHint> {
        for attr in attributes {
            if attr.name != "layout" {
                continue;
            }

            let mut hint = FunctionLayoutHint::default();
            let mut found_layout = false;

            // Parse attribute arguments like #[layout(phase="startup", pin)]
            if let Some(args) = &attr.args {
                for arg in args {
                    match arg {
                        // Handle named arguments like phase="startup"
                        ast::Expr::Binary {
                            op: ast::BinOp::Eq,
                            left,
                            right,
                        } => {
                            if let ast::Expr::Identifier(key) = left.as_ref() {
                                if let ast::Expr::String(value) = right.as_ref() {
                                    match key.as_str() {
                                        "phase" => {
                                            if let Some(phase) = LayoutPhase::from_str(value) {
                                                hint.phase = phase;
                                                found_layout = true;
                                            }
                                        }
                                        "anchor" => {
                                            if let Some(anchor) = LayoutAnchor::from_str(value) {
                                                hint.anchor = Some(anchor);
                                                found_layout = true;
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                        // Handle flag like pin
                        ast::Expr::Identifier(name) if name == "pin" => {
                            hint.pinned = true;
                            found_layout = true;
                        }
                        _ => {}
                    }
                }
            }

            // Also support #[layout = "phase_name"] shorthand
            if let Some(ast::Expr::String(value)) = &attr.value {
                if let Some(phase) = LayoutPhase::from_str(value) {
                    hint.phase = phase;
                    found_layout = true;
                }
            }

            if found_layout {
                return Some(hint);
            }
        }
        None
    }

    /// Lower a function, optionally injecting type invariants for methods
    /// `owner_type`: If this function is a method, the name of the owning type
    pub(super) fn lower_function(
        &mut self,
        f: &ast::FunctionDef,
        owner_type: Option<&str>,
    ) -> LowerResult<HirFunction> {
        // Local IDs restart for every function. Capabilities retained from the
        // previous function would therefore alias unrelated locals that happen
        // to reuse the same numeric ID. Reuse the table allocation but begin a
        // fresh function-local aliasing domain.
        self.capability_env.clear();

        // Set current class type for Self resolution
        let previous_class_type = self.current_class_type;
        if let Some(type_name) = owner_type {
            self.current_class_type = self.module.types.lookup(type_name);
        }

        // Set function name for lifetime error messages
        let func_name = if let Some(owner) = owner_type {
            format!("{}.{}", owner, f.name)
        } else {
            f.name.clone()
        };
        let previous_function_name = self.current_function_name.clone();
        let previous_function_line = self.current_function_line;
        let fn_flatten_owner = Self::flatten_owner_of(f.attributes.iter().map(|a| a.name.as_str()));
        let previous_function_owner = std::mem::replace(&mut self.current_function_owner, fn_flatten_owner.clone());
        self.current_function_name = Some(func_name.clone());
        // Attribution anchor for the `lenient_types` unresolved-name fallback:
        // `Expr::Identifier` has no span, so the enclosing function's
        // declaration line is the tightest source location available.
        self.current_function_line = Some(f.span.line);
        self.lifetime_context.set_function(&func_name);

        // Enter function scope for lifetime tracking
        self.lifetime_context.enter_scope(ScopeKind::Function, Some(f.span));

        let inject = f.decorators.iter().any(|dec| {
            if let ast::Expr::Identifier(name) = &dec.name {
                name == "inject" || name == "sys_inject"
            } else {
                false
            }
        });

        // Parse concurrency mode from attributes
        let concurrency_mode = Self::parse_concurrency_mode(&f.attributes);

        // An absent annotation is not an explicit unit return. Lower the body
        // in a tagged-value context, then distinguish a value-producing body
        // from a genuine procedure after its HIR is available.
        let declared_return_type = f.return_type.as_ref().map(|ty| self.resolve_type(ty)).transpose()?;
        let return_type = declared_return_type.unwrap_or(TypeId::ANY);

        // Determine if this is a method (has self parameter)
        let has_self = f.params.first().map(|p| p.name == "self").unwrap_or(false);
        let body_uses_self = owner_type.is_some() && !has_self && block_uses_self(&f.body);
        let inject_implicit_self = owner_type.is_some() && !has_self && (!f.is_static || body_uses_self);

        // Create appropriate function context based on whether this is a method
        let mut ctx = if has_self || inject_implicit_self {
            FunctionContext::new_method(return_type, f.is_me_method)
        } else {
            FunctionContext::new(return_type)
        };

        if inject_implicit_self {
            let self_ty = self.current_class_type.unwrap_or(TypeId::VOID);
            let self_mutability = if f.is_me_method {
                ast::Mutability::Mutable
            } else {
                ast::Mutability::Immutable
            };
            self.lifetime_context.register_variable(
                "self",
                ReferenceOrigin::Parameter {
                    name: "self".to_string(),
                    index: 0,
                },
            );
            ctx.add_local("self".to_string(), self_ty, self_mutability);
        }

        // Add parameters as locals and check capability compatibility with mode
        for (param_idx, param) in f.params.iter().enumerate() {
            // Register parameter with lifetime context
            let origin = ReferenceOrigin::Parameter {
                name: param.name.clone(),
                index: param_idx,
            };
            self.lifetime_context.register_variable(&param.name, origin);
            let ty = if let Some(t) = &param.ty {
                // Check if parameter has a capability that's incompatible with the mode
                if let ast::Type::Capability { capability, .. } = t {
                    use crate::hir::capability::CapabilityEnv;
                    CapabilityEnv::check_mode_compatibility(*capability, concurrency_mode, &f.name)
                        .map_err(LowerError::Capability)?;
                }
                self.resolve_type(t)?
            } else if param.name == "self" && owner_type.is_some() {
                // Special case: implicit self parameter in methods
                // The parser adds an implicit self parameter with ty: None
                // We infer it as the class type
                self.current_class_type.unwrap_or(TypeId::VOID)
            } else if self.lenient_types {
                TypeId::ANY
            } else {
                return Err(LowerError::MissingParameterType {
                    param: param.name.clone(),
                    function: f.name.clone(),
                });
            };
            // The parser injects `self` before HIR lowering and records that
            // synthetic parameter as immutable, even for `me` methods.  Once
            // `has_self` is true the mutable implicit-self branch above is not
            // used, so preserve the method contract explicitly here.
            let param_mutability = if param_idx == 0 && param.name == "self" && f.is_me_method {
                ast::Mutability::Mutable
            } else {
                param.mutability
            };
            ctx.add_local_with_inject_and_type_hint(
                param.name.clone(),
                ty,
                param.ty.as_ref().and_then(type_name_hint),
                param_mutability,
                param.inject,
            );
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        // FR-DRIVER-0001: auto-synthesize the registration body when
        //   1. the function has a @driver(..., ops=X) attribute, AND
        //   2. the existing body is a stub (empty or single pass_todo/pass_dn call).
        // This lets drivers declare their registration with just:
        //   @driver(class=DriverClass.Block, vendor=0, device=[0], version="0.1", ops=my_ops)
        //   fn register_my_driver() -> Result<i32, DriverError>:
        //     pass_todo("auto-synthesized")
        // Any real body is left untouched so hand-written registrations keep working.
        let driver_synthesized: Option<ast::Block> = if is_stub_body(&f.body) {
            driver_ops_arg(&f.attributes)
                .map(|ops_expr| synthesize_driver_registration_body(&f.name, &f.attributes, ops_expr, f.span))
        } else {
            None
        };
        let effective_body: &ast::Block = driver_synthesized.as_ref().unwrap_or(&f.body);

        let mut body = self.lower_block(effective_body, &mut ctx)?;
        let return_type = match declared_return_type {
            Some(ty) => ty,
            None if f.name == "main" => TypeId::VOID,
            None if body_produces_value(&body) => TypeId::ANY,
            None => TypeId::VOID,
        };
        ctx.return_type = return_type;
        self.method_return_types.insert(func_name.clone(), return_type);

        // Implicit-return counterpart of the `Node::Return` bool coercion in
        // stmt_lowering: a function declared `-> bool` whose trailing
        // expression is `x.?` is in boolean context, so `.?` must lower to the
        // presence predicate rather than the `T?` value form. Otherwise the
        // value escapes through the function boundary and every `if has(..):`
        // caller branches on the non-zero nil sentinel and takes the wrong
        // branch. Most of the 42 owned `-> bool` functions returning a bare
        // `.?` use this implicit form rather than an explicit `return`.
        //
        // Rewritten structurally on the already-lowered HIR rather than by
        // re-lowering the AST: a second `lower_expr` pass over the same tail
        // re-registers whatever that subtree references, which perturbed the
        // JIT's extern set (observed as a new "unresolved external symbol
        // 'rt_index_of'" bailout demoting the whole browser-engine module to
        // the interpreter). This transform allocates nothing and touches no
        // lowering state.
        //
        // The tail is not always a single trailing `HirStmt::Expr`: a `match`
        // lowers to a chain of `HirStmt::If`, leaving the `.?` as the last
        // statement of a nested `then_block`. `coerce_exists_tail_in_place`
        // walks into those arms; see its doc comment for the measurement.
        if ctx.return_type == TypeId::BOOL {
            Lowerer::coerce_exists_tail_in_place(&mut body);
        }
        if declared_return_type.is_some() {
            if let Err(error) = self.validate_implicit_return_type(&body, return_type) {
                if std::env::var_os("SIMPLE_SEED_RETURN_TYPE_DEBUG").is_some() {
                    eprintln!("return-type mismatch in function {}: {error:?}", func_name);
                }
                return Err(error);
            }
        }

        // Detect suspension operators in function body for async/sync validation.
        // Synthesized bodies (from @driver ops= auto-synthesis) never contain
        // suspension operators, so using the original body is correct in all cases.
        let has_suspension = simple_parser::effect_inference::has_suspension_in_body(&f.body);

        // Lower contract if present, or create one for type invariants
        let mut contract = if let Some(ref ast_contract) = f.contract {
            Some(self.lower_contract(ast_contract, &mut ctx)?)
        } else {
            None
        };

        // Inject type invariants for public methods and constructors (CTR-011)
        // Constructors always check invariants (they establish the invariant)
        // Public methods check invariants (they maintain the invariant)
        // Private methods skip invariants (they're internal helpers)
        let is_ctor = self.is_constructor(f, owner_type, return_type);
        if let Some(type_name) = owner_type {
            if is_ctor || f.visibility.is_public() {
                if let Some(type_invariant) = self.module.type_invariants.get(type_name).cloned() {
                    // Add type invariants to function invariants
                    let contract = contract.get_or_insert_with(HirContract::default);
                    for clause in type_invariant.conditions {
                        contract.invariants.push(clause);
                    }
                }
            }
        }

        // CTR-012: Module boundary checking for public functions
        // Check type invariants for parameters and return values that cross module boundaries
        if f.visibility.is_public() && owner_type.is_none() {
            // Check parameter types for invariants (add as preconditions)
            for (param_idx, param) in params.iter().enumerate() {
                if let Some(type_name) = self.module.types.get_type_name(param.ty) {
                    if let Some(type_invariant) = self.module.type_invariants.get(type_name).cloned() {
                        let contract = contract.get_or_insert_with(HirContract::default);
                        for clause in &type_invariant.conditions {
                            // Substitute self (local 0) with the parameter index
                            let substituted_condition = clause.condition.substitute_local(0, param_idx);
                            contract.preconditions.push(crate::hir::types::HirContractClause {
                                condition: substituted_condition,
                                message: clause
                                    .message
                                    .clone()
                                    .or_else(|| Some(format!("Type invariant for parameter '{}'", param.name))),
                            });
                        }
                    }
                }
            }

            // Check return type for invariants (add as postconditions)
            if let Some(type_name) = self.module.types.get_type_name(return_type) {
                if let Some(type_invariant) = self.module.type_invariants.get(type_name).cloned() {
                    let contract = contract.get_or_insert_with(HirContract::default);
                    for clause in &type_invariant.conditions {
                        // Substitute self (local 0) with ContractResult
                        let substituted_condition = clause.condition.substitute_self_with_result();
                        contract.postconditions.push(crate::hir::types::HirContractClause {
                            condition: substituted_condition,
                            message: clause
                                .message
                                .clone()
                                .or_else(|| Some("Type invariant for return value".to_string())),
                        });
                    }
                }
            }
        }

        // VER-011: Handle return constraint for dependent function types
        // Convert `fn f(x: T) -> U where result.len() == x.len():` to a postcondition
        if let Some(ref constraint_expr) = f.return_constraint {
            let constraint_hir = self.lower_expr(constraint_expr, &mut ctx)?;
            let contract = contract.get_or_insert_with(HirContract::default);
            contract.postconditions.push(crate::hir::types::HirContractClause {
                condition: constraint_hir,
                message: Some("Return constraint".to_string()),
            });
        }

        // Extract attributes for AOP predicate matching.
        // Include both #[attr] attributes and @decorator decorators (that aren't effects).
        let mut attributes: Vec<String> = f.attributes.iter().map(|attr| attr.name.clone()).collect();
        for attr in &f.attributes {
            append_gpu_attribute_metadata(&mut attributes, attr);
            append_asm_placement_attribute_metadata(&mut attributes, attr);
        }
        for dec in &f.decorators {
            if let ast::Expr::Identifier(name) = &dec.name {
                if ast::Effect::from_decorator_name(name).is_none() && !attributes.contains(name) {
                    attributes.push(name.clone());
                }
            }
        }

        // Extract layout hint from #[layout(...)] attribute
        let layout_hint = self.extract_layout_hint(&f.attributes);

        // Extract effects from decorators for AOP effect() selector
        let effects: Vec<String> = f
            .decorators
            .iter()
            .filter_map(|dec| {
                // Extract identifier from decorator expression
                if let ast::Expr::Identifier(name) = &dec.name {
                    // Check if it's an effect decorator
                    if ast::Effect::from_decorator_name(name).is_some() {
                        Some(name.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        // Get module path (currently use module name, will be enhanced later)
        let module_path = self.module.name.clone().unwrap_or_default();

        // Exit function scope for lifetime tracking
        self.lifetime_context.exit_scope();

        // Restore previous class type
        self.current_class_type = previous_class_type;
        self.current_function_name = previous_function_name;
        self.current_function_line = previous_function_line;
        self.current_function_owner = previous_function_owner;

        // Use qualified name for methods (ClassName.method) for DI compatibility
        let name = if let Some(owner) = owner_type {
            format!("{}.{}", owner, f.name)
        } else {
            self.flatten_emitted_symbol(fn_flatten_owner.as_deref(), &f.name)
        };

        // Determine verification mode from effects
        let verification_mode = crate::hir::VerificationMode::from_effects(&f.effects);

        Ok(HirFunction {
            name,
            span: Some(f.span),
            params,
            locals: ctx.locals[params_len..].to_vec(),
            return_type,
            body,
            visibility: f.visibility,
            contract,
            is_pure: f.is_pure(),
            inject,
            concurrency_mode,
            module_path,
            attributes,
            effects,
            layout_hint,
            verification_mode,
            is_ghost: f.is_ghost(),
            is_sync: f.is_sync,
            has_suspension,
        })
    }
}
