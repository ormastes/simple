//! Shape check (`SPL-PAT-001`, error by default for Some/None) for `Option`/`Result` patterns lowered
//! against a scrutinee whose static type can never be one.
//!
//! Bug:
//! `doc/08_tracking/bug/option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`
//!
//! ## Why this exists separately from the interpreter's check
//!
//! `interpreter_patterns.rs` carries the same warning keyed on the *runtime
//! value*. That instrument is structurally blind to the default engine: a bare
//! `simple foo.spl` runs parse -> `hir::lower` -> MIR -> Cranelift JIT and never
//! enters the AST interpreter. Measured 2026-08-01 at `f7b68068a3e` with
//! unconditional probes in four candidate match implementations, on an 11-site
//! probe:
//!
//! | site | JIT run | `SIMPLE_EXECUTION_MODE=interpret` |
//! |---|---|---|
//! | `hir/lower/stmt_lowering.rs` `lower_pattern_condition_stmt` | **11** | 0 |
//! | `interpreter_patterns.rs` `Pattern::Enum` | 0 | **11** |
//! | `hir/lower/expr/control.rs` `lower_pattern_condition` | 0 | 0 |
//! | `codegen/instr/pattern.rs` `compile_pattern_test` | 0 | 0 |
//!
//! So the engine that binds the corrupt value decides `case Some(v)` in the HIR
//! *statement* lowering, and the expression-form twin
//! (`hir/lower/expr/control.rs`) handles `val x = match ...` instead. Both are
//! instrumented here, which is why this lives in a shared module rather than in
//! either file.
//!
//! ## Why keying on the static type is sound here
//!
//! A nullable `T?` is NOT erased by HIR lowering: it resolves to
//! `HirType::Pointer { inner: T }`, while a bare `T` resolves to
//! `HirType::Int` / `Float` / `Bool` / `Char` / `String`. Measured on the same
//! probe: the 8 defective sites all reported a bare scalar/text subject type and
//! the 2 correct `.at()` sites both reported `Pointer { inner: i64 }`. Only
//! those bare scalar/text types are reported, so a legitimate `T?` scrutinee can
//! never trip this. Anything unknown, `Any`, aggregate, pointer, struct or enum
//! is deliberately NOT reported -- an under-report is correct here, a false
//! positive is not.
//!
//! ## Staging (Ok/Err only)
//!
//! `Some`/`None` are a hard error by default (owner decision 2026-11-13).
//! `Ok`/`Err` promotion is still staged: the tree carries ~2,746
//! Option-shaped and ~4,211 Result-shaped pattern sites across 620 owned files.
//! Enable with `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` (the same switch the
//! interpreter check uses, so one run instruments both engines) to measure the
//! true fallout before any promotion. Do NOT make this quieter -- the silence is
//! the bug.

use crate::hir::lower::error::LowerError;
use crate::hir::types::HirType;

/// `SIMPLE_DIAG_OPTION_PATTERN_SHAPE`: unset/0 = off, `1`/`warn` = warn,
/// `error` = hard error (stage-1 opt-in; the default flip is an owner decision).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ShapeGate {
    Off,
    Warn,
    Error,
}

pub(crate) fn shape_gate() -> ShapeGate {
    match std::env::var("SIMPLE_DIAG_OPTION_PATTERN_SHAPE").as_deref() {
        Ok("1") | Ok("warn") => ShapeGate::Warn,
        Ok("error") | Ok("2") => ShapeGate::Error,
        _ => ShapeGate::Off,
    }
}

/// Stable diagnostic code (config/policy/diagnostic_policy.sdn `SPL-PAT-001`).
pub const SHAPE_ERROR_CODE: &str = "SPL-PAT-001";

/// Marker shared with `driver/src/exec_core.rs::jit_failure_must_propagate` so the
/// error is NOT demoted to an interpreter run.
pub const SHAPE_ERROR_TAG: &str = "error[SPL-PAT-001]";

/// Static name for the subject type, or `None` when the type is one this check
/// deliberately stays silent about.
pub(crate) fn never_option_type_name(ty: &HirType) -> Option<String> {
    use crate::hir::Signedness;
    match ty {
        HirType::Int { bits, signedness } => Some(match signedness {
            Signedness::Signed => format!("i{bits}"),
            _ => format!("u{bits}"),
        }),
        HirType::Float { bits } => Some(format!("f{bits}")),
        HirType::Bool => Some("bool".to_string()),
        HirType::Char => Some("char".to_string()),
        HirType::String => Some("text".to_string()),
        HirType::Void => Some("()".to_string()),
        HirType::Array { .. } => Some("[T]".to_string()),
        HirType::Tuple(_) | HirType::LabeledTuple(_) => Some("tuple".to_string()),
        HirType::Dict { .. } => Some("dict".to_string()),
        HirType::Function { .. } => Some("function".to_string()),
        HirType::Simd { .. } => Some("simd".to_string()),
        HirType::Struct { name, .. } if name != "Option" => Some(format!("struct `{name}`")),
        HirType::Enum { name, .. } if name == "Result" => Some("Result".to_string()),
        // `Pointer` (= `T?`), `Any`, `Unknown`, type parameters, and non-Result enums
        // without explicit pattern context stay silent here.
        _ => None,
    }
}

fn is_option_pattern_owner(pattern_owner: Option<&str>) -> bool {
    matches!(pattern_owner, None | Some("") | Some("_") | Some("Option"))
}

pub(crate) fn never_option_pattern_type_name(
    pattern_owner: Option<&str>,
    variant: &str,
    ty: &HirType,
) -> Option<String> {
    if let Some(name) = never_option_type_name(ty) {
        return Some(name);
    }
    if let HirType::Enum { name, variants, .. } = ty {
        if name != "Option" {
            if is_option_pattern_owner(pattern_owner)
                && !variants.is_empty()
                && !variants.iter().any(|(v, _)| v == variant)
            {
                return Some(format!("enum `{name}`"));
            }
        }
    }
    None
}

/// Where a report came from, as much of it as the lowerer actually knows.
///
/// Until 2026-08-02 the warning carried nothing at all, so a hit named the RUN
/// and not the offending line — recorded as the known gap in §15 of the bug
/// doc, and the reason the measured JIT fallout ("8 warnings in 2 files") could
/// not be triaged: neither spec file contained a `Some(` of its own, and there
/// was no way to say which line of which imported library produced it.
///
/// `line`/`column` come from the spanned AST owner of the pattern (`MatchArm`
/// for a `case`, `IfStmt` for `if val`/`elif val`, `WhileStmt` for
/// `while val`) — `Pattern` itself carries no span. They are `None` for the
/// expression-form `if val`, whose lowering entry point is handed the pattern
/// and condition rather than the statement; that case degrades to
/// `file (fn name)` rather than reporting a stale location from a previous arm.
pub(crate) struct DiagLocation<'a> {
    pub file: Option<&'a std::path::Path>,
    pub function: Option<&'a str>,
    pub line: Option<usize>,
    pub column: Option<usize>,
}

impl DiagLocation<'_> {
    fn render(&self) -> String {
        let file = self
            .file
            .map(|p| p.display().to_string())
            .unwrap_or_else(|| "<unknown file>".to_string());
        let mut out = match (self.line, self.column) {
            (Some(line), Some(column)) => format!("{file}:{line}:{column}"),
            (Some(line), None) => format!("{file}:{line}"),
            _ => file,
        };
        if let Some(function) = self.function {
            out.push_str(&format!(" (fn {function})"));
        }
        out
    }
}

/// Report an `Option`/`Result` pattern lowered against a scrutinee whose static
/// type can never be one.
///
/// `Some`/`None` over a bare scalar/text subject is a hard compile error by
/// default (owner decision 2026-11-13, as Rust E0308 / Swift): the #8675
/// silent "flat bind" was removed. `Ok`/`Err` stay on the staged
/// `SIMPLE_DIAG_OPTION_PATTERN_SHAPE` gate.
///
/// `subject_ty` is the resolved `HirType` of the scrutinee, or `None` when the
/// lowerer could not resolve it (in which case nothing is reported).
pub(crate) fn report_if_never_option(
    variant: &str,
    subject_ty: Option<&HirType>,
    form: &str,
    location: DiagLocation<'_>,
) -> Result<(), LowerError> {
    report_if_never_option_with_owner(None, variant, subject_ty, form, location)
}

pub(crate) fn report_if_never_option_with_owner(
    pattern_owner: Option<&str>,
    variant: &str,
    subject_ty: Option<&HirType>,
    form: &str,
    location: DiagLocation<'_>,
) -> Result<(), LowerError> {
    let option_owner = is_option_pattern_owner(pattern_owner);
    let result_owner = matches!(pattern_owner, None | Some("_") | Some("Result"));
    let option_variant = option_owner && matches!(variant, "Some" | "None" | "nil");
    let result_variant = result_owner && matches!(variant, "Ok" | "Err");
    if !option_variant && !result_variant {
        return Ok(());
    }
    let gate = if option_variant { ShapeGate::Error } else { shape_gate() };
    if gate == ShapeGate::Off {
        return Ok(());
    }
    let Some(ty) = subject_ty else { return Ok(()) };
    let Some(kind) = never_option_pattern_type_name(pattern_owner, variant, ty) else {
        return Ok(());
    };
    let at = location.render();
    let shown = if matches!(variant, "None" | "nil") {
        variant.to_string()
    } else {
        format!("{variant}(_)")
    };
    let expects = if option_variant { "Option<T>" } else { "Result<T, E>" };
    if gate == ShapeGate::Error {
        return Err(LowerError::Unsupported(format!(
            "{SHAPE_ERROR_TAG}: {at}: pattern `{shown}` expects {expects}, found {kind} ({form})\n  \
             fix: a `{kind}` is never nil -- bind it directly (`val j = x`) or remove the pattern; \
             if absence is intended, make the subject `{kind}?` and use `if val j = x:`"
        )));
    }
    eprintln!(
        "warning[{SHAPE_ERROR_CODE}]: {at}: pattern `{shown}` expects {expects}, found {kind} ({form})"
    );
    Ok(())
}

/// Static interpreter pre-check matching `SPL-PAT-001` Option/nil pattern and
/// Option method receiver/default guards before flat-Option runtime execution.
pub(crate) fn check_interpreter_option_shapes(items: &[simple_parser::ast::Node]) -> Option<String> {
    interp_ast_guard::check_module(items)
}

mod interp_ast_guard {
    use std::collections::{HashMap, HashSet};

    use simple_parser::ast::{
        BinOp, Block, DeferBody, Expr, FunctionDef, MatchArm, Mutability, Node, Parameter, Pattern, Type, UnaryOp,
    };

    use super::SHAPE_ERROR_TAG;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum AstShape {
        Unknown,
        Optional(Box<AstShape>),
        Result(Box<AstShape>),
        Array(Box<AstShape>),
        Tuple,
        Dict,
        Struct(String),
        UserEnum(String),
        Scalar(&'static str),
    }

    impl AstShape {
        fn kind_name(&self) -> Option<&str> {
            match self {
                AstShape::Unknown | AstShape::Optional(_) => None,
                AstShape::Result(_) => Some("Result"),
                AstShape::Array(_) => Some("Array"),
                AstShape::Tuple => Some("Tuple"),
                AstShape::Dict => Some("Dict"),
                AstShape::Struct(name) | AstShape::UserEnum(name) => Some(name.as_str()),
                AstShape::Scalar(name) => Some(*name),
            }
        }
    }

    struct ModuleSymbols {
        structs: HashSet<String>,
        enums: HashMap<String, HashSet<String>>,
        user_methods: HashMap<String, HashSet<String>>,
        fn_returns: HashMap<String, AstShape>,
        method_returns: HashMap<(String, String), AstShape>,
        struct_fields: HashMap<(String, String), AstShape>,
    }

    pub(super) fn check_module(items: &[Node]) -> Option<String> {
        let symbols = collect_symbols(items);
        let mut checker = ShapeChecker {
            symbols: &symbols,
            env: HashMap::new(),
            widened_vars: HashSet::new(),
        };
        checker.check_top_items(items)
    }

    fn collect_symbols(items: &[Node]) -> ModuleSymbols {
        let mut structs = HashSet::new();
        let mut enums: HashMap<String, HashSet<String>> = HashMap::new();
        let mut user_methods: HashMap<String, HashSet<String>> = HashMap::new();

        // First pass collects nominal type definitions so signatures can resolve them.
        for item in items {
            match item {
                Node::Struct(s) => {
                    structs.insert(s.name.clone());
                    let mset = user_methods.entry(s.name.clone()).or_default();
                    for m in &s.methods {
                        mset.insert(m.name.clone());
                    }
                }
                Node::Class(c) => {
                    structs.insert(c.name.clone());
                    let mset = user_methods.entry(c.name.clone()).or_default();
                    for m in &c.methods {
                        mset.insert(m.name.clone());
                    }
                }
                Node::Enum(e) => {
                    let vset = e.variants.iter().map(|v| v.name.clone()).collect();
                    enums.insert(e.name.clone(), vset);
                    let mset = user_methods.entry(e.name.clone()).or_default();
                    for m in &e.methods {
                        mset.insert(m.name.clone());
                    }
                }
                Node::Impl(imp) => {
                    if let Some(target) = type_head_name(&imp.target_type) {
                        let mset = user_methods.entry(target).or_default();
                        for m in &imp.methods {
                            mset.insert(m.name.clone());
                        }
                    }
                }
                Node::Extend(ext) => {
                    let mset = user_methods.entry(ext.target_type.clone()).or_default();
                    for m in &ext.methods {
                        mset.insert(m.name.clone());
                    }
                }
                _ => {}
            }
        }

        let mut fn_returns = HashMap::new();
        let mut method_returns = HashMap::new();
        let mut struct_fields = HashMap::new();

        for item in items {
            match item {
                Node::Function(f) => {
                    if let Some(ret) = &f.return_type {
                        fn_returns.insert(
                            f.name.clone(),
                            ast_type_to_shape(ret, &f.generic_params, &structs, &enums),
                        );
                    }
                }
                Node::Struct(s) => {
                    for field in &s.fields {
                        struct_fields.insert(
                            (s.name.clone(), field.name.clone()),
                            ast_type_to_shape(&field.ty, &s.generic_params, &structs, &enums),
                        );
                    }
                    record_method_returns(&s.name, &s.generic_params, &s.methods, &structs, &enums, &mut method_returns);
                }
                Node::Class(c) => {
                    for field in &c.fields {
                        struct_fields.insert(
                            (c.name.clone(), field.name.clone()),
                            ast_type_to_shape(&field.ty, &c.generic_params, &structs, &enums),
                        );
                    }
                    record_method_returns(&c.name, &c.generic_params, &c.methods, &structs, &enums, &mut method_returns);
                }
                Node::Enum(e) => {
                    record_method_returns(&e.name, &e.generic_params, &e.methods, &structs, &enums, &mut method_returns);
                }
                Node::Impl(imp) => {
                    if let Some(target) = type_head_name(&imp.target_type) {
                        record_method_returns(
                            &target,
                            &imp.generic_params,
                            &imp.methods,
                            &structs,
                            &enums,
                            &mut method_returns,
                        );
                    }
                }
                Node::Extend(ext) => {
                    record_method_returns(
                        &ext.target_type,
                        &ext.generic_params,
                        &ext.methods,
                        &structs,
                        &enums,
                        &mut method_returns,
                    );
                }
                _ => {}
            }
        }

        ModuleSymbols {
            structs,
            enums,
            user_methods,
            fn_returns,
            method_returns,
            struct_fields,
        }
    }

    fn record_method_returns(
        owner: &str,
        owner_generics: &[String],
        methods: &[FunctionDef],
        structs: &HashSet<String>,
        enums: &HashMap<String, HashSet<String>>,
        out: &mut HashMap<(String, String), AstShape>,
    ) {
        for m in methods {
            if let Some(ret) = &m.return_type {
                let mut generics: Vec<String> = owner_generics.to_vec();
                generics.extend(m.generic_params.iter().cloned());
                out.insert(
                    (owner.to_string(), m.name.clone()),
                    ast_type_to_shape(ret, &generics, structs, enums),
                );
            }
        }
    }

    fn type_head_name(ty: &Type) -> Option<String> {
        match ty {
            Type::Simple(name) => Some(name.clone()),
            Type::Generic { name, .. } => Some(name.clone()),
            Type::Capability { inner, .. } => type_head_name(inner),
            _ => None,
        }
    }

    fn ast_type_to_shape(
        ty: &Type,
        generic_params: &[String],
        structs: &HashSet<String>,
        enums: &HashMap<String, HashSet<String>>,
    ) -> AstShape {
        match ty {
            Type::Optional(inner) => AstShape::Optional(Box::new(ast_type_to_shape(
                inner,
                generic_params,
                structs,
                enums,
            ))),
            Type::Generic { name, args } => {
                if generic_params.iter().any(|g| g == name) {
                    return AstShape::Unknown;
                }
                match name.as_str() {
                    "Option" => AstShape::Optional(Box::new(
                        args.first()
                            .map(|a| ast_type_to_shape(a, generic_params, structs, enums))
                            .unwrap_or(AstShape::Unknown),
                    )),
                    "Result" => AstShape::Result(Box::new(
                        args.first()
                            .map(|a| ast_type_to_shape(a, generic_params, structs, enums))
                            .unwrap_or(AstShape::Unknown),
                    )),
                    "List" | "Vec" | "Array" | "Slice" => AstShape::Array(Box::new(
                        args.first()
                            .map(|a| ast_type_to_shape(a, generic_params, structs, enums))
                            .unwrap_or(AstShape::Unknown),
                    )),
                    "Dict" | "Map" | "HashMap" => AstShape::Dict,
                    _ if structs.contains(name) => AstShape::Struct(name.clone()),
                    _ if enums.contains_key(name) => AstShape::UserEnum(name.clone()),
                    _ => AstShape::Unknown,
                }
            }
            Type::Simple(name) => {
                if generic_params.iter().any(|g| g == name) {
                    return AstShape::Unknown;
                }
                match name.as_str() {
                    "Option" => AstShape::Optional(Box::new(AstShape::Unknown)),
                    "Result" => AstShape::Result(Box::new(AstShape::Unknown)),
                    "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "isize" | "usize" | "int" => {
                        AstShape::Scalar("i64")
                    }
                    "f32" | "f64" | "float" => AstShape::Scalar("f64"),
                    "bool" => AstShape::Scalar("bool"),
                    "text" | "str" | "String" => AstShape::Scalar("text"),
                    "unit" | "void" | "()" => AstShape::Scalar("()"),
                    "Dict" | "Map" | "HashMap" => AstShape::Dict,
                    "List" | "Vec" | "Array" => AstShape::Array(Box::new(AstShape::Unknown)),
                    _ if structs.contains(name) => AstShape::Struct(name.clone()),
                    _ if enums.contains_key(name) => AstShape::UserEnum(name.clone()),
                    _ => AstShape::Unknown,
                }
            }
            Type::Tuple(elems) => {
                if elems.is_empty() {
                    AstShape::Scalar("()")
                } else {
                    AstShape::Tuple
                }
            }
            Type::LabeledTuple(_) => AstShape::Tuple,
            Type::Array { element, .. } => {
                AstShape::Array(Box::new(ast_type_to_shape(element, generic_params, structs, enums)))
            }
            Type::Function { .. } => AstShape::Scalar("fn"),
            Type::Capability { inner, .. } => ast_type_to_shape(inner, generic_params, structs, enums),
            _ => AstShape::Unknown,
        }
    }

    struct ShapeChecker<'a> {
        symbols: &'a ModuleSymbols,
        env: HashMap<String, AstShape>,
        widened_vars: HashSet<String>,
    }

    impl<'a> ShapeChecker<'a> {
        fn check_top_items(&mut self, items: &[Node]) -> Option<String> {
            let saved_widened = std::mem::take(&mut self.widened_vars);
            collect_widened_assignments(items, &mut self.widened_vars);
            for item in items {
                if let Some(err) = self.check_node(item) {
                    self.widened_vars = saved_widened;
                    return Some(err);
                }
            }
            self.widened_vars = saved_widened;
            None
        }

        fn check_function(&mut self, func: &FunctionDef, extra_generics: &[String]) -> Option<String> {
            let saved_env = self.env.clone();
            let saved_widened = std::mem::take(&mut self.widened_vars);

            let mut generics: Vec<String> = extra_generics.to_vec();
            generics.extend(func.generic_params.iter().cloned());
            collect_widened_assignments(&func.body.statements, &mut self.widened_vars);

            for param in &func.params {
                if let Some(err) = param.default.as_ref().and_then(|d| self.check_expr(d)) {
                    self.env = saved_env;
                    self.widened_vars = saved_widened;
                    return Some(err);
                }
                let shape = param
                    .ty
                    .as_ref()
                    .map(|t| ast_type_to_shape(t, &generics, &self.symbols.structs, &self.symbols.enums))
                    .unwrap_or(AstShape::Unknown);
                self.bind_param(param, shape);
            }

            let res = self.check_block(&func.body);
            self.env = saved_env;
            self.widened_vars = saved_widened;
            res
        }

        fn bind_param(&mut self, param: &Parameter, shape: AstShape) {
            if param.mutability == Mutability::Mutable && param.ty.is_none() && self.widened_vars.contains(&param.name) {
                self.env.insert(param.name.clone(), AstShape::Unknown);
            } else {
                self.env.insert(param.name.clone(), shape);
            }
        }

        fn check_block(&mut self, block: &Block) -> Option<String> {
            let saved = self.env.clone();
            for stmt in &block.statements {
                if let Some(err) = self.check_node(stmt) {
                    self.env = saved;
                    return Some(err);
                }
            }
            self.env = saved;
            None
        }

        fn check_node(&mut self, node: &Node) -> Option<String> {
            match node {
                Node::Function(f) => self.check_function(f, &[]),
                Node::Struct(s) => {
                    for m in &s.methods {
                        if let Some(err) = self.check_function(m, &s.generic_params) {
                            return Some(err);
                        }
                    }
                    None
                }
                Node::Class(c) => {
                    for m in &c.methods {
                        if let Some(err) = self.check_function(m, &c.generic_params) {
                            return Some(err);
                        }
                    }
                    None
                }
                Node::Enum(e) => {
                    for m in &e.methods {
                        if let Some(err) = self.check_function(m, &e.generic_params) {
                            return Some(err);
                        }
                    }
                    None
                }
                Node::Trait(t) => {
                    for m in &t.methods {
                        if let Some(err) = self.check_function(m, &t.generic_params) {
                            return Some(err);
                        }
                    }
                    None
                }
                Node::Impl(imp) => {
                    for m in &imp.methods {
                        if let Some(err) = self.check_function(m, &imp.generic_params) {
                            return Some(err);
                        }
                    }
                    None
                }
                Node::Extend(ext) => {
                    for m in &ext.methods {
                        if let Some(err) = self.check_function(m, &ext.generic_params) {
                            return Some(err);
                        }
                    }
                    None
                }
                Node::Let(let_stmt) => {
                    if let Some(val) = &let_stmt.value {
                        if let Some(err) = self.check_expr(val) {
                            return Some(err);
                        }
                    }
                    let shape = if let Some(ty) = &let_stmt.ty {
                        ast_type_to_shape(ty, &[], &self.symbols.structs, &self.symbols.enums)
                    } else if let Some(val) = &let_stmt.value {
                        self.infer_expr_shape(val)
                    } else {
                        AstShape::Unknown
                    };
                    if let Some(err) = self.check_pattern_against_shape(&let_stmt.pattern, &shape, "let binding") {
                        return Some(err);
                    }
                    self.bind_pattern(&let_stmt.pattern, &shape, let_stmt.mutability, let_stmt.ty.is_some());
                    None
                }
                Node::Const(c) => {
                    if let Some(err) = self.check_expr(&c.value) {
                        return Some(err);
                    }
                    let shape = c
                        .ty
                        .as_ref()
                        .map(|t| ast_type_to_shape(t, &[], &self.symbols.structs, &self.symbols.enums))
                        .unwrap_or_else(|| self.infer_expr_shape(&c.value));
                    self.env.insert(c.name.clone(), shape);
                    None
                }
                Node::Static(s) => {
                    if let Some(err) = self.check_expr(&s.value) {
                        return Some(err);
                    }
                    let shape = s
                        .ty
                        .as_ref()
                        .map(|t| ast_type_to_shape(t, &[], &self.symbols.structs, &self.symbols.enums))
                        .unwrap_or_else(|| self.infer_expr_shape(&s.value));
                    if s.mutability == Mutability::Mutable && s.ty.is_none() && self.widened_vars.contains(&s.name) {
                        self.env.insert(s.name.clone(), AstShape::Unknown);
                    } else {
                        self.env.insert(s.name.clone(), shape);
                    }
                    None
                }
                Node::Assignment(assign) => {
                    if let Some(err) = self.check_expr(&assign.target) {
                        return Some(err);
                    }
                    self.check_expr(&assign.value)
                }
                Node::Return(ret) => ret.value.as_ref().and_then(|v| self.check_expr(v)),
                Node::If(if_stmt) => {
                    if let Some(err) = self.check_expr(&if_stmt.condition) {
                        return Some(err);
                    }
                    let saved = self.env.clone();
                    if let Some(pat) = &if_stmt.let_pattern {
                        let cond_shape = self.infer_expr_shape(&if_stmt.condition);
                        if let Some(err) = self.check_pattern_against_shape(pat, &cond_shape, "if-val condition") {
                            return Some(err);
                        }
                        self.bind_pattern(pat, &cond_shape, Mutability::Immutable, false);
                    }
                    let then_err = self.check_block(&if_stmt.then_block);
                    self.env = saved.clone();
                    if then_err.is_some() {
                        return then_err;
                    }
                    for (elif_pat, elif_cond, elif_block) in &if_stmt.elif_branches {
                        if let Some(err) = self.check_expr(elif_cond) {
                            return Some(err);
                        }
                        if let Some(pat) = elif_pat {
                            let cond_shape = self.infer_expr_shape(elif_cond);
                            if let Some(err) = self.check_pattern_against_shape(pat, &cond_shape, "elif-val condition") {
                                return Some(err);
                            }
                            self.bind_pattern(pat, &cond_shape, Mutability::Immutable, false);
                        }
                        let elif_err = self.check_block(elif_block);
                        self.env = saved.clone();
                        if elif_err.is_some() {
                            return elif_err;
                        }
                    }
                    if let Some(else_blk) = &if_stmt.else_block {
                        return self.check_block(else_blk);
                    }
                    None
                }
                Node::Match(match_stmt) => self.check_match_arms(&match_stmt.subject, &match_stmt.arms),
                Node::While(while_stmt) => {
                    if let Some(err) = self.check_expr(&while_stmt.condition) {
                        return Some(err);
                    }
                    let saved = self.env.clone();
                    if let Some(pat) = &while_stmt.let_pattern {
                        let cond_shape = self.infer_expr_shape(&while_stmt.condition);
                        if let Some(err) = self.check_pattern_against_shape(pat, &cond_shape, "while-val condition") {
                            return Some(err);
                        }
                        self.bind_pattern(pat, &cond_shape, Mutability::Immutable, false);
                    }
                    let err = self.check_block(&while_stmt.body);
                    self.env = saved;
                    err
                }
                Node::For(for_stmt) => {
                    if let Some(err) = self.check_expr(&for_stmt.iterable) {
                        return Some(err);
                    }
                    let iter_shape = self.infer_expr_shape(&for_stmt.iterable);
                    let elem_shape = match iter_shape {
                        AstShape::Array(inner) => *inner,
                        _ => AstShape::Unknown,
                    };
                    if let Some(err) = self.check_pattern_against_shape(&for_stmt.pattern, &elem_shape, "for-loop pattern") {
                        return Some(err);
                    }
                    let saved = self.env.clone();
                    self.bind_pattern(&for_stmt.pattern, &elem_shape, Mutability::Immutable, false);
                    let err = self.check_block(&for_stmt.body);
                    self.env = saved;
                    err
                }
                Node::Loop(loop_stmt) => self.check_block(&loop_stmt.body),
                Node::Guard(guard_stmt) => {
                    if let Some(cond) = &guard_stmt.condition {
                        if let Some(err) = self.check_expr(cond) {
                            return Some(err);
                        }
                    }
                    self.check_expr(&guard_stmt.result)
                }
                Node::Assert(assert_stmt) => self.check_expr(&assert_stmt.condition),
                Node::Assume(assume_stmt) => self.check_expr(&assume_stmt.condition),
                Node::Admit(admit_stmt) => self.check_expr(&admit_stmt.condition),
                Node::Defer(defer_stmt) => match &defer_stmt.body {
                    DeferBody::Expr(e) => self.check_expr(e),
                    DeferBody::Block(b) => self.check_block(b),
                },
                Node::ErrDefer(defer_stmt) => match &defer_stmt.body {
                    DeferBody::Expr(e) => self.check_expr(e),
                    DeferBody::Block(b) => self.check_block(b),
                },
                Node::Context(ctx_stmt) => {
                    if let Some(err) = self.check_expr(&ctx_stmt.context) {
                        return Some(err);
                    }
                    self.check_block(&ctx_stmt.body)
                }
                Node::With(with_stmt) => {
                    if let Some(err) = self.check_expr(&with_stmt.resource) {
                        return Some(err);
                    }
                    self.check_block(&with_stmt.body)
                }
                Node::Expression(expr) => self.check_expr(expr),
                _ => None,
            }
        }

        fn check_match_arms(&mut self, subject: &Expr, arms: &[MatchArm]) -> Option<String> {
            if let Some(err) = self.check_expr(subject) {
                return Some(err);
            }
            let subj_shape = self.infer_expr_shape(subject);
            for arm in arms {
                if let Some(err) = self.check_pattern_against_shape(&arm.pattern, &subj_shape, "match arm") {
                    return Some(err);
                }
                let saved = self.env.clone();
                self.bind_pattern(&arm.pattern, &subj_shape, Mutability::Immutable, false);
                if let Some(guard) = &arm.guard {
                    if let Some(err) = self.check_expr(guard) {
                        self.env = saved;
                        return Some(err);
                    }
                }
                let err = self.check_block(&arm.body);
                self.env = saved;
                if err.is_some() {
                    return err;
                }
            }
            None
        }

        fn check_expr(&mut self, expr: &Expr) -> Option<String> {
            match expr {
                Expr::FString { parts, .. } => {
                    for part in parts {
                        match part {
                            simple_parser::ast::FStringPart::Expr(e)
                            | simple_parser::ast::FStringPart::ExprWithFormat(e, _) => {
                                if let Some(err) = self.check_expr(e) {
                                    return Some(err);
                                }
                            }
                            simple_parser::ast::FStringPart::Literal(_) => {}
                        }
                    }
                    None
                }
                Expr::GenericInst { expr, .. } | Expr::Unary { operand: expr, .. } | Expr::Try(expr)
                | Expr::ForceUnwrap(expr) | Expr::ExistsCheck(expr) | Expr::Cast { expr, .. } => {
                    self.check_expr(expr)
                }
                Expr::Binary { left, right, .. } => self.check_expr(left).or_else(|| self.check_expr(right)),
                Expr::Call { callee, args } => {
                    if let Some(err) = self.check_expr(callee) {
                        return Some(err);
                    }
                    for arg in args {
                        if let Some(err) = self.check_expr(&arg.value) {
                            return Some(err);
                        }
                    }
                    None
                }
                Expr::MethodCall {
                    receiver,
                    method,
                    args,
                    ..
                } => {
                    if let Some(err) = self.check_expr(receiver) {
                        return Some(err);
                    }
                    for arg in args {
                        if let Some(err) = self.check_expr(&arg.value) {
                            return Some(err);
                        }
                    }
                    self.check_option_method_call(receiver, method, args)
                }
                Expr::OptionalMethodCall { receiver, args, .. } => {
                    if let Some(err) = self.check_expr(receiver) {
                        return Some(err);
                    }
                    for arg in args {
                        if let Some(err) = self.check_expr(&arg.value) {
                            return Some(err);
                        }
                    }
                    None
                }
                Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => {
                    self.check_expr(receiver)
                }
                Expr::Index { receiver, index } => self.check_expr(receiver).or_else(|| self.check_expr(index)),
                Expr::Lambda { params, body, .. } => {
                    let saved = self.env.clone();
                    for p in params {
                        let shape = p
                            .ty
                            .as_ref()
                            .map(|t| ast_type_to_shape(t, &[], &self.symbols.structs, &self.symbols.enums))
                            .unwrap_or(AstShape::Unknown);
                        self.env.insert(p.name.clone(), shape);
                    }
                    let err = self.check_expr(body);
                    self.env = saved;
                    err
                }
                Expr::If {
                    let_pattern,
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    if let Some(err) = self.check_expr(condition) {
                        return Some(err);
                    }
                    let saved = self.env.clone();
                    if let Some(pat) = let_pattern {
                        let cond_shape = self.infer_expr_shape(condition);
                        if let Some(err) = self.check_pattern_against_shape(pat, &cond_shape, "if-val condition") {
                            return Some(err);
                        }
                        self.bind_pattern(pat, &cond_shape, Mutability::Immutable, false);
                    }
                    let then_err = self.check_expr(then_branch);
                    self.env = saved;
                    if then_err.is_some() {
                        return then_err;
                    }
                    if let Some(else_expr) = else_branch {
                        return self.check_expr(else_expr);
                    }
                    None
                }
                Expr::Match { subject, arms } => self.check_match_arms(subject, arms),
                Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => {
                    for item in items {
                        if let Some(err) = self.check_expr(item) {
                            return Some(err);
                        }
                    }
                    None
                }
                Expr::LabeledTuple(fields) => {
                    for f in fields {
                        if let Some(err) = self.check_expr(&f.value) {
                            return Some(err);
                        }
                    }
                    None
                }
                Expr::ArrayRepeat { value, count } => self.check_expr(value).or_else(|| self.check_expr(count)),
                Expr::Dict(entries) => {
                    for (k, v) in entries {
                        if let Some(err) = self.check_expr(k).or_else(|| self.check_expr(v)) {
                            return Some(err);
                        }
                    }
                    None
                }
                Expr::StructInit { fields, spread, .. } => {
                    for (_, v) in fields {
                        if let Some(err) = self.check_expr(v) {
                            return Some(err);
                        }
                    }
                    if let Some(base) = spread {
                        return self.check_expr(base);
                    }
                    None
                }
                Expr::UnwrapOr { expr: recv, default } | Expr::UnwrapOrReturn { expr: recv, default }
                | Expr::Coalesce { expr: recv, default } => {
                    if let Some(err) = self.check_expr(recv).or_else(|| self.check_expr(default)) {
                        return Some(err);
                    }
                    if matches!(expr, Expr::UnwrapOr { .. }) {
                        return self.check_unwrap_receiver_and_default(recv, "unwrap_or", Some(default));
                    }
                    None
                }
                Expr::UnwrapElse {
                    expr: recv,
                    fallback_fn,
                } => self.check_expr(recv).or_else(|| self.check_expr(fallback_fn)),
                Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes, _) => {
                    let saved = self.env.clone();
                    for node in nodes {
                        if let Some(err) = self.check_node(node) {
                            self.env = saved;
                            return Some(err);
                        }
                    }
                    self.env = saved;
                    None
                }
                Expr::Range { start, end, .. } => {
                    if let Some(s) = start {
                        if let Some(err) = self.check_expr(s) {
                            return Some(err);
                        }
                    }
                    if let Some(e) = end {
                        return self.check_expr(e);
                    }
                    None
                }
                _ => None,
            }
        }

        fn check_option_method_call(
            &self,
            receiver: &Expr,
            method: &str,
            args: &[simple_parser::ast::Argument],
        ) -> Option<String> {
            if !matches!(method, "unwrap" | "unwrap_or" | "expect" | "is_some" | "is_none") {
                return None;
            }
            let default_expr = if method == "unwrap_or" && args.len() == 1 {
                Some(&args[0].value)
            } else {
                None
            };
            self.check_unwrap_receiver_and_default(receiver, method, default_expr)
        }

        fn check_unwrap_receiver_and_default(
            &self,
            receiver: &Expr,
            method: &str,
            default_expr: Option<&Expr>,
        ) -> Option<String> {
            let recv_shape = self.infer_expr_shape(receiver);
            match &recv_shape {
                AstShape::Unknown => None,
                AstShape::Optional(inner) => {
                    if let Some(default) = default_expr {
                        if inner.kind_name().is_some() {
                            let default_shape = self.infer_expr_shape(default);
                            if !unwrap_or_shapes_compatible(inner, &default_shape) {
                                if let (Some(expected_kind), Some(found_kind)) =
                                    (inner.kind_name(), default_shape.kind_name().or_else(|| optional_display(&default_shape)))
                                {
                                    return Some(format!(
                                        "{SHAPE_ERROR_TAG}: Option method 'unwrap_or' default argument type mismatch: \
                                         expected `{expected_kind}`, found `{found_kind}`"
                                    ));
                                }
                            }
                        }
                    }
                    None
                }
                AstShape::Result(inner) => {
                    if matches!(method, "is_some" | "is_none") {
                        return Some(format!(
                            "{SHAPE_ERROR_TAG}: Option method '{method}' requires an optional receiver, found `Result`"
                        ));
                    }
                    if let Some(default) = default_expr {
                        if inner.kind_name().is_some() {
                            let default_shape = self.infer_expr_shape(default);
                            if !unwrap_or_shapes_compatible(inner, &default_shape) {
                                if let (Some(expected_kind), Some(found_kind)) =
                                    (inner.kind_name(), default_shape.kind_name().or_else(|| optional_display(&default_shape)))
                                {
                                    return Some(format!(
                                        "{SHAPE_ERROR_TAG}: Result method 'unwrap_or' default argument type mismatch: \
                                         expected `{expected_kind}`, found `{found_kind}`"
                                    ));
                                }
                            }
                        }
                    }
                    None
                }
                AstShape::Struct(name) | AstShape::UserEnum(name) => {
                    if self
                        .symbols
                        .user_methods
                        .get(name)
                        .is_some_and(|methods| methods.contains(method))
                    {
                        return None;
                    }
                    Some(format!(
                        "{SHAPE_ERROR_TAG}: Option method '{method}' requires an optional receiver, found `{name}`"
                    ))
                }
                other => {
                    if matches!(other, AstShape::Array(_)) && is_ast_slot_yielding_array_accessor(receiver) {
                        return None;
                    }
                    let kind = other.kind_name()?;
                    Some(format!(
                        "{SHAPE_ERROR_TAG}: Option method '{method}' requires an optional receiver, found `{kind}`"
                    ))
                }
            }
        }

        fn check_pattern_against_shape(&self, pattern: &Pattern, shape: &AstShape, form: &str) -> Option<String> {
            match pattern {
                Pattern::Or(pats) => {
                    for p in pats {
                        if let Some(err) = self.check_pattern_against_shape(p, shape, form) {
                            return Some(err);
                        }
                    }
                    None
                }
                Pattern::Typed { pattern, .. } => self.check_pattern_against_shape(pattern, shape, form),
                Pattern::Enum { name: owner, variant, .. } => {
                    if !super::is_option_pattern_owner(Some(owner.as_str()))
                        || !matches!(variant.as_str(), "Some" | "None")
                    {
                        return None;
                    }
                    match shape {
                        AstShape::Unknown | AstShape::Optional(_) => None,
                        AstShape::UserEnum(enum_name) => {
                            let has_variant = self
                                .symbols
                                .enums
                                .get(enum_name)
                                .is_none_or(|variants| variants.is_empty() || variants.contains(variant));
                            if has_variant {
                                return None;
                            }
                            let shown = if variant == "None" {
                                "None".to_string()
                            } else {
                                "Some(_)".to_string()
                            };
                            Some(format_option_pattern_error(&shown, enum_name, form))
                        }
                        other => {
                            let kind = other.kind_name()?;
                            let shown = if variant == "None" {
                                "None".to_string()
                            } else {
                                "Some(_)".to_string()
                            };
                            Some(format_option_pattern_error(&shown, kind, form))
                        }
                    }
                }
                Pattern::Literal(expr) if matches!(**expr, Expr::Nil) => match shape {
                    AstShape::Unknown | AstShape::Optional(_) => None,
                    AstShape::UserEnum(enum_name) => {
                        if self
                            .symbols
                            .enums
                            .get(enum_name)
                            .is_some_and(|variants| variants.contains("nil"))
                        {
                            return None;
                        }
                        Some(format_option_pattern_error("nil", enum_name, form))
                    }
                    other => {
                        let kind = other.kind_name()?;
                        Some(format_option_pattern_error("nil", kind, form))
                    }
                },
                _ => None,
            }
        }

        fn bind_pattern(&mut self, pattern: &Pattern, shape: &AstShape, mutability: Mutability, has_explicit_ty: bool) {
            match pattern {
                Pattern::Identifier(name) | Pattern::MutIdentifier(name) | Pattern::MoveIdentifier(name) => {
                    if mutability == Mutability::Mutable && !has_explicit_ty && self.widened_vars.contains(name) {
                        self.env.insert(name.clone(), AstShape::Unknown);
                    } else {
                        self.env.insert(name.clone(), shape.clone());
                    }
                }
                Pattern::Typed { pattern, ty } => {
                    let ty_shape = ast_type_to_shape(ty, &[], &self.symbols.structs, &self.symbols.enums);
                    self.bind_pattern(pattern, &ty_shape, mutability, true);
                }
                Pattern::Enum {
                    name: owner,
                    variant,
                    payload: Some(subpats),
                } => {
                    if matches!(owner.as_str(), "" | "_" | "Option") && variant == "Some" && subpats.len() == 1 {
                        let inner = match shape {
                            AstShape::Optional(inner) => inner.as_ref().clone(),
                            _ => AstShape::Unknown,
                        };
                        self.bind_pattern(&subpats[0], &inner, mutability, has_explicit_ty);
                    } else if matches!(owner.as_str(), "" | "_" | "Result") && variant == "Ok" && subpats.len() == 1 {
                        let inner = match shape {
                            AstShape::Result(inner) => inner.as_ref().clone(),
                            _ => AstShape::Unknown,
                        };
                        self.bind_pattern(&subpats[0], &inner, mutability, has_explicit_ty);
                    } else {
                        for sub in subpats {
                            self.bind_pattern(sub, &AstShape::Unknown, mutability, false);
                        }
                    }
                }
                Pattern::Tuple(pats) | Pattern::Array(pats) => {
                    let elem = match shape {
                        AstShape::Array(inner) => inner.as_ref().clone(),
                        _ => AstShape::Unknown,
                    };
                    for p in pats {
                        self.bind_pattern(p, &elem, mutability, false);
                    }
                }
                _ => {}
            }
        }

        fn is_enum_variant(&self, enum_name: &str, member: &str) -> bool {
            self.symbols
                .enums
                .get(enum_name)
                .is_some_and(|variants| variants.contains(member))
        }

        fn is_static_type_receiver(&self, owner: &str) -> bool {
            !self.env.contains_key(owner)
                && (matches!(owner, "Option" | "Result")
                    || self.symbols.enums.contains_key(owner)
                    || self.symbols.structs.contains(owner))
        }

        fn infer_static_member_shape(
            &self,
            owner: &str,
            member: &str,
            args: Option<&[simple_parser::ast::Argument]>,
        ) -> AstShape {
            match (owner, member) {
                ("Option", "Some") => {
                    let inner = args
                        .and_then(|a| a.first())
                        .map(|a| self.infer_expr_shape(&a.value))
                        .unwrap_or(AstShape::Unknown);
                    AstShape::Optional(Box::new(inner))
                }
                ("Option", "None") => AstShape::Optional(Box::new(AstShape::Unknown)),
                ("Result", "Ok") => {
                    let inner = args
                        .and_then(|a| a.first())
                        .map(|a| self.infer_expr_shape(&a.value))
                        .unwrap_or(AstShape::Unknown);
                    AstShape::Result(Box::new(inner))
                }
                ("Result", "Err") => AstShape::Result(Box::new(AstShape::Unknown)),
                _ if self.is_enum_variant(owner, member) => AstShape::UserEnum(owner.to_string()),
                _ if self.symbols.enums.contains_key(owner) || self.symbols.structs.contains(owner) => self
                    .symbols
                    .method_returns
                    .get(&(owner.to_string(), member.to_string()))
                    .cloned()
                    .unwrap_or(AstShape::Unknown),
                _ => AstShape::Unknown,
            }
        }

        fn infer_expr_shape(&self, expr: &Expr) -> AstShape {
            match expr {
                Expr::Integer(_) | Expr::TypedInteger(_, _) => AstShape::Scalar("i64"),
                Expr::Float(_) | Expr::TypedFloat(_, _) => AstShape::Scalar("f64"),
                Expr::Bool(_) => AstShape::Scalar("bool"),
                Expr::String(_) | Expr::TypedString(_, _) | Expr::FString { .. } => AstShape::Scalar("text"),
                Expr::Nil => AstShape::Optional(Box::new(AstShape::Unknown)),
                Expr::Array(elems) => {
                    let elem = common_shape(elems.iter().map(|e| self.infer_expr_shape(e)));
                    AstShape::Array(Box::new(elem))
                }
                Expr::ArrayRepeat { value, .. } => AstShape::Array(Box::new(self.infer_expr_shape(value))),
                Expr::Tuple(elems) => {
                    if elems.is_empty() {
                        AstShape::Scalar("()")
                    } else {
                        AstShape::Tuple
                    }
                }
                Expr::LabeledTuple(_) => AstShape::Tuple,
                Expr::Dict(_) => AstShape::Dict,
                Expr::Lambda { .. } => AstShape::Scalar("fn"),
                Expr::StructInit { name, .. } => {
                    if name == "Option" {
                        AstShape::Optional(Box::new(AstShape::Unknown))
                    } else if self.symbols.structs.contains(name) {
                        AstShape::Struct(name.clone())
                    } else {
                        AstShape::Unknown
                    }
                }
                Expr::Identifier(name) => {
                    if matches!(name.as_str(), "nil" | "None") {
                        AstShape::Optional(Box::new(AstShape::Unknown))
                    } else {
                        self.env.get(name).cloned().unwrap_or(AstShape::Unknown)
                    }
                }
                Expr::Path(parts) => {
                    if parts.as_slice() == ["None"] || parts.as_slice() == ["Option", "None"] {
                        AstShape::Optional(Box::new(AstShape::Unknown))
                    } else if parts.len() == 2 {
                        self.infer_static_member_shape(&parts[0], &parts[1], None)
                    } else {
                        AstShape::Unknown
                    }
                }
                Expr::GenericInst { expr, .. } => self.infer_expr_shape(expr),
                Expr::Call { callee, args } => match callee.as_ref() {
                    Expr::Identifier(name) => match name.as_str() {
                        "Some" => {
                            let inner = args
                                .first()
                                .map(|a| self.infer_expr_shape(&a.value))
                                .unwrap_or(AstShape::Unknown);
                            AstShape::Optional(Box::new(inner))
                        }
                        "Ok" => {
                            let inner = args
                                .first()
                                .map(|a| self.infer_expr_shape(&a.value))
                                .unwrap_or(AstShape::Unknown);
                            AstShape::Result(Box::new(inner))
                        }
                        "Err" => AstShape::Result(Box::new(AstShape::Unknown)),
                        _ if self.symbols.structs.contains(name) => AstShape::Struct(name.clone()),
                        _ => self.symbols.fn_returns.get(name).cloned().unwrap_or(AstShape::Unknown),
                    },
                    Expr::Path(parts) if parts.len() == 2 => {
                        self.infer_static_member_shape(&parts[0], &parts[1], Some(args))
                    }
                    Expr::FieldAccess { receiver, field } => match receiver.as_ref() {
                        Expr::Identifier(owner) if self.is_static_type_receiver(owner) => {
                            self.infer_static_member_shape(owner, field, Some(args))
                        }
                        _ => AstShape::Unknown,
                    },
                    _ => AstShape::Unknown,
                },
                Expr::MethodCall {
                    receiver, method, args, ..
                } => {
                    if let Expr::Identifier(owner) = receiver.as_ref() {
                        if self.is_static_type_receiver(owner) {
                            return self.infer_static_member_shape(owner, method, Some(args));
                        }
                    }
                    let recv = self.infer_expr_shape(receiver);
                    match (&recv, method.as_str()) {
                        (AstShape::Optional(inner) | AstShape::Result(inner), "unwrap" | "unwrap_or" | "expect") => {
                            inner.as_ref().clone()
                        }
                        (AstShape::Optional(_) | AstShape::Result(_), "is_some" | "is_none" | "is_ok" | "is_err") => {
                            AstShape::Scalar("bool")
                        }
                        (
                            AstShape::Array(elem),
                            "pop" | "first" | "last" | "remove" | "at" | "get" | "min" | "max",
                        ) => AstShape::Optional(elem.clone()),
                        (AstShape::Array(_), "len" | "length") => AstShape::Scalar("i64"),
                        (AstShape::Array(_), "is_empty") => AstShape::Scalar("bool"),
                        (AstShape::Dict, "get") => AstShape::Optional(Box::new(AstShape::Unknown)),
                        (AstShape::Dict, "len" | "length") => AstShape::Scalar("i64"),
                        (AstShape::Dict, "is_empty" | "contains_key" | "has_key" | "has") => {
                            AstShape::Scalar("bool")
                        }
                        (AstShape::Result(_), "ok" | "err") => AstShape::Optional(Box::new(AstShape::Unknown)),
                        (AstShape::Struct(owner) | AstShape::UserEnum(owner), m) => self
                            .symbols
                            .method_returns
                            .get(&(owner.clone(), m.to_string()))
                            .cloned()
                            .unwrap_or(AstShape::Unknown),
                        _ => AstShape::Unknown,
                    }
                }
                Expr::OptionalMethodCall { .. } => AstShape::Optional(Box::new(AstShape::Unknown)),
                Expr::FieldAccess { receiver, field } => {
                    if let Expr::Identifier(owner) = receiver.as_ref() {
                        if !self.env.contains_key(owner)
                            && (owner == "Option" || self.symbols.enums.contains_key(owner))
                        {
                            return self.infer_static_member_shape(owner, field, None);
                        }
                    }
                    if let AstShape::Struct(owner) = self.infer_expr_shape(receiver) {
                        self.symbols
                            .struct_fields
                            .get(&(owner, field.clone()))
                            .cloned()
                            .unwrap_or(AstShape::Unknown)
                    } else {
                        AstShape::Unknown
                    }
                }
                Expr::Cast { target_type, .. } => {
                    ast_type_to_shape(target_type, &[], &self.symbols.structs, &self.symbols.enums)
                }
                Expr::UnwrapOr { expr, .. } | Expr::ForceUnwrap(expr) | Expr::Coalesce { expr, .. } => {
                    match self.infer_expr_shape(expr) {
                        AstShape::Optional(inner) | AstShape::Result(inner) => *inner,
                        _ => AstShape::Unknown,
                    }
                }
                Expr::Unary { op, operand } => match op {
                    UnaryOp::Not => AstShape::Scalar("bool"),
                    UnaryOp::Neg => match self.infer_expr_shape(operand) {
                        s @ (AstShape::Scalar("i64") | AstShape::Scalar("f64")) => s,
                        _ => AstShape::Unknown,
                    },
                    _ => AstShape::Unknown,
                },
                Expr::Binary { op, left, right } => match op {
                    BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq | BinOp::And | BinOp::Or => {
                        AstShape::Scalar("bool")
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        match (self.infer_expr_shape(left), self.infer_expr_shape(right)) {
                            (AstShape::Scalar("i64"), AstShape::Scalar("i64")) => AstShape::Scalar("i64"),
                            (AstShape::Scalar("f64"), AstShape::Scalar("f64" | "i64"))
                            | (AstShape::Scalar("i64"), AstShape::Scalar("f64")) => AstShape::Scalar("f64"),
                            (AstShape::Scalar("text"), AstShape::Scalar("text")) if matches!(op, BinOp::Add) => {
                                AstShape::Scalar("text")
                            }
                            _ => AstShape::Unknown,
                        }
                    }
                    _ => AstShape::Unknown,
                },
                Expr::If {
                    then_branch,
                    else_branch: Some(else_branch),
                    ..
                } => {
                    let a = self.infer_expr_shape(then_branch);
                    let b = self.infer_expr_shape(else_branch);
                    common_shape([a, b].into_iter())
                }
                _ => AstShape::Unknown,
            }
        }
    }

    fn optional_display(shape: &AstShape) -> Option<&'static str> {
        match shape {
            AstShape::Optional(_) => Some("Option"),
            _ => None,
        }
    }

    fn format_option_pattern_error(shown: &str, kind: &str, form: &str) -> String {
        format!(
            "{SHAPE_ERROR_TAG}: {form}: pattern `{shown}` expects Option<T>, found {kind}\n  \
             fix: a `{kind}` is never nil -- bind it directly (`val j = x`) or remove the pattern; \
             if absence is intended, make the subject `{kind}?` and use `if val j = x:`"
        )
    }

    fn is_ast_slot_yielding_array_accessor(expr: &Expr) -> bool {
        matches!(
            expr,
            Expr::MethodCall { method, .. } if matches!(method.as_str(), "pop" | "first" | "last" | "remove")
        )
    }

    fn common_shape<I: Iterator<Item = AstShape>>(mut iter: I) -> AstShape {
        let Some(first) = iter.next() else {
            return AstShape::Unknown;
        };
        if matches!(first, AstShape::Unknown) {
            return AstShape::Unknown;
        }
        for next in iter {
            if next != first {
                return match (&first, &next) {
                    (AstShape::Optional(_), AstShape::Optional(_)) => AstShape::Optional(Box::new(AstShape::Unknown)),
                    _ => AstShape::Unknown,
                };
            }
        }
        first
    }

    fn unwrap_or_shapes_compatible(expected: &AstShape, default_shape: &AstShape) -> bool {
        match (expected, default_shape) {
            (AstShape::Unknown, _) | (_, AstShape::Unknown) => true,
            (AstShape::Optional(a), AstShape::Optional(b)) => unwrap_or_shapes_compatible(a, b),
            (AstShape::Optional(_), _) | (_, AstShape::Optional(_)) => false,
            (AstShape::Result(_), AstShape::Result(_)) => true,
            (AstShape::Array(a), AstShape::Array(b)) => unwrap_or_shapes_compatible(a, b),
            (AstShape::Tuple, AstShape::Tuple) => true,
            (AstShape::Dict, AstShape::Dict) => true,
            (AstShape::Struct(a), AstShape::Struct(b)) => a == b,
            (AstShape::UserEnum(a), AstShape::UserEnum(b)) => a == b,
            (AstShape::Scalar(a), AstShape::Scalar(b)) => a == b,
            _ => false,
        }
    }

    fn collect_widened_assignments(nodes: &[Node], out: &mut HashSet<String>) {
        for node in nodes {
            match node {
                Node::Assignment(assign) => {
                    if let Expr::Identifier(name) = &assign.target {
                        out.insert(name.clone());
                    }
                    collect_widened_expr(&assign.value, out);
                }
                Node::Let(l) => {
                    if let Some(val) = &l.value {
                        collect_widened_expr(val, out);
                    }
                }
                Node::If(if_stmt) => {
                    collect_widened_expr(&if_stmt.condition, out);
                    collect_widened_assignments(&if_stmt.then_block.statements, out);
                    for (_, cond, blk) in &if_stmt.elif_branches {
                        collect_widened_expr(cond, out);
                        collect_widened_assignments(&blk.statements, out);
                    }
                    if let Some(else_blk) = &if_stmt.else_block {
                        collect_widened_assignments(&else_blk.statements, out);
                    }
                }
                Node::Match(m) => {
                    collect_widened_expr(&m.subject, out);
                    for arm in &m.arms {
                        collect_widened_assignments(&arm.body.statements, out);
                    }
                }
                Node::While(w) => {
                    collect_widened_expr(&w.condition, out);
                    collect_widened_assignments(&w.body.statements, out);
                }
                Node::For(f) => {
                    collect_widened_expr(&f.iterable, out);
                    collect_widened_assignments(&f.body.statements, out);
                }
                Node::Loop(l) => collect_widened_assignments(&l.body.statements, out),
                Node::Context(c) => {
                    collect_widened_expr(&c.context, out);
                    collect_widened_assignments(&c.body.statements, out);
                }
                Node::With(w) => {
                    collect_widened_expr(&w.resource, out);
                    collect_widened_assignments(&w.body.statements, out);
                }
                Node::Expression(e) => collect_widened_expr(e, out),
                _ => {}
            }
        }
    }

    fn collect_widened_expr(expr: &Expr, out: &mut HashSet<String>) {
        match expr {
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                collect_widened_expr(condition, out);
                collect_widened_expr(then_branch, out);
                if let Some(e) = else_branch {
                    collect_widened_expr(e, out);
                }
            }
            Expr::Match { subject, arms } => {
                collect_widened_expr(subject, out);
                for arm in arms {
                    collect_widened_assignments(&arm.body.statements, out);
                }
            }
            Expr::Call { callee, args } => {
                collect_widened_expr(callee, out);
                for a in args {
                    collect_widened_expr(&a.value, out);
                }
            }
            Expr::MethodCall { receiver, args, .. } | Expr::OptionalMethodCall { receiver, args, .. } => {
                collect_widened_expr(receiver, out);
                for a in args {
                    collect_widened_expr(&a.value, out);
                }
            }
            Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes, _) => collect_widened_assignments(nodes, out),
            _ => {}
        }
    }
}

