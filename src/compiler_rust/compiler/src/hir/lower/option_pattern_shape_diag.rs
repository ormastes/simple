//! Warn-only shape check (DEFAULT OFF) for `Option`/`Result` patterns lowered
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
//! ## Default OFF
//!
//! Promotion to a hard error must be staged: the tree carries ~2,746
//! Option-shaped and ~4,211 Result-shaped pattern sites across 620 owned files.
//! Enable with `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` (the same switch the
//! interpreter check uses, so one run instruments both engines) to measure the
//! true fallout before any promotion. Do NOT make this quieter -- the silence is
//! the bug.

use crate::hir::types::HirType;

/// Is the default-off `SIMPLE_DIAG_OPTION_PATTERN_SHAPE` gate on?
fn gate_on() -> bool {
    std::env::var("SIMPLE_DIAG_OPTION_PATTERN_SHAPE").as_deref() == Ok("1")
}

/// Static name for the subject type, or `None` when the type is one this check
/// deliberately stays silent about.
fn never_option_type_name(ty: &HirType) -> Option<&'static str> {
    match ty {
        HirType::Int { .. } => Some("int"),
        HirType::Float { .. } => Some("float"),
        HirType::Bool => Some("bool"),
        HirType::Char => Some("char"),
        HirType::String => Some("text"),
        // Everything else is either a legitimate Option carrier
        // (`Pointer` == `T?`, `Enum` == a real Option/Result or a user enum),
        // or too weakly typed to judge (`Any`, `Unknown`, generics), or an
        // aggregate whose nullable form has not been measured. Stay silent.
        _ => None,
    }
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
/// type can never be one. Warn-only and default off; see the module docs.
///
/// `subject_ty` is the resolved `HirType` of the scrutinee, or `None` when the
/// lowerer could not resolve it (in which case nothing is reported).
pub(crate) fn report_if_never_option(
    variant: &str,
    subject_ty: Option<&HirType>,
    form: &str,
    location: DiagLocation<'_>,
) {
    if !matches!(variant, "Some" | "None" | "Ok" | "Err") {
        return;
    }
    if !gate_on() {
        return;
    }
    let Some(ty) = subject_ty else { return };
    let Some(kind) = never_option_type_name(ty) else {
        return;
    };
    let at = location.render();
    eprintln!(
        "warning[option-pattern-shape]: {at}: `{variant}(...)` pattern ({form}) tested against a \
         scrutinee statically typed `{kind}`, which is never an Option/Result; this pattern \
         can never legitimately match and the default (JIT) engine answers it silently by \
         taking the arm and binding a corrupt value"
    );
}
