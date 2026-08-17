use simple_parser::Span;
use thiserror::Error;

use super::super::lifetime::LifetimeViolation;
use super::super::types::TypeId;
use super::memory_warning::{MemoryWarningCode, MemoryWarningCollector};

/// Render the declared-field hint for `CannotInferFieldType`.
///
/// Returns the empty string when nothing is known, so the field-ACCESS path
/// (which never populates `available_fields`) keeps its historical message.
fn fmt_available_fields(available_fields: &[String]) -> String {
    if available_fields.is_empty() {
        String::new()
    } else {
        format!(" (declared fields: {})", available_fields.join(", "))
    }
}

#[derive(Error, Debug)]
pub enum LowerError {
    #[error("Unknown type: {type_name}")]
    UnknownType {
        type_name: String,
        /// Available type names for suggestions
        available_types: Vec<String>,
    },

    #[error("Unknown variable: {0}")]
    UnknownVariable(String),

    /// E1032: self used in static method
    #[error("cannot use `self` in static method")]
    SelfInStatic,

    /// E1016: let binding failed - complex pattern not supported
    #[error("let binding failed: {pattern} - complex patterns are not yet supported in let bindings")]
    LetBindingFailed { pattern: String },

    #[error("Type mismatch: expected {expected:?}, found {found:?}")]
    TypeMismatch { expected: TypeId, found: TypeId },

    #[error("Cannot infer type")]
    CannotInferType,

    #[error("Cannot infer type: {0}")]
    CannotInferTypeFor(String),

    #[error("Parameter '{param}' in function '{function}' requires explicit type annotation")]
    MissingParameterType { param: String, function: String },

    #[error("Cannot infer element type of empty array - use explicit annotation")]
    EmptyArrayNeedsType,

    // The `available_fields` tail is what makes this diagnosable: when the error
    // comes from a struct LITERAL naming a field the declaration does not have
    // (hir/lower/expr/collections.rs), the declared set is known and printing it
    // turns an unlocatable fleet-wide JIT de-optimisation into an obvious typo
    // report. Empty vec (field-ACCESS path) prints nothing, preserving the old
    // message byte-for-byte. See
    // doc/08_tracking/bug/test_runner_jit_fallback_functionoutline_type_params_2026-08-17.md
    #[error(
        "Cannot infer field type: struct '{struct_name}' field '{field}'{}",
        fmt_available_fields(available_fields)
    )]
    CannotInferFieldType {
        struct_name: String,
        field: String,
        /// Available field names for suggestions
        available_fields: Vec<String>,
    },

    #[error("Cannot infer element type for index into '{0}'")]
    CannotInferIndexType(String),

    #[error("Cannot infer deref type for '{0}'")]
    CannotInferDerefType(String),

    #[error("Unsupported feature: {0}")]
    Unsupported(String),

    /// E1050: Use Python-style constructor instead of .new()
    #[error("Use Python-style constructor `{class_name}(...)` instead of `{class_name}.new(...)`")]
    UseConstructorNotNew { class_name: String },

    /// E1052: Attempted to mutate self in an immutable fn method
    #[error(
        "cannot modify self in immutable fn method '{func_name}'. Use `me` instead of `fn` to allow self mutation"
    )]
    SelfMutationInImmutableMethod { func_name: String },

    /// A bare `field = value` (no `self.`) inside a method body, where `field`
    /// is a declared field of the receiver's class. Without this the HIR
    /// lowering minted a *fresh local* that shadows the field, so the write was
    /// silently discarded and `self.field` kept its old value — the JIT half of
    /// doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md.
    /// The AST interpreter already rejects this shape
    /// (interpreter/node_exec.rs); this variant makes the lowering-based
    /// engines (Cranelift JIT, LLVM/native) agree instead of losing the write.
    /// Wording is deliberately kept in lockstep with the interpreter's message.
    #[error(
        "invalid assignment: `{field}` is a field of `{class}`; a bare `{field} = ...` creates a new local and leaves `self.{field}` unchanged. Write `self.{field} = ...` to assign the field; `self` is implicit only in the parameter list, not in field access"
    )]
    ImplicitSelfFieldAssignment { field: String, class: String },

    /// CTR-032: Impure function call in contract expression
    #[error(
        "Impure function call '{func_name}' in contract expression. Only #[pure] functions can be called in contracts"
    )]
    ImpureFunctionInContract { func_name: String },

    /// CTR-060-062: Non-snapshot-safe type in old() expression
    #[error(
        "Type is not snapshot-safe for old() expression. Only primitives, enums, and immutable structs can be captured"
    )]
    NotSnapshotSafe,

    /// Capability error (aliasing, conversion, mode compatibility)
    #[error("Capability error: {0}")]
    Capability(#[from] super::super::capability::CapabilityError),

    /// Module resolution error (cannot find or load imported module)
    #[error("Module resolution error: {0}")]
    ModuleResolution(String),

    /// Lifetime violation errors (E2001-E2006)
    #[error("{}", .0.description())]
    LifetimeViolation(LifetimeViolation),

    /// Multiple lifetime violations
    #[error("Multiple lifetime violations detected ({} errors)", .0.len())]
    LifetimeViolations(Vec<LifetimeViolation>),

    /// Memory safety violation (strict mode - Rust-level safety)
    /// W1001-W1006 become compile errors in strict mode
    #[error("Memory safety error [{code}]: {message}")]
    MemorySafetyViolation {
        /// The warning code that became an error
        code: MemoryWarningCode,
        /// Human-readable error message
        message: String,
        /// Source location
        span: Span,
        /// All collected warnings (for detailed diagnostics)
        all_warnings: MemoryWarningCollector,
    },
}

pub type LowerResult<T> = Result<T, LowerError>;
