//! Effect and capability declarations for the Simple language.
//!
//! Effects are compile-time markers indicating what side effects a function may have.
//! Capabilities are module-level restrictions on what effects are allowed.

/// Effect marker for function side effects
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    /// Non-blocking guarantee - cannot call blocking operations
    Async,
    /// No side effects - cannot do I/O, network, filesystem, or GC allocation
    Pure,
    /// I/O operations allowed (console, general I/O)
    Io,
    /// Network operations allowed (HTTP, TCP, UDP)
    Net,
    /// Filesystem operations allowed (read/write files, directories)
    Fs,
    /// Unsafe/unchecked operations allowed (raw pointers, FFI)
    Unsafe,
    /// Verification mode - enables Lean proof generation and verification constraints
    /// Code marked @verify must follow the verified subset (no unsafe, no reflection, etc.)
    Verify,
    /// Trusted boundary - marks interface between verified and unverified code
    /// Must prove calling code satisfies contracts before crossing boundary
    Trusted,
    /// Ghost declaration - exists only for verification, erased at runtime
    /// Ghost functions/classes are included in Lean output but not in compiled code
    Ghost,
    /// Auto-generate Lean scaffolding (structures, lookups, BEq, theorems)
    /// Mode: full (default) - generates all scaffolding
    /// Mode: structure_only - only generates structure/inductive definitions
    /// Mode: skip - excludes from generation
    AutoLean(AutoLeanMode),
}

/// Mode for @auto_lean attribute controlling what gets generated
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum AutoLeanMode {
    /// Full auto-generation: structure + lookups + BEq + reflexivity theorems
    #[default]
    Full,
    /// Only generate structure/inductive definitions
    StructureOnly,
    /// Skip this item from Lean generation
    Skip,
    /// Generate determinism theorems for Option-returning functions
    Determinism,
}

impl Effect {
    /// Parse an effect from a decorator name.
    /// Returns None if the name is not a recognized effect.
    pub fn from_decorator_name(name: &str) -> Option<Self> {
        match name {
            "async" => Some(Effect::Async),
            "pure" => Some(Effect::Pure),
            "io" => Some(Effect::Io),
            "net" => Some(Effect::Net),
            "fs" => Some(Effect::Fs),
            "unsafe" => Some(Effect::Unsafe),
            "verify" => Some(Effect::Verify),
            "trusted" => Some(Effect::Trusted),
            "ghost" => Some(Effect::Ghost),
            "auto_lean" => Some(Effect::AutoLean(AutoLeanMode::Full)),
            _ => None,
        }
    }

    /// Parse an effect from a decorator name with an optional argument.
    /// For @auto_lean(mode), parses the mode argument.
    pub fn from_decorator_name_with_arg(name: &str, arg: Option<&str>) -> Option<Self> {
        match name {
            "auto_lean" => {
                let mode = match arg {
                    Some("full") | None => AutoLeanMode::Full,
                    Some("structure_only") => AutoLeanMode::StructureOnly,
                    Some("skip") => AutoLeanMode::Skip,
                    Some("determinism") => AutoLeanMode::Determinism,
                    _ => return None,
                };
                Some(Effect::AutoLean(mode))
            }
            _ => Self::from_decorator_name(name),
        }
    }

    /// Get the decorator name for this effect.
    pub fn decorator_name(&self) -> &'static str {
        match self {
            Effect::Async => "async",
            Effect::Pure => "pure",
            Effect::Io => "io",
            Effect::Net => "net",
            Effect::Fs => "fs",
            Effect::Unsafe => "unsafe",
            Effect::Verify => "verify",
            Effect::Trusted => "trusted",
            Effect::Ghost => "ghost",
            Effect::AutoLean(_) => "auto_lean",
        }
    }

    /// Check if this is a verification-related effect.
    pub fn is_verification(&self) -> bool {
        matches!(
            self,
            Effect::Verify | Effect::Trusted | Effect::Ghost | Effect::AutoLean(_)
        )
    }

    /// Get the auto_lean mode if this is an AutoLean effect.
    pub fn auto_lean_mode(&self) -> Option<AutoLeanMode> {
        match self {
            Effect::AutoLean(mode) => Some(*mode),
            _ => None,
        }
    }
}

impl AutoLeanMode {
    /// Parse mode from string argument.
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "full" => Some(AutoLeanMode::Full),
            "structure_only" => Some(AutoLeanMode::StructureOnly),
            "skip" => Some(AutoLeanMode::Skip),
            "determinism" => Some(AutoLeanMode::Determinism),
            _ => None,
        }
    }

    /// Get the string representation of this mode.
    pub fn as_str(&self) -> &'static str {
        match self {
            AutoLeanMode::Full => "full",
            AutoLeanMode::StructureOnly => "structure_only",
            AutoLeanMode::Skip => "skip",
            AutoLeanMode::Determinism => "determinism",
        }
    }

    /// Check if this mode generates structures.
    pub fn generates_structures(&self) -> bool {
        matches!(self, AutoLeanMode::Full | AutoLeanMode::StructureOnly)
    }

    /// Check if this mode generates lookups.
    pub fn generates_lookups(&self) -> bool {
        matches!(self, AutoLeanMode::Full)
    }

    /// Check if this mode generates BEq instances.
    pub fn generates_beq(&self) -> bool {
        matches!(self, AutoLeanMode::Full)
    }

    /// Check if this mode generates theorems.
    pub fn generates_theorems(&self) -> bool {
        matches!(self, AutoLeanMode::Full | AutoLeanMode::Determinism)
    }
}

/// Module capability declarations for restricting what effects are allowed.
///
/// Capabilities are declared at the module level in `__init__.spl` files
/// using the `requires [cap1, cap2]` syntax. A module can only define
/// functions with effects that are subsets of its declared capabilities.
///
/// Example:
/// ```simple
/// # In __init__.spl
/// requires [pure, io]
///
/// # This module can only contain @pure and @io functions
/// # @net or @fs functions would be compile errors
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Capability {
    /// Pure computation only - no side effects
    Pure,
    /// I/O operations (console, general I/O)
    Io,
    /// Network operations (HTTP, TCP, UDP)
    Net,
    /// Filesystem operations (read/write files, directories)
    Fs,
    /// Unsafe/unchecked operations (raw pointers, FFI)
    Unsafe,
    /// Garbage collection allowed
    Gc,
}

impl Capability {
    /// Parse a capability from its name.
    /// Returns None if the name is not a recognized capability.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "pure" => Some(Capability::Pure),
            "io" => Some(Capability::Io),
            "net" => Some(Capability::Net),
            "fs" => Some(Capability::Fs),
            "unsafe" => Some(Capability::Unsafe),
            "gc" => Some(Capability::Gc),
            _ => None,
        }
    }

    /// Get the name of this capability.
    pub fn name(&self) -> &'static str {
        match self {
            Capability::Pure => "pure",
            Capability::Io => "io",
            Capability::Net => "net",
            Capability::Fs => "fs",
            Capability::Unsafe => "unsafe",
            Capability::Gc => "gc",
        }
    }

    /// Convert an Effect to its corresponding Capability (if applicable).
    /// Note: Async is not a capability since it's about execution model, not permissions.
    /// Note: Verify and Trusted are verification mode markers, not capabilities.
    pub fn from_effect(effect: &Effect) -> Option<Self> {
        match effect {
            Effect::Pure => Some(Capability::Pure),
            Effect::Io => Some(Capability::Io),
            Effect::Net => Some(Capability::Net),
            Effect::Fs => Some(Capability::Fs),
            Effect::Unsafe => Some(Capability::Unsafe),
            Effect::Async => None,       // Async is execution model, not capability
            Effect::Verify => None,      // Verify is verification mode marker
            Effect::Trusted => None,     // Trusted is verification boundary marker
            Effect::Ghost => None,       // Ghost is verification-only marker
            Effect::AutoLean(_) => None, // AutoLean is Lean code generation marker
        }
    }
}
