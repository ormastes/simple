//! Common backend infrastructure for both AOT and JIT compilation.
//!
//! This module provides a generic `CodegenBackend<M: Module>` that handles
//! shared functionality between AOT (ObjectModule) and JIT (JITModule) backends.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{Arc, LazyLock, Mutex};

use cranelift_codegen::ir::{types, InstBuilder, UserFuncName};
use cranelift_codegen::isa::{CallConv, OwnedTargetIsa};
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_codegen::Context;
use cranelift_module::{Linkage, Module};
use target_lexicon::Triple;
use thiserror::Error;

use simple_common::target::{Target, TargetArch, TargetCpu};

use crate::hir::TypeId;
use crate::mir::{MirFunction, MirInst, MirModule};

use super::instr::compile_function_body;
use super::mir_inline::inline_small_pure_functions;
use super::runtime_sffi::runtime_funcs_for_target;
use super::shared::{build_mir_signature, create_body_stub, expand_with_outlined};

/// Common error type for codegen backends
#[derive(Error, Debug)]
pub enum BackendError {
    #[error("Compilation error: {0}")]
    Compilation(String),

    #[error("Unsupported type: {0:?}")]
    UnsupportedType(TypeId),

    #[error("Unknown function: {0}")]
    UnknownFunction(String),

    #[error("Module error: {0}")]
    ModuleError(String),

    #[error("Unsupported target architecture: {0}")]
    UnsupportedTarget(String),
}

pub type BackendResult<T> = Result<T, BackendError>;

pub(crate) fn referenced_call_names(functions: &[MirFunction]) -> HashSet<String> {
    let mut names = HashSet::new();
    for func in functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                match inst {
                    MirInst::Call { target, .. } => {
                        let raw = target.name();
                        names.insert(raw.to_string());
                        // Also declare the canonical alias target so that the
                        // runtime_funcs.get(sffi_name) branch in compile_call
                        // fires (with proper text-arg expansion) instead of
                        // falling through to the cross-module path.
                        // e.g., "rt_file_delete" → also insert "rt_file_remove"
                        let base = raw.rsplit_once("__").map(|(_, t)| t).unwrap_or(raw);
                        if let Some(alias) = super::instr::calls::sffi_alias_target(base) {
                            names.insert(alias.to_string());
                        }
                    }
                    MirInst::InterpCall { func_name, .. } => {
                        names.insert(func_name.clone());
                    }
                    MirInst::DictLit { .. } => {
                        names.insert("rt_dict_new".to_string());
                        names.insert("rt_dict_set".to_string());
                    }
                    MirInst::IndexGet { .. } => {
                        names.insert("rt_index_get".to_string());
                    }
                    MirInst::IndexSet { .. } => {
                        names.insert("rt_index_set".to_string());
                    }
                    MirInst::SliceOp { .. } => {
                        names.insert("rt_slice".to_string());
                    }
                    MirInst::ActorSpawn { .. } => {
                        names.insert("rt_actor_spawn".to_string());
                    }
                    MirInst::ActorSend { .. } => {
                        names.insert("rt_actor_send".to_string());
                    }
                    MirInst::ActorJoin { .. } => {
                        names.insert("rt_actor_join".to_string());
                    }
                    MirInst::ActorReply { .. } => {
                        names.insert("rt_actor_reply".to_string());
                    }
                    MirInst::FutureCreate { .. } => {
                        names.insert("rt_future_new".to_string());
                    }
                    MirInst::Await { .. } => {
                        names.insert("rt_future_await".to_string());
                    }
                    MirInst::GeneratorCreate { .. } => {
                        names.insert("rt_generator_new".to_string());
                    }
                    MirInst::GeneratorNext { .. } => {
                        names.insert("rt_generator_next".to_string());
                        names.insert("rt_value_as_int".to_string());
                    }
                    MirInst::Yield { .. } => {
                        names.insert("rt_generator_set_state".to_string());
                        names.insert("rt_value_int".to_string());
                    }
                    MirInst::Wait { .. } => {
                        names.insert("rt_wait".to_string());
                    }
                    _ => {}
                }
            }
        }
    }
    names
}

pub(crate) fn runtime_symbol_is_codegen_root(name: &str) -> bool {
    matches!(
        name,
        "__simple_runtime_init"
            | "__simple_runtime_shutdown"
            | "rt_set_args"
            | "rt_function_not_found"
            | "rt_string_new"
            | "rt_string_data"
            | "rt_string_len"
            | "rt_print_str"
            | "rt_println_str"
            | "rt_eprint_str"
            | "rt_eprintln_str"
            | "rt_print_value"
            | "rt_println_value"
            | "rt_eprint_value"
            | "rt_eprintln_value"
            | "rt_contains"
            | "rt_len"
            | "rt_slice"
            | "rt_alloc"
            | "rt_array_new"
            | "rt_byte_array_new"
            | "rt_array_len"
            | "rt_array_get"
            | "rt_array_get_text"
            | "rt_array_data_ptr_text"
            | "rt_array_data_ptr_u8"
            | "rt_array_set_text"
            | "rt_array_set_len_known_text"
            | "rt_array_push"
            | "rt_typed_bytes_u8_push"
            | "rt_tuple_new"
            | "rt_tuple_set"
            | "rt_enum_new"
            | "rt_string_eq"
            | "rt_hash_text"
            | "rt_value_bool"
            | "rt_interp_call"
            | "rt_native_eq"
            | "rt_native_neq"
    )
}

/// Common codegen backend that works with any Cranelift Module type.
///
/// This struct contains all shared state and logic between AOT and JIT backends.
pub struct CodegenBackend<M: Module> {
    pub module: M,
    pub ctx: Context,
    pub func_ids: BTreeMap<String, cranelift_module::FuncId>,
    pub runtime_funcs: HashMap<&'static str, cranelift_module::FuncId>,
    pub global_ids: BTreeMap<String, cranelift_module::DataId>,
    pub body_stub: Option<cranelift_module::FuncId>,
    pub target: Target,
    /// Optional module prefix for name mangling (e.g., "compiler__frontend__core__lexer").
    /// When set, local function declarations are mangled as `prefix__name` to prevent
    /// symbol collisions in multi-file native builds. Raw names are also registered in
    /// func_ids so that intra-module calls by raw name still resolve locally.
    pub module_prefix: Option<String>,
    /// Whether this module contains the program entry point.
    /// When true, `main` is emitted as `spl_main` with Preemptible linkage so the
    /// C runtime entry stub can find it. When false, `main` is mangled like any
    /// other local function to avoid symbol collisions.
    pub is_entry_module: bool,
    /// Import map: raw function name → mangled name for cross-module resolution.
    /// Built during the discovery phase of multi-file native builds.
    pub import_map: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Set of function names that have multiple definitions across modules.
    /// These names keep their raw (unmangled) symbol name to avoid breaking
    /// cross-module resolution when the import map can't disambiguate.
    pub ambiguous_names: std::sync::Arc<std::collections::HashSet<String>>,
    /// Per-module use map: local imported name → mangled name.
    /// Built from the current file's `use` statements. Used to resolve
    /// ambiguous cross-module imports that the global import map can't handle.
    pub use_map: std::collections::HashMap<String, String>,
    /// Set of mangled names that correspond to module-level data (val/var/
    /// const/static) rather than functions. When a cross-module imported
    /// global name resolves (via use_map/import_map) to a member of this set,
    /// `declare_globals` skips the function-import fast path and declares it
    /// as a data import instead. Without this, imported `val K: u32 = 1`
    /// style constants get registered as function imports and `GlobalLoad`
    /// returns the symbol's address instead of its value.
    pub data_exports: std::sync::Arc<std::collections::HashSet<String>>,
    /// Mangled function name → declared parameter count for cross-module free
    /// functions. Used to strip spurious nil receivers from module-qualified calls.
    pub fn_arities: std::sync::Arc<std::collections::HashMap<String, usize>>,
    /// Vtable data object IDs: struct_name -> DataId for each trait-impl struct.
    /// Used by compile_struct_init to write vtable_ptr at offset 0.
    pub vtable_data_ids: BTreeMap<String, cranelift_module::DataId>,
    /// Vtable data object IDs by TypeId (HIR TypeId -> DataId).
    /// Used by MirInst::StructInit dispatch which has type_id, not struct_name.
    pub vtable_type_ids: BTreeMap<crate::hir::TypeId, cranelift_module::DataId>,
}

/// Toggle individual ISA extensions on or off.
/// `None` = use Cranelift default (detect from host CPU or target CPU profile).
///
/// # Notes on flag availability
/// - Tokens `neon`, `sve`, `sve2`, `sse2` are accepted by the parser but are
///   **no-ops** at the Cranelift level: Cranelift's aarch64 backend exposes only
///   `has_lse`, `has_pauth`, and `has_fp16`; it has no NEON/SVE toggles. SSE2
///   is also an unconditional x86_64 baseline with no Cranelift flag. Toggles
///   that actually take effect are the x86 ones from `has_sse3` onward, plus
///   `has_lse`/`has_pauth`/`has_fp16` on aarch64.
/// - Unknown tokens generate a warning to stderr and are silently ignored.
#[derive(Debug, Clone, Default)]
pub struct CpuFeatureConfig {
    pub neon: Option<bool>, // aarch64 — accepted but no-op (no Cranelift flag)
    pub sve: Option<bool>,  // aarch64 — accepted but no-op
    pub sve2: Option<bool>, // aarch64 — accepted but no-op
    pub sse2: Option<bool>, // x86_64  — accepted but no-op (unconditional baseline)
    pub sse3: Option<bool>,
    pub ssse3: Option<bool>,
    pub sse41: Option<bool>,
    pub sse42: Option<bool>,
    pub avx: Option<bool>,
    pub avx2: Option<bool>,
    pub avx512f: Option<bool>,
    pub avx512vl: Option<bool>,
    pub bmi1: Option<bool>,
    pub bmi2: Option<bool>,
    pub fma: Option<bool>,
    pub lzcnt: Option<bool>,
    pub popcnt: Option<bool>,
}

impl CpuFeatureConfig {
    /// Parse from an environment string like `+neon,-sve2,+avx2,-avx512f`
    /// (`+` = enable, `-` = disable, bare name = enable, comma-separated).
    /// Unknown tokens are logged to stderr and silently ignored.
    pub fn from_env_string(s: &str) -> Self {
        let mut out = Self::default();
        for token in s.split(',') {
            let token = token.trim();
            if token.is_empty() {
                continue;
            }
            let (op, name) = match token.chars().next() {
                Some('+') => (Some(true), &token[1..]),
                Some('-') => (Some(false), &token[1..]),
                _ => (Some(true), token), // bare name = enable
            };
            match name {
                "neon" => out.neon = op,
                "sve" => out.sve = op,
                "sve2" => out.sve2 = op,
                "sse2" => out.sse2 = op,
                "sse3" => out.sse3 = op,
                "ssse3" => out.ssse3 = op,
                "sse41" => out.sse41 = op,
                "sse42" => out.sse42 = op,
                "avx" => out.avx = op,
                "avx2" => out.avx2 = op,
                "avx512f" => out.avx512f = op,
                "avx512vl" => out.avx512vl = op,
                "bmi1" => out.bmi1 = op,
                "bmi2" => out.bmi2 = op,
                "fma" => out.fma = op,
                "lzcnt" => out.lzcnt = op,
                "popcnt" => out.popcnt = op,
                _ => eprintln!("simple: unknown cpu feature token '{}' ignored", name),
            }
        }
        out
    }

    /// Read from the `SIMPLE_CPU_FEATURES` environment variable.
    /// Unset or empty string = all defaults.
    pub fn from_env() -> Self {
        match std::env::var("SIMPLE_CPU_FEATURES") {
            Ok(s) if !s.is_empty() => Self::from_env_string(&s),
            _ => Self::default(),
        }
    }
}

/// Apply `CpuFeatureConfig` overrides to a Cranelift ISA builder.
///
/// Called AFTER `apply_cranelift_cpu_policy` so per-level presets (x86-64-v2/v3/v4)
/// are applied first, then env overrides can selectively enable or disable individual
/// features (e.g. `--cpu x86-64-v3` + `SIMPLE_CPU_FEATURES=-avx512f`).
///
/// Flags that the target ISA does not recognise are silently ignored — Cranelift
/// returns an error for unknown flag names, which we swallow here.
fn apply_feature_overrides(isa_builder: &mut dyn cranelift_codegen::settings::Configurable, cfg: &CpuFeatureConfig) {
    let mut set = |key: &str, val: bool| {
        // Ignore errors: unknown flags are silently no-op across ISAs.
        let _ = isa_builder.set(key, if val { "true" } else { "false" });
    };
    // x86_64 flags (no-op on other ISAs):
    if let Some(v) = cfg.sse3 {
        set("has_sse3", v);
    }
    if let Some(v) = cfg.ssse3 {
        set("has_ssse3", v);
    }
    if let Some(v) = cfg.sse41 {
        set("has_sse41", v);
    }
    if let Some(v) = cfg.sse42 {
        set("has_sse42", v);
    }
    if let Some(v) = cfg.avx {
        set("has_avx", v);
    }
    if let Some(v) = cfg.avx2 {
        set("has_avx2", v);
    }
    if let Some(v) = cfg.avx512f {
        set("has_avx512f", v);
    }
    if let Some(v) = cfg.avx512vl {
        set("has_avx512vl", v);
    }
    if let Some(v) = cfg.bmi1 {
        set("has_bmi1", v);
    }
    if let Some(v) = cfg.bmi2 {
        set("has_bmi2", v);
    }
    if let Some(v) = cfg.fma {
        set("has_fma", v);
    }
    if let Some(v) = cfg.lzcnt {
        set("has_lzcnt", v);
    }
    if let Some(v) = cfg.popcnt {
        set("has_popcnt", v);
    }
    // aarch64 flags (no-op on other ISAs — neon/sve have no Cranelift flag):
    // has_lse and has_pauth are the real aarch64 toggles but are not yet in the
    // CpuFeatureConfig token set; neon/sve are parsed but produce no set() call.
}

/// Settings for creating a codegen backend
#[derive(Debug, Clone)]
pub struct BackendSettings {
    pub opt_level: &'static str,
    pub is_pic: bool,
    pub target: Target,
    pub cpu: TargetCpu,
    /// Per-feature override config. Defaults to all-None (use Cranelift defaults).
    /// Populated from `SIMPLE_CPU_FEATURES` env var when calling `aot()`, `jit()`,
    /// or `aot_for_target()`.
    pub cpu_features: CpuFeatureConfig,
}

impl Default for BackendSettings {
    fn default() -> Self {
        Self {
            opt_level: "speed",
            is_pic: false,
            target: Target::host(),
            cpu: TargetCpu::builtin_default_for_arch(Target::host().arch),
            cpu_features: CpuFeatureConfig::default(),
        }
    }
}

impl BackendSettings {
    /// Settings for AOT compilation (host target)
    pub fn aot() -> Self {
        Self {
            opt_level: "speed",
            // Enable PIC for compatibility with PIE executables and shared libraries
            is_pic: true,
            target: Target::host(),
            cpu: TargetCpu::builtin_default_for_arch(Target::host().arch),
            cpu_features: CpuFeatureConfig::from_env(),
        }
    }

    /// Settings for AOT compilation with a specific target
    pub fn aot_for_target(target: Target) -> Self {
        Self {
            opt_level: "speed",
            // Enable PIC for hosted targets (PIE executables, shared libraries).
            // Disable PIC for baremetal/freestanding targets — no GOT, no dynamic linker.
            is_pic: !target.is_baremetal(),
            target,
            cpu: TargetCpu::builtin_default_for_arch(target.arch),
            cpu_features: CpuFeatureConfig::from_env(),
        }
    }

    /// Settings for JIT compilation (always host target).
    ///
    /// PLT entries (required when `is_pic=true`) are only implemented for x86_64
    /// in cranelift-jit (`vendor/cranelift-jit/src/backend.rs:297`).
    /// On aarch64, riscv64, and other non-x86_64 hosts the PLT write path
    /// asserts and panics, so we disable PIC there.  The AOT path
    /// (`BackendSettings::aot_for_target`) is unaffected — it uses
    /// `ObjectModule`, not `JITModule`, and never touches the PLT writer.
    pub fn jit() -> Self {
        // PLT entries needed by is_pic=true are only implemented for x86_64
        // in cranelift-jit (vendor/cranelift-jit/src/backend.rs:297).
        // On aarch64/riscv/etc., disable PIC so the assert never fires.
        let is_pic = cfg!(target_arch = "x86_64");
        Self {
            opt_level: "speed",
            is_pic,
            target: Target::host(),
            cpu: TargetCpu::builtin_default_for_arch(Target::host().arch),
            cpu_features: CpuFeatureConfig::from_env(),
        }
    }

    /// Set the target architecture
    pub fn with_target(mut self, target: Target) -> Self {
        self.target = target;
        self
    }

    /// Set the optimization level
    pub fn with_opt_level(mut self, level: &'static str) -> Self {
        self.opt_level = level;
        self
    }

    pub fn with_cpu(mut self, cpu: TargetCpu) -> Self {
        self.cpu = cpu;
        self
    }

    /// Override the CPU feature config (replaces what `from_env()` set).
    pub fn with_cpu_features(mut self, features: CpuFeatureConfig) -> Self {
        self.cpu_features = features;
        self
    }
}

/// Convert TargetArch to target_lexicon::Triple
fn target_arch_to_triple(arch: TargetArch) -> BackendResult<Triple> {
    let triple_str = arch.triple_str();
    triple_str
        .parse()
        .map_err(|e: target_lexicon::ParseError| BackendError::UnsupportedTarget(e.to_string()))
}

/// Cache key for ISA instances: stringified from all discriminating `BackendSettings` fields.
type IsaCacheKey = (
    Target,       // target (Hash+Eq)
    TargetCpu,    // cpu    (Hash+Eq)
    &'static str, // opt_level
    bool,         // is_pic
    String,       // cpu_features — Debug-stringified (no Hash impl)
);

/// Process-wide ISA cache. ISA construction (especially `cranelift_native::builder_with_options`
/// + CPUID inference) is expensive and the result is immutable within a process.
/// `Arc<dyn TargetIsa>` is `Send + Sync`, so sharing across threads is safe.
static ISA_CACHE: LazyLock<Mutex<HashMap<IsaCacheKey, (Flags, Arc<dyn cranelift_codegen::isa::TargetIsa>)>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Create ISA and flags from settings, caching by (target, cpu, opt_level, is_pic, cpu_features).
pub fn create_isa_and_flags(
    settings: &BackendSettings,
) -> BackendResult<(Flags, std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>)> {
    let cache_key: IsaCacheKey = (
        settings.target,
        settings.cpu.clone(),
        settings.opt_level,
        settings.is_pic,
        format!("{:?}", settings.cpu_features),
    );

    // Fast path: return cached ISA.
    {
        let guard = ISA_CACHE.lock().unwrap();
        if let Some((flags, isa)) = guard.get(&cache_key) {
            return Ok((flags.clone(), Arc::clone(isa)));
        }
    }

    // Slow path: build ISA, then cache it.
    let mut settings_builder = settings::builder();
    settings_builder
        .set("opt_level", settings.opt_level)
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    if settings.is_pic {
        settings_builder
            .set("is_pic", "true")
            .map_err(|e| BackendError::Compilation(e.to_string()))?;
    }

    let flags = Flags::new(settings_builder);

    let triple: Triple = if settings.target.is_host() {
        Triple::host()
    } else {
        settings
            .target
            .triple_str()
            .parse()
            .map_err(|e: target_lexicon::ParseError| BackendError::UnsupportedTarget(e.to_string()))?
    };

    let (flags, isa) =
        create_isa_from_settings(triple, flags, &settings.target, &settings.cpu, &settings.cpu_features)?;

    {
        let mut guard = ISA_CACHE.lock().unwrap();
        guard
            .entry(cache_key)
            .or_insert_with(|| (flags.clone(), Arc::clone(&isa)));
    }

    Ok((flags, isa))
}

/// Helper to create ISA from a triple
fn create_isa_from_triple(
    triple: Triple,
    flags: settings::Flags,
) -> Result<(settings::Flags, OwnedTargetIsa), BackendError> {
    let isa = cranelift_codegen::isa::lookup(triple)
        .map_err(|e| BackendError::Compilation(e.to_string()))?
        .finish(flags.clone())
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    Ok((flags, isa))
}

fn create_isa_from_settings(
    triple: Triple,
    flags: settings::Flags,
    target: &Target,
    cpu: &TargetCpu,
    cpu_features: &CpuFeatureConfig,
) -> Result<(settings::Flags, OwnedTargetIsa), BackendError> {
    if matches!(target.arch, TargetArch::Arm | TargetArch::Riscv32) {
        return Err(BackendError::UnsupportedTarget(format!(
            "Cranelift native builds do not support hosted {} yet; use --backend llvm for this lane",
            target.arch
        )));
    }

    let mut isa_builder = if target.is_host() && matches!(cpu, TargetCpu::Native) {
        cranelift_native::builder_with_options(true).map_err(|e| BackendError::Compilation(e.to_string()))?
    } else {
        cranelift_codegen::isa::lookup(triple).map_err(|e| BackendError::Compilation(e.to_string()))?
    };

    // Apply CPU-level presets first (e.g. x86-64-v3 enables avx2, bmi1, etc.)
    apply_cranelift_cpu_policy(&mut isa_builder, target, cpu)?;
    // Then apply per-feature env overrides so users can selectively enable/disable
    // individual features on top of the preset (e.g. --cpu x86-64-v3 + -avx512f).
    apply_feature_overrides(&mut isa_builder, cpu_features);

    let isa = isa_builder
        .finish(flags.clone())
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    Ok((flags, isa))
}

fn apply_cranelift_cpu_policy(
    isa_builder: &mut dyn cranelift_codegen::settings::Configurable,
    target: &Target,
    cpu: &TargetCpu,
) -> BackendResult<()> {
    match cpu {
        TargetCpu::Default => Ok(()),
        TargetCpu::Native => {
            if target.is_host() {
                cranelift_native::infer_native_flags(isa_builder).map_err(|e| BackendError::Compilation(e.to_string()))
            } else {
                Err(BackendError::Compilation(format!(
                    "Cranelift backend cannot use --cpu native when targeting {}; native only works for host builds",
                    target
                )))
            }
        }
        TargetCpu::X86_64V1 | TargetCpu::X86_64V2 | TargetCpu::X86_64V3 | TargetCpu::X86_64V4 => {
            if target.arch != TargetArch::X86_64 {
                return Err(BackendError::Compilation(format!(
                    "CPU level {} only applies to x86_64 targets, not {}",
                    cpu, target.arch
                )));
            }
            enable_x86_64_level(isa_builder, cpu)
        }
        TargetCpu::Custom(value) => Err(BackendError::Compilation(format!(
            "Cranelift backend does not accept free-form CPU '{}'; use default, native, or x86-64-v1..v4",
            value
        ))),
    }
}

fn enable_x86_64_level(
    isa_builder: &mut dyn cranelift_codegen::settings::Configurable,
    cpu: &TargetCpu,
) -> BackendResult<()> {
    let enable = |name: &str, builder: &mut dyn cranelift_codegen::settings::Configurable| {
        builder
            .enable(name)
            .map_err(|e| BackendError::Compilation(format!("failed to enable Cranelift feature {name}: {e}")))
    };

    match cpu {
        TargetCpu::X86_64V1 => {}
        TargetCpu::X86_64V2 => {
            for feature in [
                "has_cmpxchg16b",
                "has_sse3",
                "has_ssse3",
                "has_sse41",
                "has_sse42",
                "has_popcnt",
            ] {
                enable(feature, isa_builder)?;
            }
        }
        TargetCpu::X86_64V3 => {
            for feature in [
                "has_cmpxchg16b",
                "has_sse3",
                "has_ssse3",
                "has_sse41",
                "has_sse42",
                "has_popcnt",
                "has_avx",
                "has_avx2",
                "has_fma",
                "has_bmi1",
                "has_bmi2",
                "has_lzcnt",
            ] {
                enable(feature, isa_builder)?;
            }
        }
        TargetCpu::X86_64V4 => {
            enable_x86_64_level(isa_builder, &TargetCpu::X86_64V3)?;
            for feature in [
                "has_avx512f",
                "has_avx512dq",
                "has_avx512vl",
                "has_avx512vbmi",
                "has_avx512bitalg",
            ] {
                enable(feature, isa_builder)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Create ISA and flags for the host target (backwards compatibility)
pub fn create_host_isa_and_flags(
    opt_level: &str,
    is_pic: bool,
) -> BackendResult<(Flags, std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>)> {
    let mut settings_builder = settings::builder();
    settings_builder
        .set("opt_level", opt_level)
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    if is_pic {
        settings_builder
            .set("is_pic", "true")
            .map_err(|e| BackendError::Compilation(e.to_string()))?;
    }

    let flags = Flags::new(settings_builder);
    let triple = Triple::host();

    create_isa_from_triple(triple, flags)
}

impl<M: Module> CodegenBackend<M> {
    /// Create a new backend with a pre-configured module (uses host target)
    pub fn with_module(module: M) -> BackendResult<Self> {
        Self::with_module_and_target(module, Target::host())
    }

    /// Create a new backend with a pre-configured module and target
    pub fn with_module_and_target(module: M, target: Target) -> BackendResult<Self> {
        let ctx = module.make_context();

        Ok(Self {
            module,
            ctx,
            func_ids: BTreeMap::new(),
            runtime_funcs: HashMap::new(),
            global_ids: BTreeMap::new(),
            body_stub: None,
            target,
            module_prefix: None,
            is_entry_module: false,
            import_map: std::sync::Arc::new(std::collections::HashMap::new()),
            ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
            use_map: std::collections::HashMap::new(),
            data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
            fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
            vtable_data_ids: BTreeMap::new(),
            vtable_type_ids: BTreeMap::new(),
        })
    }

    /// Get the target this backend is compiling for
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Set the module prefix for name mangling.
    pub fn set_module_prefix(&mut self, prefix: String) {
        self.module_prefix = Some(prefix);
    }

    /// Mark this module as the program entry point.
    ///
    /// When `true`, the `main` function is emitted as `spl_main` with
    /// Preemptible linkage so the C runtime entry stub can call it.
    /// When `false`, `main` is prefix-mangled like any other local symbol.
    pub fn set_entry_module(&mut self, v: bool) {
        self.is_entry_module = v;
    }

    /// Set the import map for cross-module function resolution.
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.import_map = map;
    }

    /// Set the ambiguous names set for symbol resolution.
    pub fn set_ambiguous_names(&mut self, names: std::sync::Arc<std::collections::HashSet<String>>) {
        self.ambiguous_names = names;
    }

    /// Set the per-module use map for resolving imports from `use` statements.
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.use_map = map;
    }

    /// Set the set of mangled names that correspond to cross-module DATA
    /// globals (val/var/const/static), so `declare_globals` does not misroute
    /// them through the function-import fast path.
    pub fn set_data_exports(&mut self, exports: std::sync::Arc<std::collections::HashSet<String>>) {
        self.data_exports = exports;
    }

    pub fn set_fn_arities(&mut self, arities: std::sync::Arc<std::collections::HashMap<String, usize>>) {
        self.fn_arities = arities;
    }

    /// Mangle a function name with the module prefix (if set).
    ///
    /// - If `name == "main"` **and** this is the entry module, return `"spl_main"`.
    /// - If `name == "main"` **and** this is NOT the entry module, apply the normal
    ///   prefix mangling (e.g. `module_prefix__main`).
    /// - All other names follow the existing prefix logic.
    pub fn mangle_name(&self, name: &str) -> String {
        if name == "main" && self.is_entry_module {
            return "spl_main".to_string();
        }
        let mangled = match &self.module_prefix {
            Some(prefix) => format!("{}__{}", prefix, name),
            None => name.to_string(),
        };
        self.sanitize_symbol(&mangled)
    }

    /// Sanitize a symbol name for consistent cross-module resolution.
    ///
    /// Dots in symbol names cause issues on macOS (Mach-O / Apple ld crashes)
    /// and create definition/reference mismatches when cross-compiling from
    /// macOS to bare-metal targets. Always sanitize to ensure consistency
    /// between function definitions and cross-module references.
    pub fn sanitize_symbol(&self, name: &str) -> String {
        if name.contains('.') {
            name.replace('.', "_dot_")
        } else {
            name.to_string()
        }
    }

    /// Declare external runtime functions for SFFI using shared specifications.
    ///
    /// Only declares functions appropriate for the given target (e.g., ARM-specific
    /// functions are excluded from x86_64 baremetal builds) to avoid spurious
    /// undefined-symbol link errors.
    pub fn declare_runtime_functions(
        module: &mut M,
        target: &Target,
        referenced_names: &HashSet<String>,
        locally_defined_names: &HashSet<String>,
    ) -> BackendResult<HashMap<&'static str, cranelift_module::FuncId>> {
        let mut funcs = HashMap::new();
        let call_conv = super::shared::platform_call_conv();

        for spec in runtime_funcs_for_target(target) {
            if locally_defined_names.contains(spec.name) {
                continue;
            }
            if !referenced_names.contains(spec.name) && !runtime_symbol_is_codegen_root(spec.name) {
                continue;
            }
            let sig = spec.build_signature(call_conv);
            let id = module
                .declare_function(spec.name, Linkage::Import, &sig)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;
            funcs.insert(spec.name, id);
        }

        Ok(funcs)
    }

    fn ensure_runtime_functions_declared(
        &mut self,
        referenced_names: &HashSet<String>,
        locally_defined_names: &HashSet<String>,
    ) -> BackendResult<()> {
        if self.runtime_funcs.is_empty() {
            self.runtime_funcs = Self::declare_runtime_functions(
                &mut self.module,
                &self.target,
                referenced_names,
                locally_defined_names,
            )?;
        }
        Ok(())
    }

    fn can_omit_runtime_imports(mir: &MirModule, functions: &[MirFunction]) -> bool {
        mir.extern_fn_names.is_empty()
            && mir.globals.is_empty()
            && mir.global_init_values.is_empty()
            && mir.global_init_strings.is_empty()
            && mir.global_init_arrays.is_empty()
            && mir.vtable_impls.is_empty()
            && functions
                .iter()
                .all(|func| func.blocks.iter().all(|block| block.instructions.is_empty()))
    }

    /// Create or return a no-op body stub (fn() -> void) and return its FuncId.
    #[allow(dead_code)] // reason: reachable via SFFI or future entry point; not yet wired
    pub fn ensure_body_stub(&mut self) -> BackendResult<cranelift_module::FuncId> {
        if let Some(id) = self.body_stub {
            return Ok(id);
        }

        let mut ctx = self.module.make_context();
        let func_id =
            create_body_stub(&mut self.module, &mut ctx, "__simple_body_stub").map_err(BackendError::ModuleError)?;

        self.body_stub = Some(func_id);
        Ok(func_id)
    }

    /// Declare all functions from a MIR module.
    ///
    /// When `module_prefix` is set, locally-defined functions are declared under
    /// their mangled name (`prefix__name`) to prevent symbol collisions across
    /// compilation units. The raw name is also inserted into `func_ids` so that
    /// intra-module call resolution by raw name still works.
    pub fn declare_functions(
        &mut self,
        functions: &[MirFunction],
        referenced_names: &HashSet<String>,
    ) -> BackendResult<()> {
        let mut func_ids = BTreeMap::new();

        // First, add runtime function IDs for functions that are already declared
        for (name, id) in &self.runtime_funcs {
            func_ids.insert(name.to_string(), *id);
        }

        let _total_mir_functions = functions.len();

        // Then declare non-runtime functions
        for func in functions {
            // Skip functions that are already declared as runtime functions
            // This handles extern functions from Simple code that match runtime functions
            if self.runtime_funcs.contains_key(func.name.as_str()) && func.blocks.is_empty() {
                continue;
            }

            let sig = super::shared::build_mir_signature(func);

            // Determine linkage and symbol name.
            //
            // `main` handling depends on is_entry_module:
            //   - Entry module main:     symbol = "spl_main",      linkage = Export
            //   - Non-entry module main: symbol = mangled name,    linkage = Local
            //
            // All other functions with bodies get Export linkage (STB_GLOBAL in ELF)
            // so they override weak crt0 boot-stubs in freestanding builds.
            let has_body = !func.blocks.is_empty();

            let (symbol_name, linkage) = if func.name == "main" && has_body {
                if self.is_entry_module {
                    ("spl_main".to_string(), cranelift_module::Linkage::Export)
                } else {
                    // Export with mangled name so cross-module trampolines can call it
                    (self.mangle_name(&func.name), cranelift_module::Linkage::Export)
                }
            } else if !has_body {
                if !referenced_names.contains(func.name.as_str()) {
                    continue;
                }
                (self.sanitize_symbol(&func.name), cranelift_module::Linkage::Import)
            } else {
                // Export (STB_GLOBAL) so symbols override weak crt0 boot-stubs and
                // are visible to the freestanding --defsym linker mechanism.
                // Mangled names prevent cross-module collisions.
                (self.mangle_name(&func.name), cranelift_module::Linkage::Export)
            };

            let func_id = self
                .module
                .declare_function(&symbol_name, linkage, &sig)
                .map_err(|e| BackendError::ModuleError(format!("Failed to declare '{}': {}", symbol_name, e)))?;

            // Always register under the raw name so local calls resolve
            func_ids.insert(func.name.clone(), func_id);
            // Also register under the mangled name if different
            if symbol_name != func.name {
                func_ids.insert(symbol_name, func_id);
            }
        }

        // Merge into existing func_ids rather than replacing.
        // Runtime funcs are pre-populated and must be preserved.
        for (name, id) in func_ids {
            self.func_ids.entry(name).or_insert(id);
        }
        Ok(())
    }

    /// Declare all global variables from a MIR module.
    ///
    /// When `module_prefix` is set, globals are mangled to prevent collisions.
    ///
    /// Globals that correspond to extern function declarations (e.g. `rt_getpid`)
    /// are initialized with the function's import address so that `GlobalLoad`
    /// followed by `IndirectCall` resolves correctly at link time.
    pub fn declare_globals(
        &mut self,
        globals: &[(String, TypeId, bool)],
        extern_fn_names: &std::collections::HashSet<String>,
        global_init_values: &std::collections::HashMap<String, i64>,
        local_globals: &std::collections::HashSet<String>,
    ) -> BackendResult<()> {
        use super::types_util::type_to_cranelift;
        let is_jit_module = std::any::type_name::<M>().contains("JITModule");

        for (name, ty, is_mutable) in globals {
            let trace_global = std::env::var("SIMPLE_TRACE_DECLARE_GLOBALS").is_ok()
                && matches!(
                    name.as_str(),
                    "decl_tag"
                        | "frontend__core__ast__decl_tag"
                        | "module_decl_slots"
                        | "frontend__core__ast__module_decl_slots"
                        | "DECL_FN"
                        | "frontend__core__ast__DECL_FN"
                );
            if trace_global {
                eprintln!(
                    "[declare-globals] start name={} ty={:?} mut={} local={} module_prefix={:?}",
                    name,
                    ty,
                    is_mutable,
                    local_globals.contains(name),
                    self.module_prefix
                );
            }
            // Skip globals that are actually runtime functions (extern functions)
            if self.runtime_funcs.contains_key(name.as_str()) {
                if trace_global {
                    eprintln!("[declare-globals] skip runtime name={}", name);
                }
                continue;
            }

            // If this global is an extern function declaration, create a data slot
            // initialized with the function's import address. This ensures that
            // GlobalLoad + IndirectCall patterns resolve correctly at link time.
            if extern_fn_names.contains(name) {
                if trace_global {
                    eprintln!("[declare-globals] skip extern fn name={}", name);
                }
                // Skip data slot creation for extern functions — the function
                // is already declared via declare_functions and can be called directly.
                // Creating a data slot with define_zeroinit + write_function_addr
                // corrupts Mach-O output (object crate BSS + relocation bug).
                continue;
            }

            // If this global name matches a declared function (local or imported),
            // it is a function reference used as a value (e.g., stored in a struct
            // field or variable). Initialize the BSS slot with the function address
            // so that GlobalLoad + IndirectCall resolves correctly.
            if let Some(&_func_id) = self.func_ids.get(name) {
                if trace_global {
                    eprintln!("[declare-globals] skip func_id name={}", name);
                }
                // Skip data slot creation for function references — calling through
                // a data slot (GlobalLoad + IndirectCall) is not needed when the function
                // can be called directly. Creating data slots with define_zeroinit +
                // write_function_addr corrupts Mach-O output (object crate bug).
                // The function is already in func_ids and can be resolved via compile_call.
                continue;
            }

            // Also skip data slot creation for cross-module function references
            // resolvable via use_map/import_map. Declare them as function imports
            // instead, so GlobalLoad + IndirectCall in MIR compiles to a direct
            // function call at codegen time. Without this, the codegen creates a
            // DATA import that the linker can't match to the FUNCTION symbol in
            // the defining module — leaving the data slot as NULL (0x1) on macOS.
            //
            // IMPORTANT: this fast path must NOT apply to cross-module data
            // globals (`val K: u32 = 1`, `var counter: i32 = 0`, etc.). If a
            // `val`-backed data symbol is declared as a function import here,
            // the GlobalLoad emitter (see codegen/instr/mod.rs) sees the name
            // in `func_ids`, picks the "function reference used as a value"
            // branch, and emits `func_addr` — returning the symbol's ADDRESS
            // instead of loading its VALUE. That's the cross-module `val u32`
            // constant corruption Agent Z1 observed (mod=5940624 instead of 1).
            // Skip this branch when the resolved mangled name is known to be
            // data (tracked in `data_exports`, built at import-map time).
            if !is_jit_module && !local_globals.contains(name) {
                if let Some(resolved) = self
                    .use_map
                    .get(name.as_str())
                    .or_else(|| self.import_map.get(name.as_str()))
                {
                    let sanitized = self.sanitize_symbol(resolved);
                    // If `resolved` (or its sanitized form) refers to a module-level
                    // data export, fall through to the data-import path below so
                    // `GlobalLoad` reads the value from memory instead of treating
                    // the symbol as a function pointer.
                    let looks_like_const_data = !name.is_empty()
                        && name
                            .chars()
                            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_');
                    let is_data_export = self.data_exports.contains(resolved) || self.data_exports.contains(&sanitized);
                    if !is_data_export && !looks_like_const_data {
                        let call_conv = super::shared::platform_call_conv();
                        let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
                        sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                        sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                        if let Ok(fid) =
                            self.module
                                .declare_function(&sanitized, cranelift_module::Linkage::Import, &sig)
                        {
                            if trace_global {
                                eprintln!(
                                    "[declare-globals] imported as function name={} resolved={}",
                                    name, sanitized
                                );
                            }
                            self.func_ids.entry(name.clone()).or_insert(fid);
                            continue;
                        }
                    }
                }
            }

            // If a symbol appears in MIR globals and local_globals for this module,
            // it must be emitted here. A use-map entry with the same short name can
            // coexist with local arena state/constants (for example core AST
            // DECL_* and decl_* globals); treating those as imports leaves only weak
            // stubs at link time and corrupts bootstrap state.
            let is_local = is_jit_module || local_globals.contains(name);

            // Linkage strategy for globals in per-module compilation:
            // - Local globals: Preemptible + initialized data (if available)
            // - Imported globals: Import linkage, resolve symbol via use_map/import_map
            if !is_local {
                if trace_global {
                    eprintln!("[declare-globals] import data name={}", name);
                }
                // Imported global: resolve the correct mangled name from the defining module
                // via use_map (per-module imports) or import_map (global unique names).
                let use_hit = self.use_map.get(name.as_str());
                let import_hit = self.import_map.get(name.as_str());
                if use_hit.is_none() && import_hit.is_none() {
                    eprintln!(
                        "[DEBUG declare_globals fallback] name={} module_prefix={:?}",
                        name, self.module_prefix
                    );
                }
                let resolved_name = use_hit
                    .or(import_hit)
                    .map(|s| self.sanitize_symbol(s))
                    .unwrap_or_else(|| self.mangle_name(name));
                let data_id = self
                    .module
                    .declare_data(&resolved_name, cranelift_module::Linkage::Import, *is_mutable, false)
                    .map_err(|e| BackendError::ModuleError(e.to_string()))?;

                self.global_ids.insert(name.clone(), data_id);
                if resolved_name != *name {
                    self.global_ids.insert(resolved_name, data_id);
                }
            } else {
                // Local global: define with Preemptible linkage.
                let local_symbol = self.mangle_name(name);
                if trace_global {
                    eprintln!(
                        "[declare-globals] define data name={} local_symbol={}",
                        name, local_symbol
                    );
                }
                let data_id = self
                    .module
                    .declare_data(
                        &local_symbol,
                        cranelift_module::Linkage::Preemptible,
                        *is_mutable,
                        false,
                    )
                    .map_err(|e| BackendError::ModuleError(e.to_string()))?;

                let mut data_desc = cranelift_module::DataDescription::new();
                // All globals are stored/loaded as i64 RuntimeValues, so allocate
                // at least 8 bytes regardless of the declared type (BOOL=1, I32=4, etc.)
                // to prevent buffer overflows when GlobalStore writes a full i64.
                let size = std::cmp::max(super::types_util::type_id_size(*ty) as usize, 8);
                if let Some(&init_val) = global_init_values.get(name) {
                    // Initialize with compile-time constant value
                    let bytes = init_val.to_le_bytes();
                    let mut buf = vec![0u8; size];
                    let copy_len = std::cmp::min(bytes.len(), size);
                    buf[..copy_len].copy_from_slice(&bytes[..copy_len]);
                    data_desc.define(buf.into_boxed_slice());
                } else {
                    data_desc.define_zeroinit(size);
                }

                self.module
                    .define_data(data_id, &data_desc)
                    .map_err(|e| BackendError::ModuleError(e.to_string()))?;

                self.global_ids.insert(name.clone(), data_id);
                if local_symbol != *name {
                    self.global_ids.insert(local_symbol, data_id);
                }
            }
        }
        Ok(())
    }

    /// Compile a single MIR function
    pub fn compile_function(&mut self, func: &MirFunction) -> BackendResult<()> {
        let func_id = *self
            .func_ids
            .get(&func.name)
            .ok_or_else(|| BackendError::UnknownFunction(func.name.clone()))?;

        // Skip extern/imported functions (no body expected; provided by runtime/SFFI).
        let decl = self.module.declarations().get_function_decl(func_id);
        if decl.linkage == cranelift_module::Linkage::Import {
            return Ok(());
        }

        let sig = build_mir_signature(func);
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        // Use the shared function body compilation
        let body_result = catch_unwind(AssertUnwindSafe(|| {
            compile_function_body(
                &mut self.module,
                &mut self.ctx.func,
                func,
                &mut self.func_ids,
                &self.runtime_funcs,
                &self.global_ids,
                &self.import_map,
                &self.use_map,
                &self.data_exports,
                &self.vtable_data_ids,
                &self.vtable_type_ids,
                &self.fn_arities,
            )
        }));
        match body_result {
            Ok(Ok(())) => {}
            Ok(Err(e)) => {
                eprintln!("[CODEGEN BODY] Function '{}' body compilation failed: {}", func.name, e);
                return Err(BackendError::ModuleError(e));
            }
            Err(payload) => {
                let panic_msg = if let Some(msg) = payload.downcast_ref::<&str>() {
                    (*msg).to_string()
                } else if let Some(msg) = payload.downcast_ref::<String>() {
                    msg.clone()
                } else {
                    "unknown panic payload".to_string()
                };
                eprintln!(
                    "[CODEGEN PANIC] Function '{}' panicked during body compilation/finalize: {}",
                    func.name, panic_msg
                );
                return Err(BackendError::ModuleError(format!(
                    "panic while compiling function '{}': {}",
                    func.name, panic_msg
                )));
            }
        }

        // Verify the function before defining - log errors but try to compile anyway
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            eprintln!(
                "[CODEGEN VERIFY] Function '{}' has verifier errors: {}",
                func.name, errors
            );
        }

        if std::env::var("SIMPLE_DUMP_STACK_SLOTS").is_ok() {
            let slot_count = self.ctx.func.sized_stack_slots.len();
            let dynamic_slot_count = self.ctx.func.dynamic_stack_slots.len();
            let slot_bytes: u32 = self.ctx.func.sized_stack_slots.values().map(|ss| ss.size).sum();
            if slot_count > 0 || dynamic_slot_count > 0 {
                eprintln!(
                    "[STACK-SLOTS] {}: sized={} bytes={} dynamic={}",
                    func.name, slot_count, slot_bytes, dynamic_slot_count
                );
                for (slot, data) in self.ctx.func.sized_stack_slots.iter() {
                    eprintln!(
                        "[STACK-SLOTS]   {:?}: kind={:?} size={} align_shift={}",
                        slot, data.kind, data.size, data.align_shift
                    );
                }
            } else {
                eprintln!("[STACK-SLOTS] {}: sized=0 bytes=0 dynamic=0", func.name);
            }
        }

        // Define the function (may fail if verifier errors are critical)
        match self.module.define_function(func_id, &mut self.ctx) {
            Ok(()) => {}
            Err(e) => {
                return Err(BackendError::ModuleError(format!(
                    "Compilation error in '{}': {}",
                    func.name, e
                )));
            }
        }

        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    /// Emit one static vtable data object per `impl Trait for Struct` entry.
    ///
    /// Each data object is named `__vtable__StructName__for__TraitName` and contains
    /// one 8-byte pointer per vtable slot (in slot index order). The pointer at slot i
    /// is a relocation to the implementing function for that method.
    ///
    /// After this call, `self.vtable_data_ids` maps struct_name → DataId so that
    /// `compile_struct_init` can write the vtable_ptr at offset 0.
    fn emit_vtable_data_objects(
        &mut self,
        vtable_impls: &[(crate::hir::TypeId, String, String, Vec<String>)],
    ) -> BackendResult<()> {
        for (struct_type_id, struct_name, vtable_sym, method_fns) in vtable_impls {
            let n = method_fns.len();
            if n == 0 {
                continue;
            }

            // Declare the vtable data object (local, read-only, not thread-local)
            let data_id = self
                .module
                .declare_data(vtable_sym, Linkage::Local, false, false)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;

            let mut data_desc = cranelift_module::DataDescription::new();
            data_desc.define(vec![0u8; n * 8].into_boxed_slice());

            // For each method slot, write a relocation pointing to the implementing function.
            for (slot, fn_name) in method_fns.iter().enumerate() {
                // Look up the func_id — try both mangled and unmangled names.
                let func_id_opt = self
                    .func_ids
                    .get(fn_name)
                    .copied()
                    .or_else(|| {
                        // Try with _dot_ mangling (StructName_dot_methodName)
                        let mangled = fn_name.replace('.', "_dot_");
                        self.func_ids.get(&mangled).copied()
                    })
                    .or_else(|| {
                        // Native-build prefixes local symbols with their module path. Vtable
                        // metadata is type-qualified but not module-qualified, so resolve a
                        // unique module-qualified suffix before falling back to a zero slot.
                        let mangled = fn_name.replace('.', "_dot_");
                        let suffix = format!("__{}", mangled);
                        let mut matches = self
                            .func_ids
                            .iter()
                            .filter(|(name, _)| name.ends_with(&suffix))
                            .map(|(_, id)| *id);
                        let first = matches.next();
                        if matches.next().is_none() {
                            first
                        } else {
                            None
                        }
                    });

                if let Some(func_id) = func_id_opt {
                    let func_ref = self.module.declare_func_in_data(func_id, &mut data_desc);
                    data_desc.write_function_addr((slot * 8) as u32, func_ref);
                }
                // If func_id not found (cross-module impl), slot stays zero — runtime will fault.
            }

            self.module
                .define_data(data_id, &data_desc)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;

            // Record struct_name → DataId and struct_type_id → DataId for compile_struct_init
            self.vtable_data_ids.insert(struct_name.clone(), data_id);
            self.vtable_type_ids.insert(*struct_type_id, data_id);
        }
        Ok(())
    }

    /// Compile all functions from a MIR module (with outlining expansion)
    pub fn compile_all_functions(&mut self, mir: &MirModule) -> BackendResult<Vec<MirFunction>> {
        // Expand with outlined functions for body_block users
        let functions = expand_with_outlined(mir);

        // Check for duplicate function names and deduplicate
        let mut seen_names = std::collections::HashSet::new();
        let mut unique_functions = Vec::new();
        for func in functions {
            if seen_names.insert(func.name.clone()) {
                unique_functions.push(func);
            }
        }
        let functions = inline_small_pure_functions(mir, unique_functions);
        let referenced_names = referenced_call_names(&functions);
        let locally_defined_names: HashSet<String> = functions
            .iter()
            .filter(|func| !func.blocks.is_empty())
            .map(|func| func.name.clone())
            .collect();
        if !Self::can_omit_runtime_imports(mir, &functions) {
            self.ensure_runtime_functions_declared(&referenced_names, &locally_defined_names)?;
        }

        // First pass: declare functions, then globals.
        // Functions must be declared first so that declare_globals can detect
        // globals that correspond to function references and initialize their
        // BSS slots with the function address (instead of zero).
        self.declare_functions(&functions, &referenced_names)?;
        self.declare_globals(
            &mir.globals,
            &mir.extern_fn_names,
            &mir.global_init_values,
            &mir.local_globals,
        )?;

        // Vtable pass: emit one static data object per impl Trait for Struct.
        // Each data object is N * 8 bytes (one pointer per vtable slot).
        // The pointer at slot i is the address of the i-th method function.
        // The struct_name entry in vtable_data_ids is used by compile_struct_init
        // to write vtable_ptr at offset 0.
        self.emit_vtable_data_objects(&mir.vtable_impls)?;

        // Second pass: compile function bodies
        // Track functions that fail compilation so we can create stubs
        //
        // SIMPLE_DUMP_MIR=<filter>: dump post-inline MIR for functions whose
        // name contains <filter> (or all functions when filter is "1").
        let dump_mir_filter: Option<String> = std::env::var("SIMPLE_DUMP_MIR").ok();
        let mut failed_functions: Vec<&MirFunction> = Vec::new();
        for func in &functions {
            if func.blocks.is_empty() {
                continue;
            }
            if let Some(ref filter) = dump_mir_filter {
                if filter == "1" || func.name.contains(filter.as_str()) {
                    eprintln!("[MIR-DUMP] function: {}", func.name);
                    for block in &func.blocks {
                        eprintln!("  block {:?} (entry={})", block.id, block.id == func.entry_block);
                        for inst in &block.instructions {
                            eprintln!("    {:?}", inst);
                        }
                        eprintln!("    terminator: {:?}", block.terminator);
                    }
                }
            }
            match self.compile_function(func) {
                Ok(()) => {}
                Err(_e) => {
                    // Loud, distinctive marker so missing-body bugs cannot hide
                    // in normal log noise. Includes the func name so methods
                    // like "DesktopShell.init" surface immediately. The
                    // previous Agent V workaround inlined launcher_init() into
                    // DesktopShell.new() because `me init()` silently became a
                    // stub via this exact path.
                    //
                    // If this looks like a "Copy: source vreg not found" error,
                    // auto-dump the failing function's MIR so the cross-block
                    // VReg root cause is visible without requiring an extra env
                    // var or a seed rebuild with SIMPLE_NO_STUB_FALLBACK.
                    let err_str = format!("{:?}", _e);
                    if err_str.contains("source vreg") {
                        eprintln!(
                            "[CODEGEN-STUB-FALLBACK] undefined-vreg in '{}': {} \
                             — auto-dumping post-inline MIR:",
                            func.name, err_str
                        );
                        for block in &func.blocks {
                            eprintln!("  block {:?} (entry={})", block.id, block.id == func.entry_block);
                            for inst in &block.instructions {
                                eprintln!("    {:?}", inst);
                            }
                            eprintln!("    terminator: {:?}", block.terminator);
                        }
                    } else {
                        eprintln!(
                            "[CODEGEN-STUB-FALLBACK] body compilation failed for '{}': {:?} \
                             — this function will be replaced by an empty stub. \
                             Set SIMPLE_NO_STUB_FALLBACK=1 to make this a hard error.",
                            func.name, _e
                        );
                    }
                    failed_functions.push(func);
                    // IMPORTANT: Clear context to prevent state from leaking to next function
                    self.module.clear_context(&mut self.ctx);
                }
            }
        }

        // Hard-fail mode: opt-in via SIMPLE_NO_STUB_FALLBACK=1.
        // When set, any function whose body failed to compile aborts the
        // whole module compilation with a clear error instead of silently
        // emitting an empty stub. This is the recommended setting when
        // diagnosing missing-body bugs (e.g., the baremetal me-method
        // dispatch issue from 2026-04-13).
        if !failed_functions.is_empty() && std::env::var("SIMPLE_NO_STUB_FALLBACK").is_ok() {
            let names: Vec<&str> = failed_functions.iter().map(|f| f.name.as_str()).collect();
            return Err(BackendError::ModuleError(format!(
                "SIMPLE_NO_STUB_FALLBACK: {} function body/bodies failed to compile and would have been replaced by empty stubs: [{}]",
                names.len(),
                names.join(", ")
            )));
        }

        // Create stubs for failed functions
        for func in failed_functions {
            // In bootstrap mode we let unresolved symbols be handled by C shims/auto-stubs.
            if std::env::var("SIMPLE_BOOTSTRAP").is_ok() {
                continue;
            }
            if let Some(&func_id) = self.func_ids.get(&func.name) {
                // If this function is declared as an import (extern), skip stub creation;
                // the symbol is expected to be provided by the runtime/SFFI.
                let decl = self.module.declarations().get_function_decl(func_id);
                if decl.linkage == cranelift_module::Linkage::Import {
                    continue;
                }
                // Create a stub with the correct signature
                let sig = build_mir_signature(func);
                self.ctx.func.signature = sig.clone();
                self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

                let mut func_ctx = cranelift_frontend::FunctionBuilderContext::new();
                let mut builder = cranelift_frontend::FunctionBuilder::new(&mut self.ctx.func, &mut func_ctx);
                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);
                builder.seal_block(entry_block);

                // Return appropriate zero/default value based on signature return type
                if sig.returns.is_empty() {
                    builder.ins().return_(&[]);
                } else {
                    // Create zero values for each return type
                    let return_vals: Vec<_> = sig
                        .returns
                        .iter()
                        .map(|abi_param| {
                            let ty = abi_param.value_type;
                            if ty.is_int() {
                                builder.ins().iconst(ty, 0)
                            } else if ty.is_float() {
                                if ty == types::F32 {
                                    builder.ins().f32const(0.0)
                                } else {
                                    builder.ins().f64const(0.0)
                                }
                            } else {
                                // Default to i64 for pointer types
                                builder.ins().iconst(types::I64, 0)
                            }
                        })
                        .collect();
                    builder.ins().return_(&return_vals);
                }
                builder.finalize();

                // Try to define the stub
                if let Err(e) = self.module.define_function(func_id, &mut self.ctx) {
                    eprintln!("[ERROR] Failed to create stub for '{}': {}", func.name, e);
                }
                self.module.clear_context(&mut self.ctx);
            }
        }

        // Generate module initialization function for heap-backed global constants.
        // This allocates runtime strings/arrays and stores their handles in globals.
        if !mir.global_init_strings.is_empty() || !mir.global_init_arrays.is_empty() {
            self.generate_module_init(&mir.global_init_strings, &mir.global_init_arrays)?;
        }

        Ok(functions)
    }

    /// Generate a `__module_init` function that initializes heap-backed globals.
    ///
    /// For each string constant (e.g., `val NL = "\n"`), this function:
    /// 1. Creates static byte data in .rodata
    /// 2. Calls `rt_string_new(ptr, len)` to create a RuntimeValue
    /// 3. Stores the result to the global variable
    ///
    /// The function is registered via `.init_array` so it runs before `main()`.
    fn generate_module_init(
        &mut self,
        init_strings: &std::collections::HashMap<String, String>,
        init_arrays: &std::collections::HashMap<String, crate::hir::HirGlobalArrayInit>,
    ) -> BackendResult<()> {
        use cranelift_codegen::ir::{types, MemFlags, UserFuncName};

        let init_name = match &self.module_prefix {
            Some(prefix) => {
                // Sanitize dots → _dot_ so the symbol name matches _init_all.cpp references
                let sanitized = if cfg!(target_os = "macos") {
                    prefix.replace('.', "_dot_")
                } else {
                    prefix.to_string()
                };
                format!("__module_init_{}", sanitized)
            }
            None => "__module_init".to_string(),
        };

        // Declare the init function: fn() -> void
        let call_conv = super::shared::platform_call_conv();
        let sig = cranelift_codegen::ir::Signature::new(call_conv);
        let func_id = self
            .module
            .declare_function(&init_name, cranelift_module::Linkage::Preemptible, &sig)
            .map_err(|e| BackendError::ModuleError(format!("declare __module_init: {e}")))?;

        let string_new_id = if init_strings.is_empty() {
            None
        } else {
            Some(
                *self
                    .runtime_funcs
                    .get("rt_string_new")
                    .ok_or_else(|| BackendError::ModuleError("rt_string_new not declared".into()))?,
            )
        };
        let array_new_id = if init_arrays.is_empty() {
            None
        } else {
            Some(
                *self
                    .runtime_funcs
                    .get("rt_array_new")
                    .ok_or_else(|| BackendError::ModuleError("rt_array_new not declared".into()))?,
            )
        };
        let array_push_id = if init_arrays.is_empty() {
            None
        } else {
            Some(
                *self
                    .runtime_funcs
                    .get("rt_array_push")
                    .ok_or_else(|| BackendError::ModuleError("rt_array_push not declared".into()))?,
            )
        };
        let byte_array_new_id = if init_arrays.values().any(|init| init.element_type == TypeId::U8) {
            Some(
                *self
                    .runtime_funcs
                    .get("rt_byte_array_new")
                    .ok_or_else(|| BackendError::ModuleError("rt_byte_array_new not declared".into()))?,
            )
        } else {
            None
        };
        let byte_push_id = if init_arrays.values().any(|init| init.element_type == TypeId::U8) {
            Some(
                *self
                    .runtime_funcs
                    .get("rt_typed_bytes_u8_push")
                    .ok_or_else(|| BackendError::ModuleError("rt_typed_bytes_u8_push not declared".into()))?,
            )
        } else {
            None
        };

        // Build the function body
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        let mut func_ctx = cranelift_frontend::FunctionBuilderContext::new();
        let mut builder = cranelift_frontend::FunctionBuilder::new(&mut self.ctx.func, &mut func_ctx);
        let entry_block = builder.create_block();
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Sort by name for deterministic output
        let mut sorted_strings: Vec<_> = init_strings.iter().collect();
        sorted_strings.sort_by_key(|(name, _)| (*name).clone());

        for (global_name, string_val) in &sorted_strings {
            // 1. Create static byte data for the string
            let bytes = string_val.as_bytes();
            let data_name = format!(".Linit_str_{:016x}", {
                let mut h: u64 = 0xcbf29ce484222325;
                for &b in global_name.as_bytes() {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                for &b in bytes {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                h
            });
            let data_id = self
                .module
                .declare_data(&data_name, cranelift_module::Linkage::Local, false, false)
                .map_err(|e| BackendError::ModuleError(format!("declare string data: {e}")))?;
            {
                let mut data_desc = cranelift_module::DataDescription::new();
                data_desc.define(bytes.to_vec().into_boxed_slice());
                let _ = self.module.define_data(data_id, &data_desc);
            }

            // 2. Load string bytes pointer and length
            let data_ref = self.module.declare_data_in_func(data_id, builder.func);
            let str_ptr = builder.ins().global_value(types::I64, data_ref);
            let str_len = builder.ins().iconst(types::I64, bytes.len() as i64);

            // 3. Call rt_string_new(ptr, len) -> RuntimeValue
            let string_new_ref = self.module.declare_func_in_func(string_new_id.unwrap(), builder.func);
            let call_inst = builder.ins().call(string_new_ref, &[str_ptr, str_len]);
            let string_rv = builder.inst_results(call_inst)[0];

            // 4. Store to global variable
            if let Some(&gid) = self.global_ids.get(global_name.as_str()) {
                let global_ref = self.module.declare_data_in_func(gid, builder.func);
                let global_addr = builder.ins().global_value(types::I64, global_ref);
                builder.ins().store(MemFlags::new(), string_rv, global_addr, 0);
            } else {
                // Global might not be in global_ids if it's cross-module.
                // Try the mangled name from the module prefix.
                let mangled = match &self.module_prefix {
                    Some(prefix) => format!("{}__{}", prefix, global_name),
                    None => global_name.to_string(),
                };
                if let Some(&gid) = self.global_ids.get(mangled.as_str()) {
                    let global_ref = self.module.declare_data_in_func(gid, builder.func);
                    let global_addr = builder.ins().global_value(types::I64, global_ref);
                    builder.ins().store(MemFlags::new(), string_rv, global_addr, 0);
                }
                // If still not found, skip silently (global might be in another module)
            }
        }

        let mut sorted_arrays: Vec<_> = init_arrays.iter().collect();
        sorted_arrays.sort_by_key(|(name, _)| (*name).clone());
        for (global_name, init) in &sorted_arrays {
            let capacity = builder.ins().iconst(types::I64, init.values.len() as i64);
            let array_rv = if init.element_type == TypeId::U8 {
                let new_ref = self
                    .module
                    .declare_func_in_func(byte_array_new_id.unwrap(), builder.func);
                let call_inst = builder.ins().call(new_ref, &[capacity]);
                let array = builder.inst_results(call_inst)[0];
                let push_ref = self.module.declare_func_in_func(byte_push_id.unwrap(), builder.func);
                for value in &init.values {
                    let byte = builder.ins().iconst(types::I64, (*value & 0xff) as i64);
                    builder.ins().call(push_ref, &[array, byte]);
                }
                array
            } else {
                let new_ref = self.module.declare_func_in_func(array_new_id.unwrap(), builder.func);
                let call_inst = builder.ins().call(new_ref, &[capacity]);
                let array = builder.inst_results(call_inst)[0];
                let push_ref = self.module.declare_func_in_func(array_push_id.unwrap(), builder.func);
                for value in &init.values {
                    let raw = builder.ins().iconst(types::I64, *value);
                    let shift = builder.ins().iconst(types::I64, 3);
                    let boxed = builder.ins().ishl(raw, shift);
                    builder.ins().call(push_ref, &[array, boxed]);
                }
                array
            };

            if let Some(&gid) = self.global_ids.get(global_name.as_str()) {
                let global_ref = self.module.declare_data_in_func(gid, builder.func);
                let global_addr = builder.ins().global_value(types::I64, global_ref);
                builder.ins().store(MemFlags::new(), array_rv, global_addr, 0);
            } else {
                let mangled = match &self.module_prefix {
                    Some(prefix) => format!("{}__{}", prefix, global_name),
                    None => global_name.to_string(),
                };
                if let Some(&gid) = self.global_ids.get(mangled.as_str()) {
                    let global_ref = self.module.declare_data_in_func(gid, builder.func);
                    let global_addr = builder.ins().global_value(types::I64, global_ref);
                    builder.ins().store(MemFlags::new(), array_rv, global_addr, 0);
                }
            }
        }

        builder.ins().return_(&[]);
        builder.finalize();

        // Define the function
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| BackendError::ModuleError(format!("define __module_init: {e}")))?;
        self.module.clear_context(&mut self.ctx);

        // Skip .init_array registration — define_zeroinit + write_function_addr
        // corrupts Mach-O output (object crate bug). Module init functions are
        // called explicitly from the native binary's startup code instead.
        // The function is still defined and exported (Preemptible linkage above),
        // so the linker/startup code can find and call it.

        Ok(())
    }
}

/// Compute a module prefix from a file path relative to a source root.
///
/// Example: `src/compiler/10.frontend/core/lexer.spl` → `compiler__frontend__core__lexer`
///
/// The numbered layer prefixes (e.g., `10.`, `70.`) are stripped.
pub fn module_prefix_from_path(file_path: &std::path::Path, source_root: &std::path::Path) -> String {
    let relative = file_path.strip_prefix(source_root).unwrap_or(file_path);

    let mut parts = Vec::new();
    for component in relative.components() {
        if let std::path::Component::Normal(s) = component {
            let s = s.to_string_lossy();
            // Strip .spl extension for the last component
            let s = s.strip_suffix(".spl").unwrap_or(&s).to_string();
            // Strip numbered layer prefix (e.g., "10.frontend" -> "frontend")
            let s = if let Some(dot_pos) = s.find('.') {
                if s[..dot_pos].chars().all(|c| c.is_ascii_digit()) {
                    s[dot_pos + 1..].to_string()
                } else {
                    s
                }
            } else {
                s
            };
            if !s.is_empty() {
                parts.push(s);
            }
        }
    }
    let prefix = parts.join("__");
    if prefix.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        format!("m_{}", prefix)
    } else {
        prefix
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{BlockId, CallTarget, MirModule, Terminator, VReg};
    use cranelift_object::{ObjectBuilder, ObjectModule};
    use simple_parser::ast::Visibility;

    fn test_backend() -> CodegenBackend<ObjectModule> {
        let settings = BackendSettings::aot();
        let (_flags, isa) = create_isa_and_flags(&settings).expect("isa");
        let builder =
            ObjectBuilder::new(isa, "test_module", cranelift_module::default_libcall_names()).expect("object builder");
        CodegenBackend::with_module(ObjectModule::new(builder)).expect("backend")
    }

    fn main_returning_zero() -> MirFunction {
        let mut main = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let ret = main.new_vreg();
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 0 });
        main.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
        main
    }

    #[test]
    fn unused_empty_extern_is_not_declared() {
        let mut unused = MirFunction::new("rt_simd_add_f32x4".to_string(), TypeId::I64, Visibility::Public);
        unused.blocks.clear();

        let mut module = MirModule::new();
        module.functions.push(unused);
        module.functions.push(main_returning_zero());

        let mut backend = test_backend();
        backend.compile_all_functions(&module).expect("compile");

        assert!(!backend.func_ids.contains_key("rt_simd_add_f32x4"));
    }

    #[test]
    fn referenced_empty_extern_is_declared() {
        let mut extern_fn = MirFunction::new("external_used".to_string(), TypeId::I64, Visibility::Public);
        extern_fn.blocks.clear();

        let mut main = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let dest = main.new_vreg();
        main.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::Call {
            dest: Some(dest),
            target: CallTarget::from_name("external_used"),
            args: Vec::<VReg>::new(),
        });
        main.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(dest));

        let mut module = MirModule::new();
        module.functions.push(extern_fn);
        module.functions.push(main);

        let mut backend = test_backend();
        backend.compile_all_functions(&module).expect("compile");

        assert!(backend.func_ids.contains_key("external_used"));
    }

    #[test]
    fn backend_generated_array_push_is_declared_without_source_reference() {
        let mut module = MirModule::new();
        module.functions.push(main_returning_zero());

        let mut backend = test_backend();
        backend.compile_all_functions(&module).expect("compile");

        assert!(backend.runtime_funcs.contains_key("rt_array_push"));
    }

    #[test]
    fn backend_generated_interp_bridge_helpers_are_declared_without_source_reference() {
        let mut main = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let arg = main.new_vreg();
        let dest = main.new_vreg();
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: arg, value: 42 });
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::InterpCall {
                dest: Some(dest),
                func_name: "fallback_function".to_string(),
                args: vec![arg],
            });
        main.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(dest));

        let mut module = MirModule::new();
        module.functions.push(main);

        let mut backend = test_backend();
        backend.compile_all_functions(&module).expect("compile");

        assert!(backend.runtime_funcs.contains_key("rt_alloc"));
        assert!(backend.runtime_funcs.contains_key("rt_interp_call"));
    }

    #[test]
    fn collection_mir_instructions_declare_generated_runtime_calls() {
        let mut main = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let collection = main.new_vreg();
        let index = main.new_vreg();
        let value = main.new_vreg();
        let get_dest = main.new_vreg();
        let slice_dest = main.new_vreg();
        let dict_dest = main.new_vreg();
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt {
                dest: collection,
                value: 0,
            });
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: index, value: 0 });
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: value, value: 1 });
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::IndexGet {
                dest: get_dest,
                collection,
                index,
            });
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::IndexSet {
                collection,
                index,
                value,
            });
        main.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::SliceOp {
            dest: slice_dest,
            collection,
            start: Some(index),
            end: Some(value),
            step: None,
        });
        main.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::DictLit {
            dest: dict_dest,
            keys: vec![index],
            values: vec![value],
        });
        main.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(get_dest));

        let names = referenced_call_names(&[main]);

        assert!(names.contains("rt_index_get"));
        assert!(names.contains("rt_index_set"));
        assert!(names.contains("rt_slice"));
        assert!(names.contains("rt_dict_new"));
        assert!(names.contains("rt_dict_set"));
    }
}
