/// LLVM backend core - struct definition, constructors, and basic accessors
use crate::codegen::backend_trait::NativeBackend;
use crate::error::CompileError;
use crate::hir::TypeId;
use crate::mir::{MirFunction, MirModule};
use crate::optimizations::NativeOptimizationLevel;
use simple_common::target::{Target, TargetArch, TargetCpu, TargetOS};
use std::cell::RefCell;

#[cfg(feature = "llvm")]
use inkwell::attributes::{Attribute, AttributeLoc};
#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::context::Context;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::passes::PassBuilderOptions;
#[cfg(feature = "llvm")]
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target as LlvmTarget, TargetMachine};
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;
#[cfg(feature = "llvm")]
use inkwell::values::{BasicMetadataValueEnum, FunctionValue};
#[cfg(feature = "llvm")]
use inkwell::OptimizationLevel;

/// LLVM-based code generator
///
/// # Drop order
/// Rust drops struct fields in declaration order.  `module` and `builder`
/// borrow from `context`, so they **must** be dropped first.  We therefore
/// declare them before `context` (which is an owned `Box<Context>`).
pub struct LlvmBackend {
    pub(super) target: Target,
    pub(super) opt_level: NativeOptimizationLevel,
    pub(super) cpu: TargetCpu,
    /// Enable coverage instrumentation
    pub(super) coverage_enabled: bool,
    // --- borrowing fields first (dropped before context) ---
    #[cfg(feature = "llvm")]
    pub(super) module: RefCell<Option<Module<'static>>>,
    #[cfg(feature = "llvm")]
    pub(super) builder: RefCell<Option<Builder<'static>>>,
    /// Counter for coverage basic blocks
    #[cfg(feature = "llvm")]
    pub(super) coverage_counter: RefCell<u32>,
    // --- owned context last (dropped after module/builder) ---
    #[cfg(feature = "llvm")]
    pub(super) context: Box<Context>,
    /// Import map: raw function name → mangled name for cross-module resolution
    pub(super) import_map: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Exact arity for imported functions, keyed by canonical mangled symbol.
    pub(super) fn_arities: std::sync::Arc<std::collections::HashMap<String, usize>>,
    /// Mangled module-level data exports, used to distinguish imported data
    /// from imported function symbols when a GlobalLoad references a symbol
    /// that was not present in the importing module's `mir.globals`.
    pub(super) data_exports: std::sync::Arc<std::collections::HashSet<String>>,
    /// Per-module use map from `use` statements
    pub(super) use_map: std::collections::HashMap<String, String>,
    /// Return types for functions declared in the current MIR module.
    pub(super) function_return_types: RefCell<std::collections::HashMap<String, crate::hir::TypeId>>,
    /// Module symbol prefix, used to name the per-module `__module_init_<prefix>`
    /// function so the linker's init-caller aggregator can discover it. Mirrors
    /// the cranelift backend's `module_prefix` (common_backend.rs).
    pub(super) module_prefix: Option<String>,
}

// Manual Debug implementation since Context/Module/Builder don't implement Debug
impl std::fmt::Debug for LlvmBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LlvmBackend")
            .field("target", &self.target)
            .field("coverage_enabled", &self.coverage_enabled)
            .field("has_module", &cfg!(feature = "llvm"))
            .finish()
    }
}

impl LlvmBackend {
    /// Return a `&'static Context` reference from the owned `Box<Context>`.
    ///
    /// # Safety
    /// This is safe because:
    /// - The `Box<Context>` lives as long as `self`.
    /// - `module` and `builder` (which borrow from `Context`) are declared
    ///   before `context` in the struct, so Rust drops them first.
    /// - No `Module` or `Builder` escapes `self` with a `'static` lifetime
    ///   that could outlive the struct.
    #[cfg(feature = "llvm")]
    pub(super) fn context_ref(&self) -> &'static Context {
        unsafe { &*(self.context.as_ref() as *const Context) }
    }

    #[cfg(feature = "llvm")]
    fn apply_function_optimization_attrs(&self, func: FunctionValue<'static>, attrs: &[String]) {
        let wants_inline = attrs
            .iter()
            .any(|attr| attr == "inline" || attr == "always_inline" || attr == "force_inline");
        if wants_inline {
            let kind = Attribute::get_named_enum_kind_id("alwaysinline");
            let always_inline = self.context_ref().create_enum_attribute(kind, 0);
            func.add_attribute(AttributeLoc::Function, always_inline);
        }
    }

    #[cfg(feature = "llvm")]
    fn llvm_optimization_level(&self) -> OptimizationLevel {
        match self.opt_level {
            NativeOptimizationLevel::None => OptimizationLevel::None,
            NativeOptimizationLevel::Basic => OptimizationLevel::Less,
            NativeOptimizationLevel::Standard => OptimizationLevel::Default,
            NativeOptimizationLevel::Aggressive => OptimizationLevel::Aggressive,
        }
    }

    #[cfg(feature = "llvm")]
    fn optimize_module_ir(&self, module: &Module<'static>, target_machine: &TargetMachine) -> Result<(), CompileError> {
        if matches!(self.opt_level, NativeOptimizationLevel::None) {
            return Ok(());
        }

        let options = PassBuilderOptions::create();
        options.set_verify_each(false);
        options.set_loop_interleaving(true);
        options.set_loop_vectorization(true);
        options.set_loop_slp_vectorization(true);
        options.set_loop_unrolling(matches!(self.opt_level, NativeOptimizationLevel::Aggressive));
        if matches!(self.opt_level, NativeOptimizationLevel::Aggressive) {
            options.set_merge_functions(true);
        }

        let pipeline = match self.opt_level {
            NativeOptimizationLevel::None => return Ok(()),
            NativeOptimizationLevel::Basic => "default<O1>",
            NativeOptimizationLevel::Standard => "default<O2>",
            NativeOptimizationLevel::Aggressive => "default<O3>",
        };
        module
            .run_passes(pipeline, target_machine, options)
            .map_err(|e| crate::error::factory::llvm_build_failed("run LLVM optimization passes", &e.to_string()))
    }

    /// Create a new LLVM backend for the given target
    pub fn new(target: Target) -> Result<Self, CompileError> {
        Self::new_with_opt_level(target, NativeOptimizationLevel::Standard)
    }

    /// Create a new LLVM backend for the given target and optimization profile.
    pub fn new_with_opt_level(target: Target, opt_level: NativeOptimizationLevel) -> Result<Self, CompileError> {
        Self::new_with_opt_level_and_cpu(target, opt_level, TargetCpu::builtin_default_for_arch(target.arch))
    }

    pub fn new_with_opt_level_and_cpu(
        target: Target,
        opt_level: NativeOptimizationLevel,
        cpu: TargetCpu,
    ) -> Result<Self, CompileError> {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = (target, opt_level, cpu); // Suppress unused warning when feature disabled
            Err(crate::error::factory::llvm_feature_required())
        }

        #[cfg(feature = "llvm")]
        {
            let context = Box::new(Context::create());
            Ok(Self {
                target,
                opt_level,
                cpu,
                coverage_enabled: false,
                module: RefCell::new(None),
                builder: RefCell::new(None),
                coverage_counter: RefCell::new(0),
                context,
                import_map: std::sync::Arc::new(std::collections::HashMap::new()),
                fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
                data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
                use_map: std::collections::HashMap::new(),
                function_return_types: RefCell::new(std::collections::HashMap::new()),
                module_prefix: None,
            })
        }
    }

    /// Set the import map for cross-module function resolution
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.import_map = map;
    }

    pub fn set_fn_arities(&mut self, arities: std::sync::Arc<std::collections::HashMap<String, usize>>) {
        self.fn_arities = arities;
    }

    /// Set the project-wide data export set for cross-module global references.
    pub fn set_data_exports(&mut self, exports: std::sync::Arc<std::collections::HashSet<String>>) {
        self.data_exports = exports;
    }

    /// Set the per-module use map from `use` statements
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.use_map = map;
    }

    /// Set the module symbol prefix used to name `__module_init_<prefix>`.
    /// Mirrors the cranelift backend so heap-typed module globals get a runtime
    /// initializer discoverable by the linker's init-caller aggregator.
    pub fn set_module_prefix(&mut self, prefix: String) {
        self.module_prefix = Some(prefix);
    }

    /// Enable coverage instrumentation
    pub fn with_coverage(mut self, enabled: bool) -> Self {
        self.coverage_enabled = enabled;
        self
    }

    /// Check if coverage is enabled
    pub fn coverage_enabled(&self) -> bool {
        self.coverage_enabled
    }

    /// Get the target for this backend
    pub fn target(&self) -> &Target {
        &self.target
    }

    pub fn cpu(&self) -> &TargetCpu {
        &self.cpu
    }

    #[cfg(feature = "llvm")]
    fn declare_globals(&self, module_ir: &MirModule) {
        let m = self.module.borrow();
        let Some(m) = m.as_ref() else {
            return;
        };
        let rv_type = self.runtime_int_type();

        let function_names: std::collections::HashSet<&str> =
            module_ir.functions.iter().map(|f| f.name.as_str()).collect();

        // A global with a heap-typed runtime initializer (string/array/struct/fn)
        // must be emitted WRITABLE: `__module_init` stores the freshly-built handle
        // into it at startup. An immutable `val X = "..."` would otherwise land in
        // .rodata and fault on that store. The init-map keys are post-mangle for
        // strings/arrays/functions; struct keys are not remapped by mangle_mir, so
        // also probe the de-prefixed tail.
        let has_runtime_init = |name: &str| -> bool {
            if module_ir.global_init_strings.contains_key(name)
                || module_ir.global_init_arrays.contains_key(name)
                || module_ir.global_init_functions.contains_key(name)
                || module_ir.global_init_structs.contains_key(name)
            {
                return true;
            }
            // struct fallback: `prefix__bare` global vs unmangled `bare` key
            if let Some((_, bare)) = name.rsplit_once("__") {
                if module_ir.global_init_structs.contains_key(bare) {
                    return true;
                }
            }
            false
        };

        for (name, _ty, is_mutable) in &module_ir.globals {
            // Extern/runtime functions are modeled as globals in MIR so GlobalLoad
            // can treat them as values, but they must not become LLVM data globals.
            // A same-named data global makes later call lowering add suffixed
            // function decls like `rt_mmio_write_u64.1`, which then fail to link.
            if module_ir.extern_fn_names.contains(name) {
                continue;
            }
            if function_names.contains(name.as_str()) {
                continue;
            }
            if m.get_global(name).is_some() {
                continue;
            }
            if m.get_function(name).is_some() {
                continue;
            }

            let global = m.add_global(rv_type, None, name);
            // Init-backed globals are written at startup by `__module_init`, so they
            // cannot be constant even if declared `val`.
            global.set_constant(!*is_mutable && !has_runtime_init(name));

            if module_ir.local_globals.contains(name) {
                let init = module_ir
                    .global_init_values
                    .get(name)
                    .map(|v| rv_type.const_int(*v as u64, true))
                    .unwrap_or_else(|| rv_type.const_zero());
                global.set_initializer(&init);
                global.set_linkage(inkwell::module::Linkage::External);
            } else {
                global.set_linkage(inkwell::module::Linkage::External);
            }
        }

        for func in &module_ir.functions {
            for block in &func.blocks {
                for inst in &block.instructions {
                    if let crate::mir::MirInst::GlobalLoad { global_name, .. } = inst {
                        if !self.data_exports.contains(global_name) {
                            if let Some(&arity) = self.fn_arities.get(global_name) {
                                if m.get_function(global_name).is_none() && m.get_global(global_name).is_none() {
                                    let params: Vec<inkwell::types::BasicMetadataTypeEnum> =
                                        std::iter::repeat_n(rv_type.into(), arity).collect();
                                    let function = m.add_function(global_name, rv_type.fn_type(&params, false), None);
                                    function.set_linkage(inkwell::module::Linkage::External);
                                }
                                continue;
                            }
                        }
                    }
                    let (name, is_store) = match inst {
                        crate::mir::MirInst::GlobalLoad { global_name, .. } => (global_name, false),
                        crate::mir::MirInst::GlobalStore { global_name, .. } => (global_name, true),
                        _ => continue,
                    };
                    if module_ir.extern_fn_names.contains(name) {
                        continue;
                    }
                    let local_init = module_ir.global_init_values.get(name);
                    if !self.data_exports.contains(name)
                        && !module_ir.local_globals.contains(name)
                        && local_init.is_none()
                    {
                        continue;
                    }
                    if m.get_global(name).is_some() || m.get_function(name).is_some() {
                        continue;
                    }
                    let global = m.add_global(rv_type, None, name);
                    global.set_constant(!is_store);
                    if let Some(value) = local_init {
                        global.set_initializer(&rv_type.const_int(*value as u64, true));
                    }
                    global.set_linkage(inkwell::module::Linkage::External);
                }
            }
        }
    }

    /// Generate a `__module_init_<prefix>` function that initializes heap-backed
    /// module globals at startup. Mirrors the cranelift backend's
    /// `generate_module_init` (common_backend.rs): for each entry in
    /// `global_init_strings / _arrays / _functions / _structs`, build the heap
    /// object via `rt_string_new` / `rt_array_new`(+push) / `rt_byte_array_new`
    /// (+`rt_typed_bytes_u8_push`) / `rt_alloc`, and store the handle into the
    /// global. The linker's `generate_init_caller` discovers `__module_init_*` and
    /// aggregates them into `__simple_call_module_inits`.
    #[cfg(feature = "llvm")]
    fn generate_module_init(&self, module_ir: &MirModule) -> Result<(), CompileError> {
        use inkwell::AddressSpace;

        if std::env::var("SIMPLE_DEBUG_MODINIT").is_ok() {
            eprintln!(
                "[modinit] prefix={:?} strings={} arrays={} fns={} structs={} globals={}",
                self.module_prefix,
                module_ir.global_init_strings.len(),
                module_ir.global_init_arrays.len(),
                module_ir.global_init_functions.len(),
                module_ir.global_init_structs.len(),
                module_ir.globals.len(),
            );
        }

        if module_ir.global_init_strings.is_empty()
            && module_ir.global_init_arrays.is_empty()
            && module_ir.global_init_functions.is_empty()
            && module_ir.global_init_structs.is_empty()
        {
            return Ok(());
        }

        let m = self.module.borrow();
        let Some(m) = m.as_ref() else {
            return Ok(());
        };
        let ctx = self.context_ref();
        let builder = ctx.create_builder();
        let i64_type = self.runtime_int_type();
        let ptr_type = ctx.ptr_type(AddressSpace::default());

        let init_name = crate::codegen::common_backend::module_init_symbol(self.module_prefix.as_deref());

        let void_type = ctx.void_type();
        let fn_type = void_type.fn_type(&[], false);
        let init_fn = m.add_function(&init_name, fn_type, None);
        // External so the linker's `starts_with("__module_init_")` symbol scan can
        // find it (an internal symbol would stay invisible → silent null globals).
        init_fn.set_linkage(inkwell::module::Linkage::External);
        let entry = ctx.append_basic_block(init_fn, "entry");
        builder.position_at_end(entry);

        // --- runtime helper declarations (lazy) ---
        let get_rt = |name: &str, nargs: usize| -> inkwell::values::FunctionValue<'static> {
            m.get_function(name).unwrap_or_else(|| {
                let params: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    std::iter::repeat_n(i64_type.into(), nargs).collect();
                let ft = i64_type.fn_type(&params, false);
                let f = m.add_function(name, ft, None);
                f.set_linkage(inkwell::module::Linkage::External);
                f
            })
        };

        // Build a static i8 data global for `bytes`, return its i64 pointer value.
        let mut str_const_counter: u32 = 0;
        let make_str_ptr =
            |bytes: &[u8], counter: &mut u32| -> Result<inkwell::values::IntValue<'static>, CompileError> {
                let cval = ctx.const_string(bytes, false);
                let name = format!("{}.str.{}", init_name, *counter);
                *counter += 1;
                let g = m.add_global(cval.get_type(), None, &name);
                g.set_initializer(&cval);
                g.set_constant(true);
                g.set_linkage(inkwell::module::Linkage::Private);
                let p = builder
                    .build_pointer_cast(g.as_pointer_value(), ptr_type, "str_p")
                    .map_err(|e| crate::error::factory::llvm_build_failed("str ptr cast", &e))?;
                builder
                    .build_ptr_to_int(p, i64_type, "str_pi")
                    .map_err(|e| crate::error::factory::llvm_build_failed("str ptrtoint", &e))
            };

        // Resolve the global symbol for `global_name`, trying the direct key then
        // the `<prefix>__<name>` mangled form (struct keys are not pre-mangled).
        let resolve_global = |global_name: &str| -> Option<inkwell::values::GlobalValue<'static>> {
            if let Some(g) = m.get_global(global_name) {
                return Some(g);
            }
            if let Some(prefix) = &self.module_prefix {
                let mangled = format!("{}__{}", prefix, global_name);
                if let Some(g) = m.get_global(&mangled) {
                    return Some(g);
                }
            }
            None
        };

        let store_to_global =
            |global_name: &str, val: inkwell::values::IntValue<'static>| -> Result<(), CompileError> {
                if let Some(g) = resolve_global(global_name) {
                    builder
                        .build_store(g.as_pointer_value(), val)
                        .map_err(|e| crate::error::factory::llvm_build_failed("init store", &e))?;
                }
                // If not found, the global lives in another module (cross-module) — skip.
                Ok(())
            };

        let call_i64 = |f: inkwell::values::FunctionValue<'static>,
                        args: &[inkwell::values::IntValue<'static>],
                        tag: &str|
         -> Result<inkwell::values::IntValue<'static>, CompileError> {
            let metas: Vec<inkwell::values::BasicMetadataValueEnum> = args.iter().map(|a| (*a).into()).collect();
            let cs = builder
                .build_call(f, &metas, tag)
                .map_err(|e| crate::error::factory::llvm_build_failed(tag, &e))?;
            Ok(cs
                .try_as_basic_value()
                .left()
                .map(|v| v.into_int_value())
                .unwrap_or_else(|| i64_type.const_int(0, false)))
        };

        // Emit a compact runtime fill loop `for i in 0..count { push(array, 0) }`
        // instead of `count` unrolled push calls. Used for all-zero array
        // initializers ([0; N]), where N unrolled calls previously produced
        // megabytes of dead .text (fd_table's seven [T; 65536] arrays = 8.5 MB,
        // pipe_compat's [u8; 262144] = 5 MB in the merged kernel). Semantics are
        // identical: the array handle is still created and filled to length N;
        // only the code size drops from O(N) to O(1).
        let emit_zero_fill_loop = |push_fn: inkwell::values::FunctionValue<'static>,
                                   array: inkwell::values::IntValue<'static>,
                                   count: inkwell::values::IntValue<'static>,
                                   tag: &str|
         -> Result<(), CompileError> {
            let preheader = builder
                .get_insert_block()
                .ok_or_else(|| CompileError::Codegen("zero-fill loop: no insert block".to_string()))?;
            let cond_bb = ctx.append_basic_block(init_fn, &format!("{tag}_cond"));
            let body_bb = ctx.append_basic_block(init_fn, &format!("{tag}_body"));
            let exit_bb = ctx.append_basic_block(init_fn, &format!("{tag}_exit"));
            builder
                .build_unconditional_branch(cond_bb)
                .map_err(|e| crate::error::factory::llvm_build_failed("zfill br cond", &e))?;
            builder.position_at_end(cond_bb);
            let phi = builder
                .build_phi(i64_type, &format!("{tag}_i"))
                .map_err(|e| crate::error::factory::llvm_build_failed("zfill phi", &e))?;
            let zero_idx = i64_type.const_int(0, false);
            phi.add_incoming(&[(&zero_idx, preheader)]);
            let idx = phi.as_basic_value().into_int_value();
            let cmp = builder
                .build_int_compare(inkwell::IntPredicate::SLT, idx, count, &format!("{tag}_cmp"))
                .map_err(|e| crate::error::factory::llvm_build_failed("zfill cmp", &e))?;
            builder
                .build_conditional_branch(cmp, body_bb, exit_bb)
                .map_err(|e| crate::error::factory::llvm_build_failed("zfill condbr", &e))?;
            builder.position_at_end(body_bb);
            let zero_elem = i64_type.const_int(0, false);
            let _ = call_i64(push_fn, &[array, zero_elem], tag)?;
            let next = builder
                .build_int_add(idx, i64_type.const_int(1, false), &format!("{tag}_next"))
                .map_err(|e| crate::error::factory::llvm_build_failed("zfill add", &e))?;
            phi.add_incoming(&[(&next, body_bb)]);
            builder
                .build_unconditional_branch(cond_bb)
                .map_err(|e| crate::error::factory::llvm_build_failed("zfill br back", &e))?;
            builder.position_at_end(exit_bb);
            Ok(())
        };

        // --- strings ---
        let mut sorted_strings: Vec<_> = module_ir.global_init_strings.iter().collect();
        sorted_strings.sort_by_key(|(name, _)| (*name).clone());
        if !sorted_strings.is_empty() {
            let string_new = get_rt("rt_string_new", 2);
            for (global_name, string_val) in sorted_strings {
                let bytes = string_val.as_bytes();
                let ptr = make_str_ptr(bytes, &mut str_const_counter)?;
                let len = i64_type.const_int(bytes.len() as u64, false);
                let rv = call_i64(string_new, &[ptr, len], "init_str")?;
                store_to_global(global_name, rv)?;
            }
        }

        // --- arrays ---
        let mut sorted_arrays: Vec<_> = module_ir.global_init_arrays.iter().collect();
        sorted_arrays.sort_by_key(|(name, _)| (*name).clone());
        for (global_name, init) in sorted_arrays {
            // All-zero initializers ([0; N]) get a compact fill loop instead of
            // N unrolled push calls (code size O(1) instead of O(N)).
            let all_zero =
                init.string_values.is_none() && !init.values.is_empty() && init.values.iter().all(|&v| v == 0);
            let element_count = init
                .string_values
                .as_ref()
                .map(|s| s.len())
                .unwrap_or(init.values.len());
            let capacity = i64_type.const_int(element_count as u64, false);
            let array_rv = if let Some(strings) = &init.string_values {
                let array_new = get_rt("rt_array_new", 1);
                let array_push = get_rt("rt_array_push", 2);
                let string_new = get_rt("rt_string_new", 2);
                let array = call_i64(array_new, &[capacity], "init_arr")?;
                for string_val in strings {
                    let bytes = string_val.as_bytes();
                    let ptr = make_str_ptr(bytes, &mut str_const_counter)?;
                    let len = i64_type.const_int(bytes.len() as u64, false);
                    let s = call_i64(string_new, &[ptr, len], "init_arr_str")?;
                    let _ = call_i64(array_push, &[array, s], "init_arr_push")?;
                }
                array
            } else if init.element_type == crate::hir::TypeId::U8 {
                let byte_array_new = get_rt("rt_byte_array_new", 1);
                let byte_push = get_rt("rt_typed_bytes_u8_push", 2);
                let array = call_i64(byte_array_new, &[capacity], "init_barr")?;
                if all_zero {
                    emit_zero_fill_loop(byte_push, array, capacity, "init_barr_zfill")?;
                } else {
                    for value in &init.values {
                        let byte = i64_type.const_int((*value & 0xff) as u64, false);
                        let _ = call_i64(byte_push, &[array, byte], "init_barr_push")?;
                    }
                }
                array
            } else if init.element_type == crate::hir::TypeId::BOOL {
                let array_new = get_rt("rt_array_new", 1);
                let array_push = get_rt("rt_array_push", 2);
                let value_bool = get_rt("rt_value_bool", 1);
                let array = call_i64(array_new, &[capacity], "init_bool_arr")?;
                for value in &init.values {
                    let raw = i64_type.const_int(u64::from(*value != 0), false);
                    let boxed = call_i64(value_bool, &[raw], "init_bool")?;
                    let _ = call_i64(array_push, &[array, boxed], "init_bool_arr_push")?;
                }
                array
            } else {
                let array_new = get_rt("rt_array_new", 1);
                let array_push = get_rt("rt_array_push", 2);
                let array = call_i64(array_new, &[capacity], "init_iarr")?;
                if all_zero {
                    // Boxed zero is `0 << 3` == 0, so pushing raw 0 is identical.
                    emit_zero_fill_loop(array_push, array, capacity, "init_iarr_zfill")?;
                } else {
                    for value in &init.values {
                        // Box small ints: raw << 3 (matches cranelift compile path).
                        let raw = i64_type.const_int(*value as u64, true);
                        let shift = i64_type.const_int(3, false);
                        let boxed = builder
                            .build_left_shift(raw, shift, "box")
                            .map_err(|e| crate::error::factory::llvm_build_failed("init box shl", &e))?;
                        let _ = call_i64(array_push, &[array, boxed], "init_iarr_push")?;
                    }
                }
                array
            };
            store_to_global(global_name, array_rv)?;
        }

        // --- function-closure globals ---
        let mut sorted_functions: Vec<_> = module_ir.global_init_functions.iter().collect();
        sorted_functions.sort_by_key(|(name, _)| (*name).clone());
        if !sorted_functions.is_empty() {
            let alloc = get_rt("rt_alloc", 1);
            for (global_name, func_name) in sorted_functions {
                let callee = m
                    .get_function(func_name)
                    .or_else(|| {
                        let sanitized = func_name.replace('.', "_dot_");
                        m.get_function(&sanitized)
                    })
                    .ok_or_else(|| {
                        CompileError::Codegen(format!(
                            "function global initializer '{}' references unknown function '{}'",
                            global_name, func_name
                        ))
                    })?;
                let closure_size = i64_type.const_int(16, false);
                let closure_pi = call_i64(alloc, &[closure_size], "init_closure")?;
                let closure_ptr = builder
                    .build_int_to_ptr(closure_pi, ptr_type, "closure_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("closure inttoptr", &e))?;
                let fn_addr = callee.as_global_value().as_pointer_value();
                let fn_addr_i = builder
                    .build_ptr_to_int(fn_addr, i64_type, "fn_addr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("fn ptrtoint", &e))?;
                let direct_marker = i64_type.const_int(0x5344_4952_4543_5446, false);
                builder
                    .build_store(closure_ptr, fn_addr_i)
                    .map_err(|e| crate::error::factory::llvm_build_failed("closure store fn", &e))?;
                let marker_slot = unsafe {
                    builder
                        .build_gep(i64_type, closure_ptr, &[i64_type.const_int(1, false)], "marker_slot")
                        .map_err(|e| crate::error::factory::llvm_build_failed("closure gep", &e))?
                };
                builder
                    .build_store(marker_slot, direct_marker)
                    .map_err(|e| crate::error::factory::llvm_build_failed("closure store marker", &e))?;
                store_to_global(global_name, closure_pi)?;
            }
        }

        // --- struct-literal globals ---
        let mut sorted_structs: Vec<_> = module_ir.global_init_structs.iter().collect();
        sorted_structs.sort_by_key(|(name, _)| (*name).clone());
        if !sorted_structs.is_empty() {
            let alloc = get_rt("rt_alloc", 1);
            for (global_name, init) in sorted_structs {
                let size = (init.fields.len().max(1) * 8) as u64;
                let struct_pi = call_i64(alloc, &[i64_type.const_int(size, false)], "init_struct")?;
                let struct_ptr = builder
                    .build_int_to_ptr(struct_pi, ptr_type, "struct_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("struct inttoptr", &e))?;
                for (idx, field) in init.fields.iter().enumerate() {
                    let field_val = match field {
                        crate::hir::HirGlobalFieldInit::Value(v) => i64_type.const_int(*v as u64, true),
                        crate::hir::HirGlobalFieldInit::Str(string_val) => {
                            let string_new = get_rt("rt_string_new", 2);
                            let bytes = string_val.as_bytes();
                            let ptr = make_str_ptr(bytes, &mut str_const_counter)?;
                            let len = i64_type.const_int(bytes.len() as u64, false);
                            call_i64(string_new, &[ptr, len], "init_struct_str")?
                        }
                        crate::hir::HirGlobalFieldInit::EmptyArray => {
                            let array_new = get_rt("rt_array_new", 1);
                            call_i64(array_new, &[i64_type.const_int(0, false)], "init_struct_arr")?
                        }
                    };
                    let slot = unsafe {
                        builder
                            .build_gep(
                                i64_type,
                                struct_ptr,
                                &[i64_type.const_int(idx as u64, false)],
                                "field_slot",
                            )
                            .map_err(|e| crate::error::factory::llvm_build_failed("struct gep", &e))?
                    };
                    builder
                        .build_store(slot, field_val)
                        .map_err(|e| crate::error::factory::llvm_build_failed("struct store", &e))?;
                }
                store_to_global(global_name, struct_pi)?;
            }
        }

        builder
            .build_return(None)
            .map_err(|e| crate::error::factory::llvm_build_failed("init return", &e))?;

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn declare_dot_aliases_for_methods(&self) {
        let m = self.module.borrow();
        let Some(m) = m.as_ref() else {
            return;
        };
        let mut originals: Vec<FunctionValue<'static>> = Vec::new();
        let mut func_opt = m.get_first_function();
        while let Some(f) = func_opt {
            originals.push(f);
            func_opt = f.get_next_function();
        }
        let _ = m;

        let m = self.module.borrow();
        let Some(m) = m.as_ref() else {
            return;
        };
        for f in originals {
            let Ok(name) = f.get_name().to_str() else {
                continue;
            };
            if !name.contains('.') || name.contains("_dot_") {
                continue;
            }
            let alias_name = name.replace('.', "_dot_");
            if m.get_function(&alias_name).is_none() {
                let alias = m.add_function(&alias_name, f.get_type(), None);
                // Cross-module callers can still reference the sanitized `_dot_`
                // spelling, so this alias must remain externally visible.
                alias.set_linkage(inkwell::module::Linkage::External);
            }
        }
    }

    #[cfg(feature = "llvm")]
    fn define_dot_alias_bodies(&self) -> Result<(), CompileError> {
        let m = self.module.borrow();
        let Some(m) = m.as_ref() else {
            return Ok(());
        };
        let mut aliases: Vec<FunctionValue<'static>> = Vec::new();
        let mut func_opt = m.get_first_function();
        while let Some(f) = func_opt {
            if f.count_basic_blocks() == 0 {
                if let Ok(name) = f.get_name().to_str() {
                    if name.contains("_dot_") {
                        aliases.push(f);
                    }
                }
            }
            func_opt = f.get_next_function();
        }
        let _ = m;

        let m = self.module.borrow();
        let Some(m) = m.as_ref() else {
            return Ok(());
        };
        for alias in aliases {
            let alias_name = alias
                .get_name()
                .to_str()
                .map_err(|_| CompileError::semantic("invalid alias function name"))?;
            let target_name = alias_name.replace("_dot_", ".");
            let Some(target) = m.get_function(&target_name) else {
                continue;
            };
            let builder = self.context_ref().create_builder();
            let entry = self.context_ref().append_basic_block(alias, "entry");
            builder.position_at_end(entry);
            let args: Vec<BasicMetadataValueEnum<'static>> = alias.get_param_iter().map(Into::into).collect();
            let call = builder
                .build_call(target, &args, "dot_alias")
                .map_err(|e| crate::error::factory::llvm_build_failed("dot alias call", &e))?;
            if alias.get_type().get_return_type().is_some() {
                let ret = call
                    .try_as_basic_value()
                    .left()
                    .ok_or_else(|| CompileError::semantic(format!("alias `{alias_name}` missing return value")))?;
                builder
                    .build_return(Some(&ret))
                    .map_err(|e| crate::error::factory::llvm_build_failed("dot alias return", &e))?;
            } else {
                builder
                    .build_return(None)
                    .map_err(|e| crate::error::factory::llvm_build_failed("dot alias return", &e))?;
            }
        }
        Ok(())
    }

    /// Get the LLVM target triple string for this target
    pub fn get_target_triple(&self) -> String {
        use simple_common::target::WasmRuntime;

        let arch_str = match self.target.arch {
            TargetArch::X86_64 => "x86_64",
            TargetArch::Aarch64 => "aarch64",
            TargetArch::X86 => "i686",
            TargetArch::Arm => "armv7",
            TargetArch::Riscv64 => "riscv64",
            TargetArch::Riscv32 => "riscv32",
            TargetArch::Wasm32 => "wasm32",
            TargetArch::Wasm64 => "wasm64",
        };

        // WASM targets use runtime-specific triples
        if matches!(self.target.arch, TargetArch::Wasm32 | TargetArch::Wasm64) {
            let runtime_str = match self.target.wasm_runtime {
                Some(WasmRuntime::Wasi) => "wasi",
                Some(WasmRuntime::Emscripten) => "unknown-emscripten",
                Some(WasmRuntime::Browser) | Some(WasmRuntime::Standalone) | None => "unknown-unknown",
            };
            return format!("{}-{}", arch_str, runtime_str);
        }

        let os_str = match self.target.os {
            TargetOS::Linux => "unknown-linux-gnu",
            TargetOS::MacOS => "apple-darwin",
            TargetOS::Windows => "pc-windows-msvc",
            TargetOS::FreeBSD => "unknown-freebsd",
            TargetOS::SimpleOS => "unknown-none-elf",
            TargetOS::Any | TargetOS::None => "unknown-unknown",
        };

        format!("{}-{}", arch_str, os_str)
    }

    /// Get pointer width (32 or 64 bits)
    pub fn pointer_width(&self) -> u32 {
        use simple_common::target::TargetArch;
        match self.target.arch {
            TargetArch::X86 | TargetArch::Arm | TargetArch::Riscv32 | TargetArch::Wasm32 => 32,
            TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::Riscv64 | TargetArch::Wasm64 => 64,
        }
    }

    /// Get the LLVM integer type used for RuntimeValue on this target.
    ///
    /// On 64-bit targets, RuntimeValue is i64 (tagged 64-bit value).
    /// On 32-bit targets, RuntimeValue is i32 (tagged 32-bit value).
    /// The C runtime defines `typedef int32_t RuntimeValue` on RV32 and
    /// `typedef int64_t RuntimeValue` on 64-bit, so this must match.
    #[cfg(feature = "llvm")]
    pub fn runtime_int_type(&self) -> inkwell::types::IntType<'static> {
        if self.pointer_width() == 32 {
            self.context_ref().i32_type()
        } else {
            self.context_ref().i64_type()
        }
    }

    #[cfg(feature = "llvm")]
    fn target_machine_for_module(
        &self,
        target_triple: &inkwell::targets::TargetTriple,
    ) -> Result<TargetMachine, CompileError> {
        use simple_common::target::{TargetArch, TargetOS};

        let triple = target_triple.as_str().to_string_lossy();
        let target = LlvmTarget::from_triple(target_triple)
            .map_err(|e| crate::error::factory::llvm_target_failed(&triple, &e))?;

        let is_freestanding = matches!(self.target.os, TargetOS::SimpleOS | TargetOS::None);
        let reloc_mode = if triple.contains("wasm") || is_freestanding {
            RelocMode::Static
        } else {
            RelocMode::PIC
        };

        let is_riscv = matches!(self.target.arch, TargetArch::Riscv32 | TargetArch::Riscv64);
        let code_model = if is_freestanding && is_riscv {
            CodeModel::Medium
        } else {
            CodeModel::Default
        };

        let freestanding_riscv32_features = std::env::var("SIMPLE_RISCV32_LLVM_FEATURES").ok();
        let features = match self.target.arch {
            TargetArch::Riscv32 if is_freestanding => freestanding_riscv32_features.as_deref().unwrap_or("+m,+a,+c"),
            TargetArch::Riscv32 => "+m,+a,+c",
            TargetArch::Riscv64 => "+m,+a,+c",
            _ => "",
        };

        let host_cpu_name;
        let cpu_name = if matches!(self.cpu, TargetCpu::Native) {
            host_cpu_name = TargetMachine::get_host_cpu_name().to_string();
            host_cpu_name.as_str()
        } else {
            self.cpu
                .llvm_cpu_name(self.target.arch)
                .unwrap_or(match self.target.arch {
                    TargetArch::X86_64 => "x86-64-v3",
                    TargetArch::Aarch64 => "generic",
                    TargetArch::X86 => "i686",
                    TargetArch::Arm => "generic",
                    TargetArch::Riscv64 => "generic-rv64",
                    TargetArch::Riscv32 => "generic-rv32",
                    TargetArch::Wasm32 | TargetArch::Wasm64 => "generic",
                })
        };

        target
            .create_target_machine(
                target_triple,
                cpu_name,
                features,
                self.llvm_optimization_level(),
                reloc_mode,
                code_model,
            )
            .ok_or_else(crate::error::factory::llvm_target_machine_failed)
    }

    /// Create an LLVM module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_module(&self, name: &str) -> Result<(), CompileError> {
        use simple_common::target::{TargetArch, WasmRuntime};

        LlvmTarget::initialize_all(&InitializationConfig::default());

        // Create module with the context
        let module = self.context_ref().create_module(name);

        // Set target triple
        let triple = self.get_target_triple();
        let target_triple = inkwell::targets::TargetTriple::create(&triple);
        module.set_triple(&target_triple);

        let target_machine = self.target_machine_for_module(&target_triple)?;
        module.set_data_layout(&target_machine.get_target_data().get_data_layout());

        // Declare WASI imports for wasm32-wasi / wasm64-wasi targets
        if matches!(self.target.arch, TargetArch::Wasm32 | TargetArch::Wasm64) {
            if matches!(self.target.wasm_runtime, Some(WasmRuntime::Wasi)) {
                #[cfg(feature = "wasm-wasi")]
                crate::codegen::llvm::wasm_imports::declare_wasi_imports(&module)?;
            }
        }

        *self.module.borrow_mut() = Some(module);

        // Create builder
        let builder = self.context_ref().create_builder();
        *self.builder.borrow_mut() = Some(builder);

        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_module(&self, _name: &str) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Create LLVM function signature (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_function_signature(
        &self,
        name: &str,
        param_types: &[TypeId],
        return_type: &TypeId,
    ) -> Result<FunctionValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        // Map parameter types
        let param_llvm: Result<Vec<_>, _> = param_types
            .iter()
            .map(|ty| self.llvm_type(ty).map(|t| t.into()))
            .collect();
        let param_llvm = param_llvm?;

        // Map return type
        let ret_llvm = self.llvm_type(return_type)?;

        // Create function type
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => t.fn_type(&param_llvm, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&param_llvm, false),
            BasicTypeEnum::PointerType(t) => t.fn_type(&param_llvm, false),
            _ => return Err(crate::error::factory::unsupported_return_type()),
        };

        // Check for existing declaration to avoid creating duplicates with suffixed names.
        // When a function was already pre-declared (e.g., by runtime function loop), reuse it.
        if let Some(existing) = module.get_function(name) {
            return Ok(existing);
        }
        Ok(module.add_function(name, fn_type, None))
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_function_signature(
        &self,
        _name: &str,
        _param_types: &[TypeId],
        _return_type: &TypeId,
    ) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Declare a function with appropriate linkage.
    /// Functions with bodies get WeakAny linkage (like Cranelift's Preemptible) to avoid
    /// duplicate symbol errors in multi-file builds with --no-mangle.
    /// Functions without bodies (extern declarations) get External linkage.
    #[cfg(feature = "llvm")]
    pub fn declare_function_with_linkage(
        &self,
        name: &str,
        param_types: &[TypeId],
        return_type: &TypeId,
        has_body: bool,
    ) -> Result<(), CompileError> {
        let func = self.create_function_signature(name, param_types, return_type)?;
        if has_body {
            // Module-qualified names (containing "__") use External linkage so they
            // override weak stubs.  Bare names use WeakAny to avoid duplicate-symbol
            // errors when the same bare name appears in multiple modules.
            // The linker uses --allow-multiple-definition to handle the rare case of
            // genuinely duplicated mangled names across modules.
            if name.contains("__") || name == "spl_main" {
                func.set_linkage(inkwell::module::Linkage::External);
            } else {
                func.set_linkage(inkwell::module::Linkage::WeakAny);
            }
        } else {
            func.set_linkage(inkwell::module::Linkage::External);
        }
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn declare_function_with_linkage(
        &self,
        _name: &str,
        _param_types: &[TypeId],
        _return_type: &TypeId,
        _has_body: bool,
    ) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Get LLVM IR as string (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;
        Ok(module.print_to_string().to_string())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Verify the module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn verify(&self) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        module
            .verify()
            .map_err(|e| crate::error::factory::llvm_verification_failed(&e))?;
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn verify(&self) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Take ownership of the LLVM module (for JIT execution engine creation).
    #[cfg(feature = "llvm")]
    pub fn take_module(&self) -> Option<Module<'static>> {
        self.module.borrow_mut().take()
    }

    /// Emit object code from the module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        // Initialize LLVM targets
        LlvmTarget::initialize_all(&InitializationConfig::default());

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        // Get target triple
        let triple = self.get_target_triple();
        let target_triple = inkwell::targets::TargetTriple::create(&triple);

        let target_machine = self.target_machine_for_module(&target_triple)?;
        module.set_data_layout(&target_machine.get_target_data().get_data_layout());

        self.optimize_module_ir(module, &target_machine)?;

        // Emit object file to memory buffer
        let buffer = target_machine
            .write_to_memory_buffer(module, FileType::Object)
            .map_err(|e| crate::error::factory::llvm_emit_failed("object file", &e))?;

        Ok(buffer.as_slice().to_vec())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }
}

#[cfg(all(test, feature = "llvm"))]
mod tests {
    use super::LlvmBackend;
    use crate::codegen::backend_trait::NativeBackend;
    use crate::hir::TypeId;
    use crate::mir::{MirFunction, MirInst, MirModule, Terminator, VReg};
    use simple_common::target::{Target, TargetArch, TargetOS};
    use simple_parser::ast::Visibility;
    use std::collections::HashMap;
    use std::sync::Arc;

    #[test]
    fn create_module_emits_target_triple_and_datalayout() {
        let backend = LlvmBackend::new(Target::new(TargetArch::X86_64, TargetOS::Linux)).unwrap();

        backend.create_module("layout_test").unwrap();
        let ir = backend.get_ir().unwrap();

        assert!(ir.contains("target triple"));
        assert!(ir.contains("x86_64"));
        assert!(ir.contains("target datalayout"));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn llvm_aot_function_sections_allow_strict_dead_reference_gc() {
        use crate::mir::CallTarget;
        use object::{Object, ObjectSection};

        let mut live = MirFunction::new("live".to_string(), TypeId::I64, Visibility::Public);
        live.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 7,
        });
        live.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        let mut dead = MirFunction::new("dead".to_string(), TypeId::I64, Visibility::Public);
        dead.blocks[0].instructions.push(MirInst::Call {
            dest: Some(VReg(0)),
            target: CallTarget::Pure("missing_dead_symbol".to_string()),
            args: vec![],
        });
        dead.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        let mut mir = MirModule::new();
        mir.functions = vec![live, dead];
        let mut backend = LlvmBackend::new(Target::new(TargetArch::host(), TargetOS::Linux)).unwrap();
        let object_bytes = backend.compile(&mir).unwrap();

        let object = object::File::parse(object_bytes.as_slice()).unwrap();
        let function_sections = object
            .sections()
            .filter_map(|section| section.name().ok())
            .filter(|name| name.starts_with(".text.simple."))
            .collect::<Vec<_>>();
        assert!(
            function_sections.len() >= 2,
            "expected distinct LLVM function sections, got {function_sections:?}"
        );

        let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
        if std::process::Command::new(&cc).arg("--version").output().is_err() {
            return;
        }
        let temp = tempfile::tempdir().unwrap();
        let llvm_object = temp.path().join("functions.o");
        std::fs::write(&llvm_object, object_bytes).unwrap();

        for (entry, should_link) in [("live", true), ("dead", false)] {
            let main_source = temp.path().join(format!("main_{entry}.c"));
            let output = temp.path().join(format!("probe_{entry}"));
            std::fs::write(
                &main_source,
                format!("extern long {entry}(void); int main(void) {{ return (int){entry}(); }}\n"),
            )
            .unwrap();
            let link = std::process::Command::new(&cc)
                .arg(&main_source)
                .arg(&llvm_object)
                .arg("-Wl,--gc-sections")
                .arg("-o")
                .arg(&output)
                .output()
                .unwrap();
            assert_eq!(
                link.status.success(),
                should_link,
                "{entry} link status mismatch: {}",
                String::from_utf8_lossy(&link.stderr)
            );
        }
    }

    #[test]
    fn global_load_declares_only_exact_known_imported_functions() {
        let mut backend = LlvmBackend::new(Target::new(TargetArch::X86_64, TargetOS::Linux)).unwrap();
        backend.create_module("function_values").unwrap();
        backend.set_fn_arities(Arc::new(HashMap::from([
            ("backend__backend__common__ascii_utils__char_to_ascii".to_string(), 1),
            ("nogc_sync_mut__io__cuda_sffi__cuda_available".to_string(), 0),
        ])));

        let mut caller = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        caller.blocks[0].instructions.push(MirInst::GlobalLoad {
            dest: VReg(0),
            global_name: "backend__backend__common__ascii_utils__char_to_ascii".to_string(),
            ty: TypeId::I64,
        });
        caller.blocks[0].instructions.push(MirInst::GlobalLoad {
            dest: VReg(1),
            global_name: "nogc_sync_mut__io__cuda_sffi__cuda_available".to_string(),
            ty: TypeId::I64,
        });
        caller.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        let mut unresolved = MirFunction::new("unresolved".to_string(), TypeId::I64, Visibility::Private);
        unresolved.blocks[0].instructions.push(MirInst::GlobalLoad {
            dest: VReg(0),
            global_name: "self".to_string(),
            ty: TypeId::I64,
        });
        unresolved.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        let mut mir = MirModule::new();
        mir.functions = vec![caller.clone(), unresolved];
        backend.declare_globals(&mir);
        backend.compile_function(&caller).unwrap();

        let ir = backend.get_ir().unwrap();
        assert!(
            ir.contains("declare i64 @backend__backend__common__ascii_utils__char_to_ascii(i64)"),
            "{ir}"
        );
        assert!(
            ir.contains("declare i64 @nogc_sync_mut__io__cuda_sffi__cuda_available()"),
            "{ir}"
        );
        assert!(!ir.contains("@self"), "{ir}");
        backend.verify().unwrap();
    }
}

impl NativeBackend for LlvmBackend {
    fn target(&self) -> &Target {
        &self.target
    }

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        let module_name = module.name.as_deref().unwrap_or("module");
        self.create_module(module_name)?;

        // Pre-declare runtime functions with correct signatures.
        // This prevents compile_call from creating wrong declarations when
        // MIR calls a runtime function with a different number of arguments
        // (e.g., rt_array_new called with 0 args in MIR vs 1 arg actual).
        //
        // Skip functions that the LLVM backend declares manually with ptr types
        // (Cranelift uses i64 for everything, but LLVM distinguishes ptr from i64).
        let referenced_function_names = crate::codegen::common_backend::referenced_call_names(&module.functions);
        #[cfg(feature = "llvm")]
        {
            let m = self.module.borrow();
            if let Some(m) = m.as_ref() {
                let rv_type = self.runtime_int_type();
                let defined_function_names: std::collections::HashSet<&str> = module
                    .functions
                    .iter()
                    .filter(|func| !func.blocks.is_empty())
                    .map(|func| func.name.as_str())
                    .collect();

                for spec in crate::codegen::runtime_sffi::RUNTIME_FUNCS {
                    if !referenced_function_names.contains(spec.name)
                        && !crate::codegen::common_backend::runtime_symbol_is_codegen_root(spec.name)
                    {
                        continue;
                    }
                    if defined_function_names.contains(spec.name) {
                        continue;
                    }
                    // Skip if already declared
                    if m.get_function(spec.name).is_some() {
                        continue;
                    }

                    // Only pre-declare functions with ALL i64 params and i64 return.
                    // (The Cranelift spec uses I64 universally; on 32-bit targets we
                    // map these to the RuntimeValue width via rv_type.)
                    // Functions with i8/i32/f64 params would cause type mismatches
                    // when compile_call passes rv_type args. Those functions will be
                    // declared on-demand by compile_call with matching arg types,
                    // and the indirect call path handles arity mismatches.
                    let all_i64_params = spec.params.iter().all(|ty| *ty == cranelift_codegen::ir::types::I64);
                    let i64_return = spec.returns.len() == 1 && spec.returns[0] == cranelift_codegen::ir::types::I64;
                    let void_return = spec.returns.is_empty();

                    // Only pre-declare functions with ALL i64 params and i64 return.
                    // Skip void-return functions — they may clash with user-defined
                    // functions that return values (e.g. debug_stubs.spl redefines
                    // rt_fault_* to return bool). The arity-mismatch path in
                    // compile_call handles void functions fine.
                    if !all_i64_params || !i64_return {
                        continue;
                    }

                    let params: Vec<inkwell::types::BasicMetadataTypeEnum> =
                        spec.params.iter().map(|_| rv_type.into()).collect();

                    let fn_type = rv_type.fn_type(&params, false);
                    let f = m.add_function(spec.name, fn_type, None);
                    f.set_linkage(inkwell::module::Linkage::External);
                }
            }
        }

        #[cfg(feature = "llvm")]
        self.declare_globals(module);

        // First pass: forward-declare all function signatures
        // This is necessary so that functions can call each other regardless of compilation order
        self.function_return_types.borrow_mut().clear();
        for func in &module.functions {
            let has_body = !func.blocks.is_empty();
            if !has_body && !referenced_function_names.contains(func.name.as_str()) {
                continue;
            }
            let declared_slots = func.params.len() + func.locals.len();
            let mut max_local_index = None;
            for block in &func.blocks {
                for inst in &block.instructions {
                    if let crate::mir::MirInst::LocalAddr { local_index, .. } = inst {
                        max_local_index =
                            Some(max_local_index.map_or(*local_index, |cur: usize| cur.max(*local_index)));
                    }
                }
            }
            let implicit_slots = match max_local_index {
                Some(max_idx) if max_idx + 1 > declared_slots => (max_idx + 1) - declared_slots,
                _ => 0,
            };
            let mut param_types = vec![crate::hir::TypeId::I64; implicit_slots];
            param_types.extend(func.params.iter().map(|p| p.ty));
            // Resolve through import_map/use_map to get the mangled name
            // (e.g., "exit" -> "app__io__cli_ops__exit") to avoid symbol collisions
            let resolved_name = self
                .use_map
                .get(&func.name)
                .or_else(|| self.import_map.get(&func.name))
                .map(|s| s.as_str())
                .unwrap_or(&func.name);
            self.function_return_types
                .borrow_mut()
                .insert(resolved_name.to_string(), func.return_type);
            self.function_return_types
                .borrow_mut()
                .insert(func.name.clone(), func.return_type);
            self.declare_function_with_linkage(resolved_name, &param_types, &func.return_type, has_body)?;
            #[cfg(feature = "llvm")]
            if has_body {
                let module_ref = self.module.borrow();
                if let Some(m) = module_ref.as_ref() {
                    if let Some(llvm_func) = m.get_function(resolved_name) {
                        self.apply_function_optimization_attrs(llvm_func, &func.attributes);
                    }
                }
            }
        }
        #[cfg(feature = "llvm")]
        self.declare_dot_aliases_for_methods();

        // Second pass: compile all function bodies
        for func in &module.functions {
            self.compile_function(func)?;
        }
        #[cfg(feature = "llvm")]
        self.define_dot_alias_bodies()?;

        // Emit the per-module init function for heap-typed module globals
        // (strings/arrays/structs/closures). The linker aggregates all
        // `__module_init_*` into `__simple_call_module_inits`, run before entry.
        #[cfg(feature = "llvm")]
        self.generate_module_init(module)?;

        // Fix linkage after compilation:
        // 1. Declarations (no body) must have External linkage, not WeakAny.
        // 2. spl_main (entry point) must have Global linkage to beat the weak stub.
        #[cfg(feature = "llvm")]
        {
            let m = self.module.borrow();
            if let Some(m) = m.as_ref() {
                let emit_elf_function_sections = matches!(
                    self.target.os,
                    TargetOS::Linux | TargetOS::FreeBSD | TargetOS::SimpleOS | TargetOS::None
                );
                let mut body_section_index = 0usize;
                let mut func_opt = m.get_first_function();
                while let Some(f) = func_opt {
                    if f.count_basic_blocks() == 0 {
                        // No body — must be External
                        f.set_linkage(inkwell::module::Linkage::External);
                    } else {
                        // ELF section GC works at section granularity. Keep every
                        // body in its own section so an unreachable generic/helper
                        // body cannot retain its unresolved imports at final link.
                        if emit_elf_function_sections {
                            f.set_section(Some(&format!(".text.simple.{body_section_index}")));
                            body_section_index += 1;
                        }
                        if f.get_name().to_str() == Ok("spl_main") {
                            // Entry point must be a strong (Global) symbol so the linker
                            // prefers it over the weak spl_main in the C main stub.
                            f.set_linkage(inkwell::module::Linkage::External);
                        }
                    }
                    func_opt = f.get_next_function();
                }
            }
        }

        self.verify()?;
        self.emit_object(module)
    }

    fn name(&self) -> &'static str {
        "llvm"
    }

    fn supports_target(target: &Target) -> bool {
        // LLVM supports all targets including WASM
        use simple_common::target::TargetArch;
        matches!(
            target.arch,
            TargetArch::X86_64
                | TargetArch::Aarch64
                | TargetArch::X86
                | TargetArch::Arm
                | TargetArch::Riscv64
                | TargetArch::Riscv32
                | TargetArch::Wasm32
                | TargetArch::Wasm64
        )
    }
}
