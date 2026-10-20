//! Boxed-entry thunks for the runtime-facing closure convention.
//!
//! # Two conventions, one closure object
//!
//! A lambda outlined by [`super::shared::expand_with_outlined`] is compiled with
//! its REAL types: `fn(ctx: i64, p1: T1, ..) -> R`. That is the fast,
//! JIT-internal convention and nothing outside this backend can call it — the
//! runtime's collection helpers (`rt_array_map`, `rt_array_filter`,
//! `rt_array_find`, `rt_dict_*`, ...) all `transmute` a closure's `func_ptr` to
//!
//! ```text
//! extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue
//! ```
//!
//! i.e. every value crossing the boundary is a TAGGED `RuntimeValue`.
//!
//! This module emits, for each outlined lambda `L`, a companion
//! `L$boxed` with exactly that signature. It unboxes each tagged argument to
//! the parameter type `L` was compiled with, calls `L`, and boxes the result
//! back. `compile_closure_create` stores `L$boxed` — never `L` — as the
//! `RuntimeClosure`'s `func_ptr`, so ANY caller (runtime helper, another
//! JIT-compiled function, an escaped/stored/returned closure value) reaches the
//! body through one uniform, tag-correct door.
//!
//! Transport notes:
//! - `rt_value_unbox_int` is TOTAL and bit-preserving: a tagged int decodes,
//!   and a heap handle (text, struct, array, enum) passes through verbatim. So
//!   a `text`-valued argument survives an `i64`-declared parameter slot
//!   unchanged; only what the BODY then does with it can be wrong, which is the
//!   pre-existing undeclared-parameter-type defect, not an ABI question.
//! - `BOOL` crosses as a full-width tagged value (`rt_value_bool` /
//!   `rt_value_unbox_int` + `icmp`), never as a bare `i8`. A raw `i8` in a
//!   register slot the caller reads as a 64-bit `RuntimeValue` is what SIGSEGV'd
//!   the previous attempt.

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature, UserFuncName};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};

use crate::hir::TypeId;
use crate::mir::MirFunction;

use super::common_backend::{BackendError, BackendResult, CodegenBackend};
use super::shared::build_mir_signature;

/// Suffix appended to an outlined lambda's name to form its boxed entry.
pub const BOXED_ENTRY_SUFFIX: &str = "$boxed";

/// Name of the boxed entry thunk for the outlined lambda `lambda_name`.
pub fn boxed_entry_name(lambda_name: &str) -> String {
    format!("{lambda_name}{BOXED_ENTRY_SUFFIX}")
}

/// Byte offset of capture slot 0 inside a `RuntimeClosure`.
///
/// `#[repr(C)] struct RuntimeClosure { header: HeapHeader /*8*/, func_ptr: *const u8 /*8*/,
/// capture_count: u32, reserved: u32 }` — captures follow. Kept only for
/// documentation/assertions; capture access itself goes through
/// `rt_closure_get_capture` / `rt_closure_set_capture` so the tagged handle is
/// untagged by the runtime rather than by open-coded pointer arithmetic here.
pub const RUNTIME_CLOSURE_CAPTURE_BASE: i32 = 24;

/// True when `func` is an outlined LAMBDA body (as opposed to an outlined
/// actor/generator/future body, which have their own conventions).
pub fn is_outlined_lambda(func: &MirFunction) -> bool {
    func.outlined_bodies
        .get(&func.entry_block)
        .is_some_and(|meta| meta.is_lambda)
}

/// Does a tagged `RuntimeValue` need a decode step to reach `ty`'s raw
/// representation? Heap-shaped and unknown types are carried verbatim.
fn is_raw_scalar(ty: TypeId) -> bool {
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
            | TypeId::BOOL
    )
}

impl<M: Module> CodegenBackend<M> {
    /// Declare and define one `L$boxed` thunk per outlined lambda in
    /// `functions`. Must run AFTER `declare_functions`, so `func_ids` already
    /// carries every `L`.
    pub fn emit_boxed_closure_entries(&mut self, functions: &[MirFunction]) -> BackendResult<()> {
        let lambdas: Vec<MirFunction> = functions
            .iter()
            .filter(|f| !f.blocks.is_empty() && is_outlined_lambda(f))
            .cloned()
            .collect();
        for lambda in &lambdas {
            self.emit_one_boxed_entry(lambda)?;
        }
        Ok(())
    }

    /// Declare and define one `F$boxed` thunk per NAMED function that some
    /// body in `mir` loads as a first-class value (`val g = add_one`,
    /// `Port(tokenize_fn: my_tok)`). A named fn has no ctx slot, so the thunk
    /// drops the closure handle and forwards only the user arguments; the
    /// `GlobalLoad` site then wraps `F$boxed` in a zero-capture
    /// `rt_closure_new` object, giving a bare function reference the SAME
    /// representation as a lambda value. Must run AFTER `declare_functions`.
    ///
    /// A function defined in ANOTHER unit gets the same thunk here, built from
    /// the `HirType::Function` its value carries and calling the import through
    /// a relocation to its symbol. Before this the load fell to a bare
    /// `rt_alloc` "direct record" that `rt_closure_func_ptr` rejects, so every
    /// call through the value jumped to address 0.
    pub fn emit_boxed_fn_value_entries(
        &mut self,
        mir: &crate::mir::MirModule,
        functions: &[MirFunction],
    ) -> BackendResult<()> {
        let trace = std::env::var("SIMPLE_NATIVE_BUILD_RUST_TRACE").ok().as_deref() == Some("1");
        for name in named_fn_value_targets(mir) {
            if trace {
                eprintln!("[rust-jit] fn-value boxed entry for {name}");
            }
            let Some(func) = functions.iter().find(|f| f.name == name) else {
                continue;
            };
            self.emit_boxed_entry_for(func, false)?;
        }
        for (name, params, ret) in imported_fn_value_targets(mir) {
            if trace {
                eprintln!("[rust-jit] fn-value boxed entry for imported {name}");
            }
            self.emit_boxed_import_entry(&name, params, ret)?;
        }
        // Module-level `val G: fn(..) = F`: `generate_module_init` stores a
        // zero-capture closure over `F$boxed` in `G`, so every function named
        // by a global initializer needs its thunk too. The name is already
        // resolved (mangle.rs); the global's own type carries the arity.
        let mut init_functions: Vec<(&String, &String)> = mir.global_init_functions.iter().collect();
        init_functions.sort();
        for (global_name, func_name) in init_functions {
            if mir.extern_fn_names.contains(func_name.as_str()) {
                continue; // extern entry points keep the raw direct record
            }
            if let Some(func) = functions.iter().find(|f| &f.name == func_name && !f.blocks.is_empty()) {
                self.emit_boxed_entry_for(func, false)?;
                continue;
            }
            let fn_ty = mir
                .globals
                .iter()
                .find(|(name, _, _)| name == global_name)
                .and_then(|(_, ty, _)| mir.type_registry.get(*ty));
            if let Some(crate::hir::HirType::Function { params, ret }) = fn_ty {
                if trace {
                    eprintln!("[rust-jit] fn-value boxed entry for global init {global_name} = {func_name}");
                }
                self.emit_boxed_import_entry_resolved(func_name, Some(func_name.clone()), params.clone(), *ret)?;
            }
            // No thunk: `generate_module_init` refuses the initializer.
        }
        Ok(())
    }

    fn emit_one_boxed_entry(&mut self, lambda: &MirFunction) -> BackendResult<()> {
        self.emit_boxed_entry_for(lambda, true)
    }

    /// `has_ctx`: the target's slot 0 is the closure ctx pointer (outlined
    /// lambda) and receives the handle; otherwise (named fn) the handle is
    /// dropped and every target param is a user param.
    fn emit_boxed_entry_for(&mut self, lambda: &MirFunction, has_ctx: bool) -> BackendResult<()> {
        let raw_name = boxed_entry_name(&lambda.name);
        if self.func_ids.contains_key(&raw_name) {
            return Ok(());
        }
        let Some(&target_id) = self.func_ids.get(&lambda.name) else {
            // The lambda body itself was not declared; nothing to wrap. The
            // ClosureCreate site falls back to its own resolution path.
            return Ok(());
        };

        // The outlined lambda's params are [ctx, p1..pn]; the boxed entry has
        // the same arity but every slot is a tagged RuntimeValue (i64).
        let target_sig = build_mir_signature(lambda, self.module.isa().default_call_conv());
        let skip = usize::from(has_ctx);
        let user_params: Vec<TypeId> = lambda.params.iter().skip(skip).map(|p| p.ty).collect();
        self.emit_boxed_thunk(raw_name, target_id, target_sig, user_params, lambda.return_type, has_ctx, false)
    }

    /// `F$boxed` for a function this unit only imports. The target's ABI is
    /// the uniform user-function one (`build_mir_signature`: every parameter
    /// and the result an `i64`), so the arity from the value's
    /// `HirType::Function` is all the signature needs. The import may already
    /// be declared with a placeholder signature (`declare_globals` uses
    /// `(i64) -> i64` for every use-map function), so the thunk calls the
    /// symbol's ADDRESS with the real signature rather than that declaration.
    /// No symbol at all is a build error -- never a NULL function value.
    fn emit_boxed_import_entry(&mut self, name: &str, user_params: Vec<TypeId>, ret_ty: TypeId) -> BackendResult<()> {
        let resolved = self.use_map.get(name).or_else(|| self.import_map.get(name)).cloned();
        self.emit_boxed_import_entry_resolved(name, resolved, user_params, ret_ty)
    }

    /// `emit_boxed_import_entry` with the import's symbol already resolved
    /// (`None`: unresolvable). The thunk is keyed by `name`.
    fn emit_boxed_import_entry_resolved(
        &mut self,
        name: &str,
        resolved: Option<String>,
        user_params: Vec<TypeId>,
        ret_ty: TypeId,
    ) -> BackendResult<()> {
        let raw_name = boxed_entry_name(name);
        if self.func_ids.contains_key(&raw_name) {
            return Ok(());
        }
        if let Some(resolved) = &resolved {
            let sanitized = self.sanitize_symbol(resolved);
            if self.data_exports.contains(resolved) || self.data_exports.contains(&sanitized) {
                // A function-typed DATA export (`val f = g` in the other unit):
                // GlobalLoad reads the stored closure value; no thunk.
                return Ok(());
            }
        }
        let call_conv = self.module.isa().default_call_conv();
        let mut target_sig = Signature::new(call_conv);
        for _ in &user_params {
            target_sig.params.push(AbiParam::new(types::I64));
        }
        target_sig.returns.push(AbiParam::new(types::I64));
        let known = self
            .func_ids
            .get(name)
            .or_else(|| self.func_ids.get(&self.sanitize_symbol(name)))
            .copied();
        let target_id = match known {
            Some(id) => id,
            None => {
                let Some(resolved) = resolved else {
                    return Err(BackendError::ModuleError(format!(
                        "function `{name}` is used as a value but is neither defined in this unit nor \
                         resolvable as an import"
                    )));
                };
                let symbol = self.sanitize_symbol(&resolved);
                // Already declared under another key (any signature): reuse
                // it; the thunk calls through the address with `target_sig`.
                let id = match self.module.get_name(&symbol) {
                    Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                    _ => self
                        .module
                        .declare_function(&symbol, Linkage::Import, &target_sig)
                        .map_err(|e| BackendError::ModuleError(format!("declare import {symbol}: {e}")))?,
                };
                self.func_ids.insert(name.to_string(), id);
                id
            }
        };
        self.emit_boxed_thunk(raw_name, target_id, target_sig, user_params, ret_ty, false, true)
    }

    /// Define `raw_name` (`(closure, tagged...) -> tagged`) forwarding to
    /// `target_id` with `target_sig`. `via_addr`: call the target through its
    /// address (one relocation to the symbol) with `target_sig`, instead of
    /// through the module-level declaration's own signature.
    #[allow(clippy::too_many_arguments)] // reason: one thunk shape, two target kinds
    fn emit_boxed_thunk(
        &mut self,
        raw_name: String,
        target_id: cranelift_module::FuncId,
        target_sig: Signature,
        user_params: Vec<TypeId>,
        ret_ty: TypeId,
        has_ctx: bool,
        via_addr: bool,
    ) -> BackendResult<()> {
        let skip = usize::from(has_ctx);
        let mut sig = Signature::new(self.module.isa().default_call_conv());
        sig.params.push(AbiParam::new(types::I64)); // closure handle
        for _ in &user_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let symbol = match &self.module_prefix {
            Some(prefix) => format!("{prefix}__{raw_name}"),
            None => raw_name.clone(),
        };
        let func_id = self
            .module
            .declare_function(&symbol, Linkage::Local, &sig)
            .map_err(|e| BackendError::ModuleError(format!("declare {symbol}: {e}")))?;
        self.func_ids.insert(raw_name.clone(), func_id);

        // Runtime helpers this thunk may need. Declared up-front so the
        // borrow of `self.runtime_funcs` does not overlap the builder.
        let helper_ids = BoxHelperIds::resolve(self, &user_params, ret_ty)?;

        self.module.clear_context(&mut self.ctx);
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let target_ref = self.module.declare_func_in_func(target_id, &mut self.ctx.func);
            let helpers = helper_ids.in_func(&mut self.module, &mut self.ctx.func);

            let mut fb_ctx = FunctionBuilderContext::new();
            let mut b = FunctionBuilder::new(&mut self.ctx.func, &mut fb_ctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);

            let params: Vec<_> = b.block_params(entry).to_vec();
            let closure = params[0];

            let mut call_args = if has_ctx { vec![closure] } else { Vec::new() };
            for (i, ty) in user_params.iter().enumerate() {
                let tagged = params[i + 1];
                // Cranelift type the target actually declares for this slot
                // (offset by one when slot 0 is the ctx pointer).
                let want = target_sig.params[i + skip].value_type;
                call_args.push(unbox_arg(&mut b, &helpers, tagged, *ty, want));
            }

            let call = if via_addr {
                let addr = b.ins().func_addr(types::I64, target_ref);
                let sig_ref = b.import_signature(target_sig.clone());
                b.ins().call_indirect(sig_ref, addr, &call_args)
            } else {
                b.ins().call(target_ref, &call_args)
            };
            let results = b.inst_results(call).to_vec();
            let boxed = if results.is_empty() {
                // VOID lambda: answer tagged NIL (raw word 3).
                b.ins().iconst(types::I64, 3)
            } else {
                box_result(&mut b, &helpers, results[0], ret_ty)
            };
            b.ins().return_(&[boxed]);
            b.finalize();
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| BackendError::ModuleError(format!("define {symbol}: {e}")))?;
        self.module.clear_context(&mut self.ctx);
        Ok(())
    }
}

/// FuncIds of the boxing helpers, resolved before the function builder borrows
/// `self.ctx`.
struct BoxHelperIds {
    unbox_int: Option<cranelift_module::FuncId>,
    as_float: Option<cranelift_module::FuncId>,
    box_int: Option<cranelift_module::FuncId>,
    box_float: Option<cranelift_module::FuncId>,
    box_bool: Option<cranelift_module::FuncId>,
}

struct BoxHelperRefs {
    unbox_int: Option<cranelift_codegen::ir::FuncRef>,
    as_float: Option<cranelift_codegen::ir::FuncRef>,
    box_int: Option<cranelift_codegen::ir::FuncRef>,
    box_float: Option<cranelift_codegen::ir::FuncRef>,
    box_bool: Option<cranelift_codegen::ir::FuncRef>,
}

impl BoxHelperIds {
    fn resolve<M: Module>(backend: &CodegenBackend<M>, params: &[TypeId], ret: TypeId) -> BackendResult<Self> {
        let need = |pred: &dyn Fn(TypeId) -> bool| params.iter().copied().any(pred) || pred(ret);
        let get = |name: &'static str| backend.runtime_funcs.get(name).copied();
        let _ = need;
        // Every helper is a declared codegen root (see
        // `common_backend::is_codegen_root_runtime_fn`), so resolving all five
        // unconditionally costs nothing and keeps the emitter total.
        let ids = BoxHelperIds {
            unbox_int: get("rt_value_unbox_int"),
            as_float: get("rt_value_as_float"),
            box_int: get("rt_value_int"),
            box_float: get("rt_value_float"),
            box_bool: get("rt_value_bool"),
        };
        let raw_scalar_used = params.iter().copied().any(is_raw_scalar) || is_raw_scalar(ret);
        if raw_scalar_used && (ids.unbox_int.is_none() || ids.box_int.is_none()) {
            return Err(BackendError::ModuleError(
                "boxed closure entry needs rt_value_unbox_int/rt_value_int, which are not declared".into(),
            ));
        }
        Ok(ids)
    }

    fn in_func<M: Module>(&self, module: &mut M, func: &mut cranelift_codegen::ir::Function) -> BoxHelperRefs {
        BoxHelperRefs {
            unbox_int: self.unbox_int.map(|id| module.declare_func_in_func(id, func)),
            as_float: self.as_float.map(|id| module.declare_func_in_func(id, func)),
            box_int: self.box_int.map(|id| module.declare_func_in_func(id, func)),
            box_float: self.box_float.map(|id| module.declare_func_in_func(id, func)),
            box_bool: self.box_bool.map(|id| module.declare_func_in_func(id, func)),
        }
    }
}

fn call1(
    b: &mut FunctionBuilder,
    fref: Option<cranelift_codegen::ir::FuncRef>,
    arg: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    match fref {
        Some(f) => {
            let call = b.ins().call(f, &[arg]);
            b.inst_results(call)[0]
        }
        None => arg,
    }
}

/// Decode one tagged argument into the raw representation the outlined body
/// declares (`want`), guided by the parameter's MIR type.
fn unbox_arg(
    b: &mut FunctionBuilder,
    h: &BoxHelperRefs,
    tagged: cranelift_codegen::ir::Value,
    ty: TypeId,
    want: types::Type,
) -> cranelift_codegen::ir::Value {
    match ty {
        TypeId::F32 | TypeId::F64 => {
            let f = call1(b, h.as_float, tagged);
            let f = if b.func.dfg.value_type(f) == types::I64 {
                b.ins().bitcast(types::F64, MemFlags::new(), f)
            } else {
                f
            };
            coerce(b, f, want)
        }
        TypeId::BOOL => {
            let raw = call1(b, h.unbox_int, tagged);
            let flag = b
                .ins()
                .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, raw, 0);
            coerce(b, flag, want)
        }
        t if is_raw_scalar(t) => {
            let raw = call1(b, h.unbox_int, tagged);
            coerce(b, raw, want)
        }
        // Heap-shaped or unknown: the tagged word IS the value.
        _ => coerce(b, tagged, want),
    }
}

/// Encode the outlined body's raw result as a tagged `RuntimeValue`.
fn box_result(
    b: &mut FunctionBuilder,
    h: &BoxHelperRefs,
    val: cranelift_codegen::ir::Value,
    ty: TypeId,
) -> cranelift_codegen::ir::Value {
    let vt = b.func.dfg.value_type(val);
    match ty {
        TypeId::F32 | TypeId::F64 => {
            let f = if vt == types::F32 {
                b.ins().fpromote(types::F64, val)
            } else if vt == types::I64 {
                b.ins().bitcast(types::F64, MemFlags::new(), val)
            } else {
                val
            };
            call1(b, h.box_float, f)
        }
        TypeId::BOOL => {
            // Full-width 0/1 through rt_value_bool — never a bare i8 in a slot
            // the caller reads as a 64-bit RuntimeValue.
            let widened = if vt == types::I64 {
                val
            } else {
                b.ins().uextend(types::I64, val)
            };
            call1(b, h.box_bool, widened)
        }
        t if is_raw_scalar(t) => {
            let widened = match vt {
                types::I8 | types::I16 | types::I32 => b.ins().sextend(types::I64, val),
                types::F64 => b.ins().bitcast(types::I64, MemFlags::new(), val),
                types::F32 => {
                    let p = b.ins().fpromote(types::F64, val);
                    b.ins().bitcast(types::I64, MemFlags::new(), p)
                }
                _ => val,
            };
            call1(b, h.box_int, widened)
        }
        _ => coerce(b, val, types::I64),
    }
}

fn coerce(
    b: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    want: types::Type,
) -> cranelift_codegen::ir::Value {
    let have = b.func.dfg.value_type(val);
    if have == want {
        return val;
    }
    match (have, want) {
        (types::I64, w) if w.is_int() && w.bits() < 64 => b.ins().ireduce(w, val),
        (h, types::I64) if h.is_int() && h.bits() < 64 => b.ins().uextend(types::I64, val),
        (types::F64, types::F32) => b.ins().fdemote(types::F32, val),
        (types::F32, types::F64) => b.ins().fpromote(types::F64, val),
        (types::I64, types::F64) => b.ins().bitcast(types::F64, MemFlags::new(), val),
        (types::F64, types::I64) => b.ins().bitcast(types::I64, MemFlags::new(), val),
        _ => val,
    }
}

/// Names of DEFINED (non-extern, with a body) functions that some function in
/// `mir` loads as a first-class value through `GlobalLoad`. Mirrors the
/// resolution in `cranelift_emitter::emit_global_load`: a name that is not a
/// declared global variable but is a function. Extern fn names are excluded
/// on both sides (they carry no body to wrap and remain guarded in jit.rs).
pub fn named_fn_value_targets(mir: &crate::mir::MirModule) -> Vec<String> {
    let global_names: std::collections::HashSet<&str> = mir
        .globals
        .iter()
        .map(|(name, _, _)| name.as_str())
        .filter(|name| !mir.extern_fn_names.contains(*name))
        .collect();
    let defined: std::collections::HashSet<&str> = mir
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty() && !mir.extern_fn_names.contains(&f.name))
        .map(|f| f.name.as_str())
        .collect();
    let mut out: Vec<String> = Vec::new();
    for func in &mir.functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                if let crate::mir::MirInst::GlobalLoad { global_name, .. } = inst {
                    let name = global_name.as_str();
                    if !global_names.contains(name) && defined.contains(name) && !out.iter().any(|n| n == name) {
                        out.push(name.to_string());
                    }
                }
            }
        }
    }
    out
}

/// Functions with NO body in this unit that some body loads as a value, with
/// the parameter and result types of the value's `HirType::Function`. A load
/// whose type is not a function type carries no arity and is left to the
/// `GlobalLoad` emitter, which refuses it rather than fabricating a pointer.
pub fn imported_fn_value_targets(mir: &crate::mir::MirModule) -> Vec<(String, Vec<TypeId>, TypeId)> {
    let defined: std::collections::HashSet<&str> = mir
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| f.name.as_str())
        .collect();
    let mut out: Vec<(String, Vec<TypeId>, TypeId)> = Vec::new();
    for func in &mir.functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                let crate::mir::MirInst::GlobalLoad { global_name, ty, .. } = inst else {
                    continue;
                };
                let name = global_name.as_str();
                if defined.contains(name)
                    || mir.local_globals.contains(name)
                    || mir.extern_fn_names.contains(name)
                    || out.iter().any(|(n, _, _)| n == name)
                {
                    continue;
                }
                if let Some(crate::hir::HirType::Function { params, ret }) = mir.type_registry.get(*ty) {
                    out.push((name.to_string(), params.clone(), *ret));
                }
            }
        }
    }
    out
}

/// Name of the vtable-slot thunk for a method whose MIR function takes no
/// `self` parameter (the body never references `self`, so HIR dropped it).
pub fn vtable_selfless_entry_name(fn_name: &str) -> String {
    format!("{fn_name}$vt")
}

impl<M: Module> CodegenBackend<M> {
    /// Emit `name$vt(self, p1..pn)` -> `name(p1..pn)` for every function in
    /// `functions` named by a vtable slot whose MIR params do not start with
    /// `self`. A virtual call (`compile_method_call_virtual`) always passes the
    /// receiver first; a slot pointing straight at a selfless body would read
    /// the receiver as its first user argument (measured: a fieldless
    /// `FileReader.lookup(name)` saw the object as `name`, `name.len()` == -1).
    /// Returns the set of thunk-backed names so the vtable writer can pick
    /// the thunk. Must run AFTER `declare_functions`.
    pub fn emit_vtable_selfless_entries(
        &mut self,
        functions: &[MirFunction],
        slot_fn_names: &std::collections::HashSet<String>,
    ) -> BackendResult<std::collections::HashSet<String>> {
        let mut thunked = std::collections::HashSet::new();
        for func in functions {
            if !slot_fn_names.contains(&func.name) {
                continue;
            }
            if func.params.first().is_some_and(|p| p.name == "self") {
                continue;
            }
            let raw_name = vtable_selfless_entry_name(&func.name);
            if self.func_ids.contains_key(&raw_name) {
                thunked.insert(func.name.clone());
                continue;
            }
            let Some(&target_id) = self.func_ids.get(&func.name) else {
                continue;
            };
            let target_sig = build_mir_signature(func, self.module.isa().default_call_conv());
            let mut sig = Signature::new(self.module.isa().default_call_conv());
            sig.params.push(AbiParam::new(types::I64)); // receiver, dropped
            for p in &target_sig.params {
                sig.params.push(AbiParam::new(p.value_type));
            }
            for r in &target_sig.returns {
                sig.returns.push(AbiParam::new(r.value_type));
            }
            let symbol = match &self.module_prefix {
                Some(prefix) => format!("{prefix}__{raw_name}"),
                None => raw_name.clone(),
            };
            let func_id = self
                .module
                .declare_function(&symbol, Linkage::Local, &sig)
                .map_err(|e| BackendError::ModuleError(format!("declare {symbol}: {e}")))?;
            self.func_ids.insert(raw_name.clone(), func_id);

            self.module.clear_context(&mut self.ctx);
            self.ctx.func.signature = sig;
            self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());
            {
                let target_ref = self.module.declare_func_in_func(target_id, &mut self.ctx.func);
                let mut fb_ctx = FunctionBuilderContext::new();
                let mut b = FunctionBuilder::new(&mut self.ctx.func, &mut fb_ctx);
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let params: Vec<_> = b.block_params(entry).to_vec();
                let call = b.ins().call(target_ref, &params[1..]);
                let results = b.inst_results(call).to_vec();
                b.ins().return_(&results);
                b.finalize();
            }
            self.module
                .define_function(func_id, &mut self.ctx)
                .map_err(|e| BackendError::ModuleError(format!("define {symbol}: {e}")))?;
            self.module.clear_context(&mut self.ctx);
            thunked.insert(func.name.clone());
        }
        Ok(thunked)
    }
}
