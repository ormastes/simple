//! LLVM implementation of the `CodegenEmitter` trait.
//!
//! This module provides an LLVM-based emitter that wraps the existing
//! `LlvmBackend` and delegates to functions in `llvm/instructions.rs`
//! and `llvm/functions/`.

#[cfg(feature = "llvm")]
use std::collections::HashMap;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::InlineAsmDialect;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicType;
#[cfg(feature = "llvm")]
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, PointerValue};

#[cfg(feature = "llvm")]
use crate::codegen::emitter_trait::CodegenEmitter;
#[cfg(feature = "llvm")]
use crate::hir::{BinOp, NeighborDirection, PointerKind, TypeId, UnaryOp};
#[cfg(feature = "llvm")]
use crate::mir::{
    BlockId, CallTarget, ContractKind, Effect, FStringPart, GpuAtomicOp, GpuMemoryScope, MirPattern, ParallelBackend,
    PatternBinding, UnitOverflowBehavior, VReg,
};

#[cfg(feature = "llvm")]
use super::LlvmBackend;

/// Type alias for vreg map
#[cfg(feature = "llvm")]
pub type VRegMap = HashMap<VReg, BasicValueEnum<'static>>;

/// LLVM-based emitter wrapping existing `LlvmBackend` infrastructure.
///
/// This struct holds references to the LLVM compilation context
/// and delegates each trait method to the corresponding helper
/// on `LlvmBackend` or generates inline LLVM IR via runtime calls.
#[cfg(feature = "llvm")]
pub struct LlvmEmitter<'a> {
    pub backend: &'a LlvmBackend,
    pub vreg_map: &'a mut VRegMap,
    pub local_allocas: &'a HashMap<usize, PointerValue<'static>>,
    pub builder: &'a Builder<'static>,
    pub module: &'a Module<'static>,
}

#[cfg(feature = "llvm")]
impl LlvmEmitter<'_> {
    /// Look up a vreg value from the map.
    fn get(&self, vreg: VReg) -> Result<BasicValueEnum<'static>, String> {
        self.vreg_map
            .get(&vreg)
            .copied()
            .ok_or_else(|| format!("LLVM emitter: vreg {:?} not found", vreg))
    }

    /// Store a value in the vreg map.
    fn set(&mut self, dest: VReg, val: BasicValueEnum<'static>) {
        self.vreg_map.insert(dest, val);
    }

    /// Call a runtime function by name and return its result.
    fn call_runtime(&self, name: &str, args: &[BasicValueEnum<'static>]) -> Result<BasicValueEnum<'static>, String> {
        self.call_runtime_with_return(name, args, self.backend.runtime_int_type().into())
    }

    /// Call a runtime function by name with an explicit return type.
    fn call_runtime_with_return(
        &self,
        name: &str,
        args: &[BasicValueEnum<'static>],
        return_type: inkwell::types::BasicTypeEnum<'static>,
    ) -> Result<BasicValueEnum<'static>, String> {
        let i64_type = self.backend.runtime_int_type();

        let func = self.module.get_function(name).unwrap_or_else(|| {
            // Auto-declare: assume runtime helper arguments use the RuntimeValue ABI.
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = return_type.fn_type(&param_types, false);
            self.module.add_function(name, fn_type, None)
        });

        let call_args: Vec<BasicMetadataValueEnum> = args.iter().map(|a| (*a).into()).collect();
        let result = self
            .builder
            .build_call(func, &call_args, name)
            .map_err(|e| format!("LLVM call to '{}' failed: {}", name, e))?;
        result
            .try_as_basic_value()
            .left()
            .ok_or_else(|| format!("'{}' did not return a value", name))
    }

    /// Call a runtime function returning a boolean-like integer and widen it to RuntimeValue width.
    fn call_runtime_bool_as_int(
        &self,
        name: &str,
        args: &[BasicValueEnum<'static>],
    ) -> Result<BasicValueEnum<'static>, String> {
        let result = self.call_runtime_with_return(name, args, self.backend.context_ref().i8_type().into())?;
        let widened = self
            .builder
            .build_int_z_extend(result.into_int_value(), self.backend.runtime_int_type(), "bool_to_rv")
            .map_err(|e| format!("LLVM zext for '{}' failed: {}", name, e))?;
        Ok(widened.into())
    }

    /// Map a Cranelift-typed runtime SFFI slot onto the matching LLVM int type.
    ///
    /// Only the integer widths the runtime SFFI table actually uses for scalar
    /// slots are handled. `F64` returns `None` on purpose: `rt_value_float` is
    /// declared `f64` in the Rust runtime but raw-bits `int64_t` in the C one
    /// (recorded in the bug doc, not reconciled here), so silently picking one
    /// of those two for a void call would be exactly the kind of guess this
    /// change exists to remove.
    fn llvm_int_type_for_sffi(&self, ty: cranelift_codegen::ir::Type) -> Option<inkwell::types::IntType<'static>> {
        use cranelift_codegen::ir::types;
        let ctx = self.backend.context_ref();
        match ty {
            types::I8 => Some(ctx.i8_type()),
            types::I16 => Some(ctx.i16_type()),
            types::I32 => Some(ctx.i32_type()),
            types::I64 => Some(ctx.i64_type()),
            _ => None,
        }
    }

    /// Call a runtime function that returns void.
    ///
    /// The declaration is built from the runtime SFFI spec when one exists and
    /// its arity matches what the caller is actually passing. Before this, every
    /// parameter was declared `runtime_int_type()` (i64) regardless of the real
    /// signature, so `rt_decision_probe(u64, bool)` was declared
    /// `void(i64, i64)` and `rt_condition_probe(u64, u32, bool)` was declared
    /// `void(i64, i64, i64)`. Those happen to survive on the SysV and AArch64
    /// ABIs the values travel over, because the low bits land in the right
    /// place, but the declaration was simply not the runtime's signature and
    /// nothing forced the two to agree.
    ///
    /// Two cases deliberately keep the old blind i64 shape rather than being
    /// "fixed":
    ///
    /// - **No spec at all** (`rt_contract_check`, `rt_unit_bound_check`,
    ///   `rt_generator_yield`): these are defined in neither runtime. Inventing
    ///   a signature would dress up a symbol that must keep failing loudly.
    /// - **Spec arity disagrees with the call** (`rt_par_for_each`: this emitter
    ///   passes 2 operands against 4 declared, dropping `input_len` and
    ///   `backend`). That mismatch is a KNOWN unfixed defect and the symbol is
    ///   undefined in both runtimes on purpose. Quietly declaring the 4-arg
    ///   form here would hide the drop, so the arity check must fail closed.
    ///
    /// A spec return type that is non-void is honoured too: `rt_actor_reply` is
    /// `(RuntimeValue) -> RuntimeValue`, and declaring it `void` here — while
    /// some other site may declare it correctly — left two disagreeing
    /// declarations of one symbol in play. The result is simply discarded.
    fn call_runtime_void(&self, name: &str, args: &[BasicValueEnum<'static>]) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();
        let void_type = self.backend.context_ref().void_type();

        // The declared slot types, when the spec exists AND its arity matches
        // what we are about to pass. `None` means "fall back to the blind i64
        // shape", which keeps a loud symbol loud.
        let spec = crate::codegen::runtime_sffi::spec_for(name).filter(|s| s.params.len() == args.len());
        let slot_types: Option<Vec<inkwell::types::IntType<'static>>> = spec.and_then(|s| {
            s.params
                .iter()
                .map(|&ty| self.llvm_int_type_for_sffi(ty))
                .collect::<Option<Vec<_>>>()
        });

        let func = self.module.get_function(name).unwrap_or_else(|| {
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = match &slot_types {
                Some(tys) => tys.iter().map(|t| (*t).into()).collect(),
                None => args.iter().map(|_| i64_type.into()).collect(),
            };
            let fn_type = match spec.map(|s| s.returns) {
                Some([]) | None => void_type.fn_type(&param_types, false),
                Some([ret]) => match self.llvm_int_type_for_sffi(*ret) {
                    Some(int_ty) => int_ty.fn_type(&param_types, false),
                    None => void_type.fn_type(&param_types, false),
                },
                Some(_) => void_type.fn_type(&param_types, false),
            };
            self.module.add_function(name, fn_type, None)
        });

        // Narrow each argument to the slot it is being passed in. Without this
        // the call would not verify once a slot is narrower than i64 — and a
        // truncation here is not a value change: these are the same low bits
        // the old i64 declaration was already relying on the ABI to deliver.
        let call_args: Vec<BasicMetadataValueEnum> = match &slot_types {
            Some(tys) => {
                let mut out = Vec::with_capacity(args.len());
                for (arg, slot) in args.iter().zip(tys.iter()) {
                    let coerced = match arg {
                        BasicValueEnum::IntValue(iv) if iv.get_type().get_bit_width() > slot.get_bit_width() => self
                            .builder
                            .build_int_truncate(*iv, *slot, "sffi_arg")
                            .map_err(|e| format!("LLVM narrowing for '{}' failed: {}", name, e))?
                            .into(),
                        BasicValueEnum::IntValue(iv) if iv.get_type().get_bit_width() < slot.get_bit_width() => self
                            .builder
                            .build_int_z_extend(*iv, *slot, "sffi_arg")
                            .map_err(|e| format!("LLVM widening for '{}' failed: {}", name, e))?
                            .into(),
                        other => *other,
                    };
                    out.push(coerced.into());
                }
                out
            }
            None => args.iter().map(|a| (*a).into()).collect(),
        };

        self.builder
            .build_call(func, &call_args, name)
            .map_err(|e| format!("LLVM call to '{}' failed: {}", name, e))?;
        Ok(())
    }

    /// Helper to create an i64 constant.
    fn i64_const(&self, value: i64) -> BasicValueEnum<'static> {
        self.backend.runtime_int_type().const_int(value as u64, true).into()
    }

    /// Helper to create an i32 constant.
    fn i32_const(&self, value: i32) -> BasicValueEnum<'static> {
        self.backend
            .context_ref()
            .i32_type()
            .const_int(value as u64, true)
            .into()
    }

    // The core-C coverage ABI owns the source name as a C string.  Keep that
    // name in an immutable module global and pass its address through the
    // runtime's i64 pointer slot.
    fn coverage_file_value(&self, file: &str) -> Result<BasicValueEnum<'static>, String> {
        let mut bytes = file.as_bytes().to_vec();
        bytes.push(0);
        let text = self.backend.context_ref().const_string(&bytes, false);
        let global = self.module.add_global(text.get_type(), None, "coverage_file");
        global.set_initializer(&text);
        global.set_constant(true);
        let pointer = global.as_pointer_value();
        let value = self
            .builder
            .build_ptr_to_int(pointer, self.backend.runtime_int_type(), "coverage_file_ptr")
            .map_err(|e| format!("LLVM coverage file pointer conversion failed: {e}"))?;
        Ok(value.into())
    }

    fn method_leaf_name(func_name: &str) -> &str {
        func_name.rsplit('.').next().unwrap_or(func_name)
    }

    fn enum_variant_discriminant(variant_name: &str) -> i64 {
        // Step (d), 2026-08-02: delegate to the SINGLE authoritative definition
        // in the runtime crate. This value is a RUNTIME ABI, not a
        // compiler-internal convention: `rt_option_some`/`rt_option_none`
        // (runtime/src/value/objects.rs) build Option values with it, the
        // bytecode compiler emits it into the instruction stream, and the
        // interpreter SFFI reads it back. A second copy here that drifted by
        // one character would desynchronize compiled code from the runtime
        // silently. See
        // doc/08_tracking/bug/enum_bare_name_collision_registry_2026-08-01.md.
        simple_runtime::value::hash_variant_discriminant(variant_name) as i64
    }

    fn runtime_method_name(method: &str) -> Option<&'static str> {
        match method {
            "len" => Some("rt_len"),
            "push" => Some("rt_array_push"),
            "pop" => Some("rt_array_pop"),
            "clear" => Some("rt_array_clear"),
            // Receiver-polymorphic. `rt_array_reverse` reverses IN PLACE and
            // returns a bool, and this table applied it to EVERY receiver, so
            // text got the `false` receiver-mismatch answer and an array had
            // its receiver mutated. The interpreter mutates nothing
            // (`interpreter_method/collections.rs` `"rev" | "reverse"` copies
            // then reverses; the string arm builds a new text), which is what
            // `rt_reverse` does. It is also the only one of the two that the C
            // runtime defines — `rt_array_reverse` has never existed there, so
            // `arr.reverse()` did not even link on the native lane.
            // MUTATING spelling — see instr/calls.rs. `rev`/`reversed` keep the
            // copying `rt_reverse`; only `reverse` rebinds the receiver.
            "reverse" => Some("rt_reverse_mut"),
            // Same defect, same shape: `rt_array_sort` sorts IN PLACE, returns
            // a bool, was applied to every receiver, and has never existed in
            // runtime_native.c. `rt_sort` copies, matching the interpreter.
            "sort" => Some("rt_sort"),
            "first" => Some("rt_array_first"),
            "last" => Some("rt_array_last"),
            // Receiver-polymorphic. Routing the bare name to the string-only
            // `rt_string_find` made every `[T].find(pred)` answer the -1
            // receiver-mismatch sentinel under LLVM, match at index 0 included,
            // while the type-AWARE table in functions.rs answered with the
            // element. `rt_find` tests receiver AND argument; the return shape
            // differs by receiver, which is the contract hir/lower/expr/mod.rs
            // already encodes. See rt_find.
            "find" => Some("rt_find"),
            "any" => Some("rt_array_any"),
            "all" => Some("rt_array_all"),
            "filter" => Some("rt_array_filter"),
            // Receiver-polymorphic, exactly like `at` and `index_of` below.
            // Routing the bare name `map` straight to the Option-only
            // `rt_option_map` made `[T].map(f)` call the closure EXACTLY ONCE,
            // on the NIL that `rt_enum_payload` returns for a non-enum, and
            // wrap that in `Some` — one call instead of len(), on a value never
            // in the receiver, with no error and exit 0. The type-AWARE table
            // in functions.rs already routes ("Array", "map") correctly; this
            // is the type-blind fallback, which has no receiver type to test,
            // so the test moves into the runtime. See rt_map.
            "map" => Some("rt_map"),
            "starts_with" => Some("rt_string_starts_with"),
            "ends_with" => Some("rt_string_ends_with"),
            "concat" => Some("rt_string_concat"),
            "contains" | "contains_key" | "has_key" | "has" => Some("rt_contains"),
            "char_at" => Some("rt_string_char_at"),
            // Receiver-polymorphic, exactly like `index_of` below: `at` must NOT
            // go straight to the string-only `rt_string_char_at`, which returns
            // its receiver-mismatch `nil` for an array receiver. That made every
            // `[T].at(i)` read as absent under LLVM — in-range hits included —
            // while Cranelift (codegen/instr/calls.rs) returns a real `Option`
            // via `rt_at`. Same source, two different answers per backend.
            // `rt_at` tests the receiver: arrays get the bounds-checked
            // `rt_array_at` Option, text keeps its raw-character result.
            // See doc/08_tracking/bug/array_at_returns_nil_for_every_index_2026-08-01.md.
            "at" => Some("rt_at"),
            "char_code_at" => Some("rt_string_char_code_at"),
            "byte_at" => Some("rt_string_byte_at"),
            "join" => Some("rt_string_join"),
            "trim" => Some("rt_string_trim"),
            "trim_start" => Some("rt_string_trim_start"),
            "trim_end" => Some("rt_string_trim_end"),
            "split" => Some("rt_string_split"),
            "replace" => Some("rt_string_replace"),
            "to_upper" | "upper" => Some("rt_string_to_upper"),
            "to_lower" | "lower" => Some("rt_string_to_lower"),
            "to_string" | "str" => Some("rt_to_string"),
            "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => Some("rt_string_to_float"),
            "to_int" | "to_i64" => Some("rt_string_to_int"),
            "parse_int" | "parse_i32" | "parse_i64" => Some("rt_string_parse_int"),
            // Receiver-polymorphic: `index_of` must NOT go straight to the
            // string-only `rt_string_find`, which returns its -1 receiver-
            // mismatch sentinel for an array receiver. That made every
            // `[T].index_of(v)` return -1 under LLVM — including when the
            // element sat at index 0 — while the Cranelift/JIT emitter
            // (codegen/instr/calls.rs) returned the correct index via
            // `rt_index_of`. Same source, two different answers per backend.
            "index_of" => Some("rt_index_of"),
            "find_str" => Some("rt_string_find"),
            "rfind" | "last_index_of" => Some("rt_string_rfind"),
            "slice" | "substring" => Some("rt_slice"),
            "get" => Some("rt_index_get"),
            "keys" => Some("rt_dict_keys"),
            "values" => Some("rt_dict_values"),
            "unwrap" | "unwrap_or" | "unwrap_err" => Some("rt_enum_payload"),
            _ => None,
        }
    }
}

#[cfg(feature = "llvm")]
impl CodegenEmitter for LlvmEmitter<'_> {
    type Value = BasicValueEnum<'static>;
    type Error = String;

    // =========================================================================
    // Constants
    // =========================================================================
    fn emit_const_int(&mut self, dest: VReg, value: i64) -> Result<(), String> {
        let val = self.backend.runtime_int_type().const_int(value as u64, true);
        self.set(dest, val.into());
        Ok(())
    }

    fn emit_const_float(&mut self, dest: VReg, value: f64) -> Result<(), String> {
        let val = self.backend.context_ref().f64_type().const_float(value);
        self.set(dest, val.into());
        Ok(())
    }

    fn emit_const_bool(&mut self, dest: VReg, value: bool) -> Result<(), String> {
        let bits = if value { 11u64 } else { 19u64 };
        let val = self.backend.runtime_int_type().const_int(bits, false);
        self.set(dest, val.into());
        Ok(())
    }

    fn emit_const_string(&mut self, dest: VReg, value: &str) -> Result<(), String> {
        let str_val = self.backend.context_ref().const_string(value.as_bytes(), false);
        let global = self.module.add_global(str_val.get_type(), None, "str");
        global.set_initializer(&str_val);
        global.set_constant(true);
        self.set(dest, global.as_pointer_value().into());
        Ok(())
    }

    fn emit_const_symbol(&mut self, dest: VReg, value: &str) -> Result<(), String> {
        let str_val = self.backend.context_ref().const_string(value.as_bytes(), false);
        let global = self
            .module
            .add_global(str_val.get_type(), None, &format!("sym_{}", value));
        global.set_initializer(&str_val);
        global.set_constant(true);
        self.set(dest, global.as_pointer_value().into());
        Ok(())
    }

    // =========================================================================
    // Basic operations
    // =========================================================================
    fn emit_copy(&mut self, dest: VReg, src: VReg) -> Result<(), String> {
        if let Some(val) = self.vreg_map.get(&src).copied() {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_aggregate_copy(
        &mut self,
        dest: VReg,
        src: VReg,
        byte_size: u32,
        deep_fields: &[crate::mir::AggregateFieldCopy],
    ) -> Result<(), String> {
        self.backend
            .compile_aggregate_copy(dest, src, byte_size, deep_fields, self.vreg_map, self.builder)
            .map_err(|e| e.to_string())
    }

    fn emit_binop(&mut self, dest: VReg, op: BinOp, left: VReg, right: VReg) -> Result<(), String> {
        let lhs = self.get(left)?;
        let rhs = self.get(right)?;
        let result = self
            .backend
            .compile_binop(op, lhs, rhs, self.builder, self.module, None, None, None)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_unary_op(&mut self, dest: VReg, op: UnaryOp, operand: VReg) -> Result<(), String> {
        let val = self.get(operand)?;
        let result = self
            .backend
            .compile_unaryop(op, val, self.builder)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_cast(&mut self, dest: VReg, source: VReg, from_ty: TypeId, to_ty: TypeId) -> Result<(), String> {
        let source_val = self.get(source)?;
        let result = self
            .backend
            .compile_cast(source_val, &from_ty, &to_ty, self.builder, self.module)
            .map_err(|e: crate::error::CompileError| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_spread(&mut self, dest: VReg, source: VReg) -> Result<(), String> {
        // Spread is a copy at the LLVM level
        if let Some(val) = self.vreg_map.get(&source).copied() {
            self.set(dest, val);
        }
        Ok(())
    }

    // =========================================================================
    // Memory
    // =========================================================================
    fn emit_load(&mut self, dest: VReg, addr: VReg) -> Result<(), String> {
        let addr_val = self.get(addr)?;
        if let BasicValueEnum::PointerValue(ptr) = addr_val {
            let i64_type = self.backend.runtime_int_type();
            let loaded = self
                .builder
                .build_load(i64_type, ptr, "load")
                .map_err(|e| format!("LLVM load failed: {}", e))?;
            self.set(dest, loaded);
        } else {
            return Err("Load requires pointer value".to_string());
        }
        Ok(())
    }

    fn emit_store(&mut self, addr: VReg, value: VReg) -> Result<(), String> {
        let addr_val = self.get(addr)?;
        let val = self.get(value)?;
        if let BasicValueEnum::PointerValue(ptr) = addr_val {
            self.builder
                .build_store(ptr, val)
                .map_err(|e| format!("LLVM store failed: {}", e))?;
        } else {
            return Err("Store requires pointer value".to_string());
        }
        Ok(())
    }

    fn emit_global_load(&mut self, dest: VReg, global_name: &str, ty: TypeId) -> Result<(), String> {
        let global = self
            .module
            .get_global(global_name)
            .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
        let llvm_ty = self.backend.llvm_type(&ty).map_err(|e| e.to_string())?;
        let loaded = self
            .builder
            .build_load(llvm_ty, global.as_pointer_value(), "global_load")
            .map_err(|e| format!("LLVM global load failed: {}", e))?;
        self.set(dest, loaded);
        Ok(())
    }

    fn emit_global_store(&mut self, global_name: &str, value: VReg, _ty: TypeId) -> Result<(), String> {
        let global = self
            .module
            .get_global(global_name)
            .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
        let val = self.get(value)?;
        self.builder
            .build_store(global.as_pointer_value(), val)
            .map_err(|e| format!("LLVM global store failed: {}", e))?;
        Ok(())
    }

    fn emit_local_addr(&mut self, dest: VReg, local_index: usize) -> Result<(), String> {
        let alloca = self
            .local_allocas
            .get(&local_index)
            .ok_or_else(|| format!("Local index {} not found", local_index))?;
        self.set(dest, (*alloca).into());
        Ok(())
    }

    fn emit_get_element_ptr(&mut self, dest: VReg, base: VReg, index: VReg) -> Result<(), String> {
        let base_val = self.get(base)?;
        let idx_val = self.get(index)?;
        if let (BasicValueEnum::PointerValue(ptr), BasicValueEnum::IntValue(idx)) = (base_val, idx_val) {
            let i8_type = self.backend.context_ref().i8_type();
            let gep = unsafe {
                self.builder
                    .build_gep(i8_type, ptr, &[idx], "gep")
                    .map_err(|e| format!("LLVM GEP failed: {}", e))?
            };
            self.set(dest, gep.into());
        } else {
            return Err("GEP requires pointer base and integer index".to_string());
        }
        Ok(())
    }

    fn emit_gc_alloc(&mut self, dest: VReg, ty: TypeId) -> Result<(), String> {
        let llvm_ty = self.backend.llvm_type(&ty).map_err(|e| e.to_string())?;
        let alloc = self
            .builder
            .build_alloca(llvm_ty, "gc_alloc")
            .map_err(|e| format!("LLVM alloca failed: {}", e))?;
        self.set(dest, alloc.into());
        Ok(())
    }

    fn emit_wait(&mut self, dest: Option<VReg>, target: VReg) -> Result<(), String> {
        let target_val = self.get(target)?;
        let result = self.call_runtime("rt_wait", &[target_val])?;
        if let Some(d) = dest {
            self.set(d, result);
        }
        Ok(())
    }

    // =========================================================================
    // Calls
    // =========================================================================
    fn emit_call(&mut self, dest: &Option<VReg>, target: &CallTarget, args: &[VReg]) -> Result<(), String> {
        let func_name = target.name();
        let method = Self::method_leaf_name(func_name);

        if matches!(method, "unwrap" | "unwrap_err") && args.len() == 1 {
            let recv = self.get(args[0])?;
            let result = self.call_runtime("rt_enum_payload", &[recv])?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
            return Ok(());
        }

        if matches!(method, "is_ok" | "is_err") && args.len() == 1 {
            let recv = self.get(args[0])?;
            let variant = if method == "is_ok" { "Ok" } else { "Err" };
            let disc = self.i64_const(Self::enum_variant_discriminant(variant));
            let result = self.call_runtime("rt_enum_check_discriminant", &[recv, disc])?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
            return Ok(());
        }

        let i64_type = self.backend.runtime_int_type();

        let called_func = self.module.get_function(func_name).unwrap_or_else(|| {
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            self.module.add_function(func_name, fn_type, None)
        });

        let mut arg_vals: Vec<BasicMetadataValueEnum> = Vec::new();
        for arg in args {
            let val = self.get(*arg)?;
            arg_vals.push(val.into());
        }

        let call_site = self
            .builder
            .build_call(called_func, &arg_vals, "call")
            .map_err(|e| format!("LLVM call failed: {}", e))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                self.set(*d, ret_val);
            }
        }
        Ok(())
    }

    fn emit_interp_call(
        &mut self,
        dest: &Option<VReg>,
        func_name: &str,
        args: &[VReg],
        _boxed_result: bool,
    ) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();
        let i8_type = self.backend.context_ref().i8_type();
        let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());
        let slot_bytes = (i64_type.get_bit_width() / 8) as u64;

        let interp_call = self.module.get_function("rt_interp_call").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            self.module.add_function("rt_interp_call", fn_type, None)
        });

        let name_bytes = func_name.as_bytes();
        let name_const = self.backend.context_ref().const_string(name_bytes, false);
        let name_global = self.module.add_global(name_const.get_type(), None, "func_name");
        name_global.set_initializer(&name_const);
        name_global.set_constant(true);
        let name_ptr = name_global.as_pointer_value();
        let name_ptr_i64 = self
            .builder
            .build_ptr_to_int(name_ptr, i64_type, "func_name_ptr")
            .map_err(|e| format!("LLVM ptr_to_int failed: {}", e))?;
        let name_len = i64_type.const_int(name_bytes.len() as u64, false);
        let argc = i64_type.const_int(args.len() as u64, false);
        let argv = if args.is_empty() {
            i64_type.const_int(0, false)
        } else {
            let alloc_fn = self.module.get_function("rt_alloc").unwrap_or_else(|| {
                let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                self.module.add_function("rt_alloc", fn_type, None)
            });
            let total_bytes = i64_type.const_int(args.len() as u64 * slot_bytes, false);
            let alloc_call = self
                .builder
                .build_call(alloc_fn, &[total_bytes.into()], "interp_argv_alloc")
                .map_err(|e| format!("LLVM rt_alloc call failed: {}", e))?;
            let argv_raw = alloc_call
                .try_as_basic_value()
                .left()
                .ok_or_else(|| "LLVM rt_alloc missing return value".to_string())?
                .into_int_value();
            let argv_ptr = self
                .builder
                .build_int_to_ptr(argv_raw, i8_ptr_type, "interp_argv_ptr")
                .map_err(|e| format!("LLVM int_to_ptr failed: {}", e))?;

            for (index, arg) in args.iter().enumerate() {
                let value = self.get(*arg)?;
                let int_value = match value {
                    BasicValueEnum::IntValue(int_value) => int_value,
                    BasicValueEnum::PointerValue(pointer_value) => self
                        .builder
                        .build_ptr_to_int(pointer_value, i64_type, "interp_arg_ptr")
                        .map_err(|e| format!("LLVM ptr_to_int failed: {}", e))?,
                    _ => {
                        return Err(format!("LLVM emitter: unsupported interp arg value kind for {:?}", arg));
                    }
                };
                let offset = self
                    .backend
                    .context_ref()
                    .i32_type()
                    .const_int((index as u64) * slot_bytes, false);
                let slot_ptr = unsafe {
                    self.builder
                        .build_gep(i8_type, argv_ptr, &[offset], "interp_argv_slot")
                        .map_err(|e| format!("LLVM gep failed: {}", e))?
                };
                let typed_ptr = self
                    .builder
                    .build_pointer_cast(
                        slot_ptr,
                        self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                        "interp_argv_typed_ptr",
                    )
                    .map_err(|e| format!("LLVM pointer cast failed: {}", e))?;
                self.builder
                    .build_store(typed_ptr, int_value)
                    .map_err(|e| format!("LLVM store failed: {}", e))?;
            }

            argv_raw
        };

        let call_args = [name_ptr_i64.into(), name_len.into(), argc.into(), argv.into()];
        let call_site = self
            .builder
            .build_call(interp_call, &call_args, "interp_call")
            .map_err(|e| format!("LLVM interp_call failed: {}", e))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                self.set(*d, ret_val);
            }
        }
        Ok(())
    }

    fn emit_interp_eval(&mut self, dest: VReg, expr_index: usize) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();

        let interp_eval = self.module.get_function("rt_interp_eval").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            self.module.add_function("rt_interp_eval", fn_type, None)
        });

        let idx = i64_type.const_int(expr_index as u64, true);
        let call_site = self
            .builder
            .build_call(interp_eval, &[idx.into()], "eval")
            .map_err(|e| format!("LLVM interp_eval failed: {}", e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            self.set(dest, ret_val);
        }
        Ok(())
    }

    fn emit_inline_asm(&mut self, instructions: &[String], volatile: bool) -> Result<(), String> {
        let fn_type = self.backend.context_ref().void_type().fn_type(&[], false);
        let asm = self.backend.context_ref().create_inline_asm(
            fn_type,
            instructions.join("\n"),
            String::new(),
            volatile,
            false,
            Some(InlineAsmDialect::ATT),
            false,
        );
        self.builder
            .build_indirect_call(fn_type, asm, &[], "")
            .map_err(|e| format!("LLVM inline asm failed: {}", e))?;
        Ok(())
    }

    fn emit_indirect_call(
        &mut self,
        dest: &Option<VReg>,
        callee: VReg,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
        _effect: Effect,
    ) -> Result<(), String> {
        let callee_val = self.get(callee)?;
        let i8_type = self.backend.context_ref().i8_type();
        let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());

        if let BasicValueEnum::PointerValue(closure_ptr) = callee_val {
            // Load function pointer from closure (at offset 0)
            let base_ptr = self
                .builder
                .build_pointer_cast(closure_ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| format!("cast failed: {}", e))?;
            let offset_val = self.backend.context_ref().i32_type().const_int(0, false);
            let fn_ptr_slot = unsafe {
                self.builder
                    .build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let fn_ptr_slot = self
                .builder
                .build_pointer_cast(
                    fn_ptr_slot,
                    self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "fn_ptr_slot_cast",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            let func_ptr = self
                .builder
                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                .map_err(|e| format!("load failed: {}", e))?;

            if let BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                let mut arg_vals: Vec<BasicMetadataValueEnum> = Vec::new();
                for arg in args {
                    let val = self.get(*arg)?;
                    arg_vals.push(val.into());
                }

                let llvm_param_types: Result<Vec<inkwell::types::BasicMetadataTypeEnum>, String> = param_types
                    .iter()
                    .map(|ty| self.backend.llvm_type(ty).map(|t| t.into()).map_err(|e| e.to_string()))
                    .collect();
                let llvm_param_types = llvm_param_types?;

                let fn_type = if return_type == TypeId::VOID {
                    self.backend.context_ref().void_type().fn_type(&llvm_param_types, false)
                } else {
                    let ret_llvm = self.backend.llvm_type(&return_type).map_err(|e| e.to_string())?;
                    match ret_llvm {
                        inkwell::types::BasicTypeEnum::ArrayType(t) => t.fn_type(&llvm_param_types, false),
                        inkwell::types::BasicTypeEnum::FloatType(t) => t.fn_type(&llvm_param_types, false),
                        inkwell::types::BasicTypeEnum::IntType(t) => t.fn_type(&llvm_param_types, false),
                        inkwell::types::BasicTypeEnum::PointerType(t) => t.fn_type(&llvm_param_types, false),
                        inkwell::types::BasicTypeEnum::StructType(t) => t.fn_type(&llvm_param_types, false),
                        inkwell::types::BasicTypeEnum::VectorType(t) => t.fn_type(&llvm_param_types, false),
                    }
                };

                let call_site = self
                    .builder
                    .build_indirect_call(fn_type, fn_ptr, &arg_vals, "indirect_call")
                    .map_err(|e| format!("indirect call failed: {}", e))?;

                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        self.set(*d, ret_val);
                    }
                }
            }
        } else {
            return Err("IndirectCall requires closure pointer".to_string());
        }
        Ok(())
    }

    // =========================================================================
    // Collections
    // =========================================================================
    fn emit_array_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();
        let array_type = i64_type.array_type(elements.len() as u32);
        let alloc = self
            .builder
            .build_alloca(array_type, "array")
            .map_err(|e| format!("alloca failed: {}", e))?;

        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get(*elem)?;
            let indices = [
                self.backend.context_ref().i32_type().const_int(0, false),
                self.backend.context_ref().i32_type().const_int(i as u64, false),
            ];
            let gep = unsafe {
                self.builder
                    .build_gep(array_type, alloc, &indices, "elem_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            self.builder
                .build_store(gep, elem_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, alloc.into());
        Ok(())
    }

    fn emit_tuple_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();
        let field_types: Vec<inkwell::types::BasicTypeEnum> = elements.iter().map(|_| i64_type.into()).collect();
        let struct_type = self.backend.context_ref().struct_type(&field_types, false);
        let alloc = self
            .builder
            .build_alloca(struct_type, "tuple")
            .map_err(|e| format!("alloca failed: {}", e))?;

        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get(*elem)?;
            let gep = self
                .builder
                .build_struct_gep(struct_type, alloc, i as u32, "tuple_elem")
                .map_err(|e| format!("struct gep failed: {}", e))?;
            self.builder
                .build_store(gep, elem_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, alloc.into());
        Ok(())
    }

    fn emit_vec_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        // Vec lit is the same as array lit at the LLVM level
        self.emit_array_lit(dest, elements)
    }

    fn emit_dict_lit(&mut self, dest: VReg, keys: &[VReg], values: &[VReg]) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();
        let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());

        let dict_new = self.module.get_function("rt_dict_new").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
            self.module.add_function("rt_dict_new", fn_type, None)
        });

        let dict_insert = self.module.get_function("rt_dict_insert").unwrap_or_else(|| {
            let fn_type = self
                .backend
                .context_ref()
                .void_type()
                .fn_type(&[i8_ptr_type.into(), i64_type.into(), i64_type.into()], false);
            self.module.add_function("rt_dict_insert", fn_type, None)
        });

        let capacity = i64_type.const_int(keys.len() as u64, false);
        let dict_ptr = self
            .builder
            .build_call(dict_new, &[capacity.into()], "dict")
            .map_err(|e| format!("dict_new call failed: {}", e))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| "dict_new returned void".to_string())?;

        for (key, value) in keys.iter().zip(values.iter()) {
            let key_val = self.get(*key)?;
            let value_val = self.get(*value)?;
            self.builder
                .build_call(dict_insert, &[dict_ptr.into(), key_val.into(), value_val.into()], "")
                .map_err(|e| format!("dict_insert call failed: {}", e))?;
        }
        self.set(dest, dict_ptr);
        Ok(())
    }

    fn emit_index_get(&mut self, dest: VReg, collection: VReg, index: VReg) -> Result<(), String> {
        let coll_val = self.get(collection)?;
        let idx_val = self.get(index)?;

        if let (BasicValueEnum::PointerValue(ptr), BasicValueEnum::IntValue(idx)) = (coll_val, idx_val) {
            let i64_type = self.backend.runtime_int_type();
            let arr_type = i64_type.array_type(0);
            let indices = [self.backend.context_ref().i32_type().const_int(0, false), idx];
            let gep = unsafe {
                self.builder
                    .build_gep(arr_type, ptr, &indices, "elem_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let loaded = self
                .builder
                .build_load(i64_type, gep, "elem")
                .map_err(|e| format!("load failed: {}", e))?;
            self.set(dest, loaded);
        }
        Ok(())
    }

    fn emit_index_set(&mut self, collection: VReg, index: VReg, value: VReg) -> Result<(), String> {
        let coll_val = self.get(collection)?;
        let idx_val = self.get(index)?;
        let val = self.get(value)?;

        if let (BasicValueEnum::PointerValue(ptr), BasicValueEnum::IntValue(idx)) = (coll_val, idx_val) {
            let i64_type = self.backend.runtime_int_type();
            let arr_type = i64_type.array_type(0);
            let indices = [self.backend.context_ref().i32_type().const_int(0, false), idx];
            let gep = unsafe {
                self.builder
                    .build_gep(arr_type, ptr, &indices, "elem_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            self.builder
                .build_store(gep, val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        Ok(())
    }

    fn emit_slice_op(
        &mut self,
        dest: VReg,
        collection: VReg,
        start: Option<VReg>,
        end: Option<VReg>,
        step: Option<VReg>,
    ) -> Result<(), String> {
        let i64_type = self.backend.runtime_int_type();
        let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());

        let slice_fn = self.module.get_function("rt_slice").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            self.module.add_function("rt_slice", fn_type, None)
        });

        let coll_val = self.get(collection)?;
        let start_val = if let Some(s) = start {
            self.get(s)?
        } else {
            i64_type.const_int(0, false).into()
        };
        let end_val = if let Some(e) = end {
            self.get(e)?
        } else {
            i64_type.const_int(i64::MAX as u64, false).into()
        };
        let step_val = if let Some(s) = step {
            self.get(s)?
        } else {
            i64_type.const_int(1, false).into()
        };

        let call_site = self
            .builder
            .build_call(
                slice_fn,
                &[coll_val.into(), start_val.into(), end_val.into(), step_val.into()],
                "slice",
            )
            .map_err(|e| format!("slice call failed: {}", e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            self.set(dest, ret_val);
        }
        Ok(())
    }

    fn emit_fstring_format(&mut self, dest: VReg, parts: &[FStringPart]) -> Result<(), String> {
        // Delegate to runtime for format string assembly
        let result = self.call_runtime("rt_fstring_format", &[self.i64_const(parts.len() as i64)])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // SIMD / Vector operations — delegate to runtime
    // =========================================================================
    fn emit_vec_reduction(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), String> {
        let src = self.get(source)?;
        let result = match op {
            "rt_vec_all" | "rt_vec_any" => self.call_runtime_bool_as_int(op, &[src])?,
            _ => self.call_runtime(op, &[src])?,
        };
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_extract(&mut self, dest: VReg, vector: VReg, index: VReg) -> Result<(), String> {
        let vec_val = self.get(vector)?;
        let idx = self.get(index)?;
        let result = self.call_runtime("rt_vec_extract", &[vec_val, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_with(&mut self, dest: VReg, vector: VReg, index: VReg, value: VReg) -> Result<(), String> {
        let vec_val = self.get(vector)?;
        let idx = self.get(index)?;
        let val = self.get(value)?;
        let result = self.call_runtime("rt_vec_with", &[vec_val, idx, val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_math(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), String> {
        let src = self.get(source)?;
        let result = self.call_runtime(op, &[src])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_shuffle(&mut self, dest: VReg, source: VReg, indices: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let idx = self.get(indices)?;
        let result = self.call_runtime("rt_vec_shuffle", &[src, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_blend(&mut self, dest: VReg, first: VReg, second: VReg, indices: VReg) -> Result<(), String> {
        let a = self.get(first)?;
        let b = self.get(second)?;
        let idx = self.get(indices)?;
        let result = self.call_runtime("rt_vec_blend", &[a, b, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_select(&mut self, dest: VReg, mask: VReg, if_true: VReg, if_false: VReg) -> Result<(), String> {
        let m = self.get(mask)?;
        let t = self.get(if_true)?;
        let f = self.get(if_false)?;
        let result = self.call_runtime("rt_vec_select", &[m, t, f])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_load(&mut self, dest: VReg, array: VReg, offset: VReg, lanes: u32) -> Result<(), String> {
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        let lanes = self.backend.runtime_int_type().const_int(lanes as u64, false).into();
        let result = self.call_runtime("rt_vec_load", &[arr, off, lanes])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_store(&mut self, source: VReg, array: VReg, offset: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        self.call_runtime_void("rt_vec_store", &[src, arr, off])
    }

    fn emit_vec_gather(&mut self, dest: VReg, array: VReg, indices: VReg) -> Result<(), String> {
        let arr = self.get(array)?;
        let idx = self.get(indices)?;
        let result = self.call_runtime("rt_vec_gather", &[arr, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_scatter(&mut self, source: VReg, array: VReg, indices: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let arr = self.get(array)?;
        let idx = self.get(indices)?;
        self.call_runtime_void("rt_vec_scatter", &[src, arr, idx])
    }

    fn emit_vec_fma(&mut self, dest: VReg, a: VReg, b: VReg, c: VReg) -> Result<(), String> {
        let av = self.get(a)?;
        let bv = self.get(b)?;
        let cv = self.get(c)?;
        let result = self.call_runtime("rt_vec_fma", &[av, bv, cv])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_recip(&mut self, dest: VReg, source: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let result = self.call_runtime("rt_vec_recip", &[src])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_masked_load(
        &mut self,
        dest: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
        default: VReg,
    ) -> Result<(), String> {
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        let m = self.get(mask)?;
        let def = self.get(default)?;
        let result = self.call_runtime("rt_vec_masked_load", &[arr, off, m, def])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_masked_store(&mut self, source: VReg, array: VReg, offset: VReg, mask: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        let m = self.get(mask)?;
        self.call_runtime_void("rt_vec_masked_store", &[src, arr, off, m])
    }

    fn emit_vec_min_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), String> {
        let av = self.get(a)?;
        let bv = self.get(b)?;
        let result = self.call_runtime("rt_vec_min_vec", &[av, bv])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_max_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), String> {
        let av = self.get(a)?;
        let bv = self.get(b)?;
        let result = self.call_runtime("rt_vec_max_vec", &[av, bv])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_clamp(&mut self, dest: VReg, source: VReg, lo: VReg, hi: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let lo_v = self.get(lo)?;
        let hi_v = self.get(hi)?;
        let result = self.call_runtime("rt_vec_clamp", &[src, lo_v, hi_v])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_neighbor_load(&mut self, dest: VReg, array: VReg, direction: NeighborDirection) -> Result<(), String> {
        let arr = self.get(array)?;
        let dir = self.i64_const(direction as i64);
        let result = self.call_runtime("rt_neighbor_load", &[arr, dir])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Structs / Fields
    // =========================================================================
    fn emit_struct_init(
        &mut self,
        dest: VReg,
        struct_size: usize,
        field_offsets: &[u32],
        field_types: &[TypeId],
        field_values: &[VReg],
    ) -> Result<(), String> {
        let i8_type = self.backend.context_ref().i8_type();
        let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(struct_size as u32);
        let alloc = self
            .builder
            .build_alloca(array_type, "struct")
            .map_err(|e| format!("alloca failed: {}", e))?;
        let struct_ptr = self
            .builder
            .build_pointer_cast(alloc, i8_ptr_type, "struct_ptr")
            .map_err(|e| format!("cast failed: {}", e))?;

        for ((offset, field_type), value) in field_offsets.iter().zip(field_types.iter()).zip(field_values.iter()) {
            let field_val = self.get(*value)?;
            let offset_val = self.backend.context_ref().i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(typed_ptr, field_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, struct_ptr.into());
        Ok(())
    }

    fn emit_field_get(
        &mut self,
        dest: VReg,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
    ) -> Result<(), String> {
        let obj_val = self.get(object)?;
        if let BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.backend.context_ref().i8_type();
            let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());
            let base_ptr = self
                .builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| format!("cast failed: {}", e))?;
            let offset_val = self
                .backend
                .context_ref()
                .i32_type()
                .const_int(byte_offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let llvm_field_ty = self.backend.llvm_type(&field_type).map_err(|e| e.to_string())?;
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            let loaded = self
                .builder
                .build_load(llvm_field_ty, typed_ptr, "field")
                .map_err(|e| format!("load failed: {}", e))?;
            self.set(dest, loaded);
        } else {
            return Err("FieldGet requires pointer to struct".to_string());
        }
        Ok(())
    }

    fn emit_field_set(
        &mut self,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
        value: VReg,
    ) -> Result<(), String> {
        let obj_val = self.get(object)?;
        let val = self.get(value)?;
        if let BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.backend.context_ref().i8_type();
            let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());
            let base_ptr = self
                .builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| format!("cast failed: {}", e))?;
            let offset_val = self
                .backend
                .context_ref()
                .i32_type()
                .const_int(byte_offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(typed_ptr, val)
                .map_err(|e| format!("store failed: {}", e))?;
        } else {
            return Err("FieldSet requires pointer to struct".to_string());
        }
        Ok(())
    }

    // =========================================================================
    // Closures
    // =========================================================================
    fn emit_closure_create(
        &mut self,
        dest: VReg,
        func_name: &str,
        closure_size: usize,
        capture_offsets: &[u32],
        captures: &[VReg],
    ) -> Result<(), String> {
        let i8_type = self.backend.context_ref().i8_type();
        let i8_ptr_type = self.backend.context_ref().ptr_type(inkwell::AddressSpace::default());
        // Closures can escape the creator via runtime pool/thread APIs. Heap
        // allocation keeps captures stable after the creating frame advances.
        let i64_type = self.backend.runtime_int_type();
        let alloc_fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
        let alloc_fn = self
            .module
            .get_function("rt_alloc")
            .unwrap_or_else(|| self.module.add_function("rt_alloc", alloc_fn_type, None));
        let allocation_size = closure_size.max(16);
        let size_val = i64_type.const_int(allocation_size as u64, false);
        let alloc_call = self
            .builder
            .build_call(alloc_fn, &[size_val.into()], "closure_alloc")
            .map_err(|e| format!("rt_alloc call failed: {}", e))?;
        let alloc_value = alloc_call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| "rt_alloc did not return a value".to_string())?;
        let closure_ptr = match alloc_value {
            BasicValueEnum::PointerValue(ptr) => self
                .builder
                .build_pointer_cast(ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| format!("cast failed: {}", e))?,
            BasicValueEnum::IntValue(iv) => self
                .builder
                .build_int_to_ptr(iv, i8_ptr_type, "closure_ptr")
                .map_err(|e| format!("int_to_ptr failed: {}", e))?,
            _ => return Err("rt_alloc returned unsupported value kind".to_string()),
        };

        // Store function pointer at offset 0
        let func_ptr = self
            .module
            .get_function(func_name)
            .map(|f| f.as_global_value().as_pointer_value())
            .unwrap_or_else(|| i8_ptr_type.const_null());
        let func_ptr_cast = self
            .builder
            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
            .map_err(|e| format!("cast failed: {}", e))?;
        let fn_slot = self
            .builder
            .build_pointer_cast(
                closure_ptr,
                self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                "fn_slot",
            )
            .map_err(|e| format!("cast failed: {}", e))?;
        self.builder
            .build_store(fn_slot, func_ptr_cast)
            .map_err(|e| format!("store failed: {}", e))?;

        if closure_size < 16 {
            let offset_val = self.backend.context_ref().i32_type().const_int(8, false);
            let marker_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, closure_ptr, &[offset_val], "closure_marker_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let marker_slot = self
                .builder
                .build_pointer_cast(
                    marker_ptr,
                    self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "closure_marker_slot",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(marker_slot, i64_type.const_zero())
                .map_err(|e| format!("store failed: {}", e))?;
        }

        // Store captured values at their offsets
        for (offset, value) in capture_offsets.iter().zip(captures.iter()) {
            let capture_val = self.get(*value)?;
            let offset_val = self.backend.context_ref().i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "cap_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(typed_ptr, capture_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, closure_ptr.into());
        Ok(())
    }

    // =========================================================================
    // Methods — delegate to runtime
    // =========================================================================
    fn emit_method_call_static(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        func_name: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        let method = Self::method_leaf_name(func_name);

        if matches!(
            method,
            "to_u8" | "to_i8" | "to_u16" | "to_i16" | "to_u32" | "to_i32" | "to_u64" | "to_i64" | "to_int"
        ) {
            let recv = self.get(receiver)?;
            let int_type = match method {
                "to_u8" | "to_i8" => self.backend.context_ref().i8_type(),
                "to_u16" | "to_i16" => self.backend.context_ref().i16_type(),
                "to_u32" | "to_i32" => self.backend.context_ref().i32_type(),
                _ => self.backend.context_ref().i64_type(),
            };
            let value = match recv {
                BasicValueEnum::IntValue(v) => {
                    if v.get_type() == int_type {
                        v
                    } else if v.get_type().get_bit_width() > int_type.get_bit_width() {
                        self.builder
                            .build_int_truncate(v, int_type, "method_int_trunc")
                            .map_err(|e| format!("LLVM int truncate failed: {}", e))?
                    } else {
                        self.builder
                            .build_int_z_extend(v, int_type, "method_int_zext")
                            .map_err(|e| format!("LLVM int zext failed: {}", e))?
                    }
                }
                BasicValueEnum::FloatValue(v) => self
                    .builder
                    .build_float_to_unsigned_int(v, int_type, "method_float_to_uint")
                    .map_err(|e| format!("LLVM float_to_uint failed: {}", e))?,
                BasicValueEnum::PointerValue(v) => self
                    .builder
                    .build_ptr_to_int(v, int_type, "method_ptr_to_int")
                    .map_err(|e| format!("LLVM ptr_to_int failed: {}", e))?,
                _ => {
                    return Err(format!(
                        "unsupported receiver kind for numeric cast method '{}'",
                        method
                    ))
                }
            };
            if let Some(d) = dest {
                self.set(*d, value.into());
            }
            return Ok(());
        }

        if matches!(method, "chr" | "to_char") {
            let recv = self.get(receiver)?;
            let result = self.call_runtime("char_from_code", &[recv])?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
            return Ok(());
        }

        if matches!(method, "min" | "max") && args.len() == 1 {
            let lhs = self.get(receiver)?;
            let rhs = self.get(args[0])?;
            let lhs = match lhs {
                BasicValueEnum::IntValue(v) => v,
                _ => return Err(format!("unsupported receiver kind for '{}' method", method)),
            };
            let rhs = match rhs {
                BasicValueEnum::IntValue(v) => v,
                _ => return Err(format!("unsupported argument kind for '{}' method", method)),
            };
            let lhs64 = if lhs.get_type() == self.backend.runtime_int_type() {
                lhs
            } else {
                self.builder
                    .build_int_z_extend(lhs, self.backend.runtime_int_type(), "int_minmax_lhs")
                    .map_err(|e| format!("LLVM int zext failed: {}", e))?
            };
            let rhs64 = if rhs.get_type() == self.backend.runtime_int_type() {
                rhs
            } else {
                self.builder
                    .build_int_z_extend(rhs, self.backend.runtime_int_type(), "int_minmax_rhs")
                    .map_err(|e| format!("LLVM int zext failed: {}", e))?
            };
            let pred = if method == "min" {
                inkwell::IntPredicate::SLE
            } else {
                inkwell::IntPredicate::SGE
            };
            let cmp = self
                .builder
                .build_int_compare(pred, lhs64, rhs64, "int_minmax_cmp")
                .map_err(|e| format!("LLVM int compare failed: {}", e))?;
            let value = self
                .builder
                .build_select(cmp, lhs64, rhs64, "int_minmax_select")
                .map_err(|e| format!("LLVM select failed: {}", e))?;
            if let Some(d) = dest {
                self.set(*d, value);
            }
            return Ok(());
        }

        if method == "repeat" && args.len() == 1 {
            let mut all_args = vec![receiver];
            all_args.extend_from_slice(args);
            self.emit_call(
                dest,
                &CallTarget::from_name("lib__common__string_core__str_repeat"),
                &all_args,
            )?;
            return Ok(());
        }

        if method == "merge" && args.len() == 1 {
            let recv = self.get(receiver)?;
            let other = self.get(args[0])?;
            let count = self.call_runtime("rt_len", &[other])?;
            let _ = self.call_runtime_bool_as_int("rt_array_extend_i64", &[recv, other, count])?;
            if let Some(d) = dest {
                self.set(*d, recv);
            }
            return Ok(());
        }

        if let Some(rt_name) = Self::runtime_method_name(method) {
            let recv = self.get(receiver)?;
            let mut rt_args = vec![recv];
            for arg in args {
                rt_args.push(self.get(*arg)?);
            }
            let result = if matches!(method, "unwrap_or") && rt_args.len() > 1 {
                // Keep the ABI simple here: unresolved lowering should not emit a fake
                // method symbol, and the runtime helper still uses the first arg payload.
                self.call_runtime(rt_name, &rt_args[..1])?
            } else {
                self.call_runtime(rt_name, &rt_args)?
            };
            if let Some(d) = dest {
                self.set(*d, result);
            }
            return Ok(());
        }

        // Static method call: prepend receiver to args and call function.
        let mut all_args = vec![receiver];
        all_args.extend_from_slice(args);
        self.emit_call(dest, &CallTarget::from_name(func_name), &all_args)
    }

    fn emit_method_call_virtual(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        vtable_slot: usize,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
    ) -> Result<(), String> {
        // Virtual dispatch: call runtime to resolve vtable
        let recv = self.get(receiver)?;
        let slot = self.i64_const(vtable_slot as i64);
        let func_ptr = self.call_runtime("rt_vtable_lookup", &[recv, slot])?;

        // Build indirect call with the resolved function pointer
        let mut all_args = vec![receiver];
        all_args.extend_from_slice(args);

        let mut all_param_types = vec![TypeId::I64]; // receiver type
        all_param_types.extend_from_slice(param_types);

        // Store the function pointer temporarily
        let temp = VReg(u32::MAX - 1);
        self.set(temp, func_ptr);
        self.emit_indirect_call(dest, temp, &all_param_types, return_type, &all_args, Effect::Compute)
    }

    fn emit_builtin_method(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        receiver_type: &str,
        method: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        let rt_name = format!("rt_builtin_{}_{}", receiver_type, method);
        let recv = self.get(receiver)?;
        let mut rt_args = vec![recv];
        for arg in args {
            rt_args.push(self.get(*arg)?);
        }
        let result = self.call_runtime(&rt_name, &rt_args)?;
        if let Some(d) = dest {
            self.set(*d, result);
        }
        Ok(())
    }

    fn emit_extern_method_call(
        &mut self,
        dest: &Option<VReg>,
        receiver: Option<VReg>,
        class_name: &str,
        method_name: &str,
        _is_static: bool,
        args: &[VReg],
    ) -> Result<(), String> {
        let rt_name = format!("{}_{}", class_name, method_name);
        let mut rt_args = Vec::new();
        if let Some(recv) = receiver {
            rt_args.push(self.get(recv)?);
        }
        for arg in args {
            rt_args.push(self.get(*arg)?);
        }
        if rt_args.is_empty() {
            let result = self.call_runtime(&rt_name, &[])?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
        } else {
            let result = self.call_runtime(&rt_name, &rt_args)?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
        }
        Ok(())
    }

    // =========================================================================
    // Pattern matching — delegate to runtime
    // =========================================================================
    fn emit_pattern_test(&mut self, dest: VReg, subject: VReg, _pattern: &MirPattern) -> Result<(), String> {
        let subj = self.get(subject)?;
        let result = self.call_runtime("rt_pattern_test", &[subj])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_pattern_bind(&mut self, dest: VReg, subject: VReg, _binding: &PatternBinding) -> Result<(), String> {
        let subj = self.get(subject)?;
        let result = self.call_runtime("rt_pattern_bind", &[subj])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Enums / Unions — delegate to runtime
    // =========================================================================
    fn emit_enum_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_enum_discriminant", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_enum_payload(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_enum_payload", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_enum_unit(&mut self, dest: VReg, _enum_name: &str, _variant_name: &str) -> Result<(), String> {
        // Enum unit variant: encode as tagged integer (discriminant only)
        let result = self.call_runtime("rt_enum_unit", &[self.i64_const(0)])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_enum_with(
        &mut self,
        dest: VReg,
        _enum_name: &str,
        _variant_name: &str,
        payload: VReg,
    ) -> Result<(), String> {
        let pay = self.get(payload)?;
        let result = self.call_runtime("rt_enum_with", &[pay])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_union_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_union_discriminant", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_union_payload(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_union_payload", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_union_wrap(&mut self, dest: VReg, value: VReg, type_index: u32) -> Result<(), String> {
        let val = self.get(value)?;
        let idx = self.i64_const(type_index as i64);
        let result = self.call_runtime("rt_union_wrap", &[val, idx])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Async / Concurrency — delegate to runtime
    // =========================================================================
    fn emit_future_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        let block_id = self.i64_const(body_block.0 as i64);
        let result = self.call_runtime("rt_future_create", &[block_id])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_await(&mut self, dest: VReg, future: VReg) -> Result<(), String> {
        let fut = self.get(future)?;
        let result = self.call_runtime("rt_future_await", &[fut])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_spawn(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        let block_id = self.i64_const(body_block.0 as i64);
        let result = self.call_runtime("rt_actor_spawn", &[block_id])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_send(&mut self, actor: VReg, message: VReg) -> Result<(), String> {
        let act = self.get(actor)?;
        let msg = self.get(message)?;
        self.call_runtime_void("rt_actor_send", &[act, msg])
    }

    fn emit_actor_recv(&mut self, dest: VReg) -> Result<(), String> {
        let result = self.call_runtime("rt_actor_recv", &[])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_join(&mut self, dest: VReg, actor: VReg) -> Result<(), String> {
        let act = self.get(actor)?;
        let result = self.call_runtime("rt_actor_join", &[act])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_reply(&mut self, message: VReg) -> Result<(), String> {
        let msg = self.get(message)?;
        self.call_runtime_void("rt_actor_reply", &[msg])
    }

    fn emit_generator_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        let block_id = self.i64_const(body_block.0 as i64);
        let result = self.call_runtime("rt_generator_create", &[block_id])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_yield(&mut self, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        self.call_runtime_void("rt_generator_yield", &[val])
    }

    fn emit_generator_next(&mut self, dest: VReg, generator: VReg) -> Result<(), String> {
        let gen = self.get(generator)?;
        let result = self.call_runtime("rt_generator_next", &[gen])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Result / Option — delegate to runtime
    // =========================================================================
    fn emit_try_unwrap(
        &mut self,
        dest: VReg,
        value: VReg,
        _error_block: BlockId,
        _error_dest: VReg,
    ) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_try_unwrap", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_option_some(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_option_some", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_option_none(&mut self, dest: VReg) -> Result<(), String> {
        let result = self.call_runtime("rt_option_none", &[])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_result_ok(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_result_ok", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_result_err(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_result_err", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Contracts — delegate to runtime
    // =========================================================================
    fn emit_contract_check(
        &mut self,
        condition: VReg,
        _kind: ContractKind,
        _func_name: &str,
        _message: Option<&str>,
    ) -> Result<(), String> {
        let cond = self.get(condition)?;
        self.call_runtime_void("rt_contract_check", &[cond])
    }

    fn emit_contract_old_capture(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        // Old capture: just copy the value (snapshot semantics)
        let val = self.get(value)?;
        self.set(dest, val);
        Ok(())
    }

    // =========================================================================
    // Coverage — delegate to runtime
    // =========================================================================
    // The admitted core-C coverage ABI records the source location with each
    // outcome.  The legacy `rt_decision_probe` and `rt_condition_probe` helpers
    // cannot produce a receipt-qualified row because they accept no file or
    // span.  Do not route native coverage through them: use the SFFI-stable
    // `rt_coverage_*` functions declared in `runtime_sffi.rs`.
    fn emit_decision_probe(
        &mut self,
        result: VReg,
        decision_id: u32,
        file: &str,
        line: u32,
        column: u32,
    ) -> Result<(), String> {
        let res = self.get(result)?;
        let id = self.i64_const(decision_id as i64);
        let file_value = self.coverage_file_value(file)?;
        let line_value = self.i64_const(line as i64);
        let column_value = self.i64_const(column as i64);
        self.call_runtime_void(
            "rt_coverage_decision_probe",
            &[id, res, file_value, line_value, column_value],
        )
    }

    fn emit_condition_probe(
        &mut self,
        decision_id: u32,
        condition_id: u32,
        result: VReg,
        file: &str,
        line: u32,
        column: u32,
    ) -> Result<(), String> {
        let res = self.get(result)?;
        let did = self.i64_const(decision_id as i64);
        let cid = self.i64_const(condition_id as i64);
        let file_value = self.coverage_file_value(file)?;
        let line_value = self.i64_const(line as i64);
        let column_value = self.i64_const(column as i64);
        self.call_runtime_void(
            "rt_coverage_condition_probe",
            &[did, cid, res, file_value, line_value, column_value],
        )
    }

    fn emit_path_probe(&mut self, path_id: u32, block_id: u32) -> Result<(), String> {
        let pid = self.i64_const(path_id as i64);
        let bid = self.i64_const(block_id as i64);
        self.call_runtime_void("rt_path_probe", &[pid, bid])
    }

    // =========================================================================
    // Units — inline LLVM IR (icmp + select)
    // =========================================================================
    fn emit_unit_bound_check(
        &mut self,
        value: VReg,
        _unit_name: &str,
        min: i64,
        max: i64,
        _overflow: UnitOverflowBehavior,
    ) -> Result<(), String> {
        let val = self.get(value)?;
        let min_val = self.i64_const(min);
        let max_val = self.i64_const(max);
        self.call_runtime_void("rt_unit_bound_check", &[val, min_val, max_val])
    }

    fn emit_unit_widen(
        &mut self,
        dest: VReg,
        value: VReg,
        _from_bits: u8,
        _to_bits: u8,
        _signed: bool,
    ) -> Result<(), String> {
        // Widen: at the LLVM level with uniform i64 representation, this is a copy
        let val = self.get(value)?;
        self.set(dest, val);
        Ok(())
    }

    fn emit_unit_narrow(
        &mut self,
        dest: VReg,
        value: VReg,
        _from_bits: u8,
        _to_bits: u8,
        _signed: bool,
        _overflow: UnitOverflowBehavior,
    ) -> Result<(), String> {
        // Narrow: at the LLVM level with uniform i64, this is a copy (bounds checked elsewhere)
        let val = self.get(value)?;
        self.set(dest, val);
        Ok(())
    }

    fn emit_unit_saturate(&mut self, dest: VReg, value: VReg, min: i64, max: i64) -> Result<(), String> {
        let val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let i64_type = self.backend.runtime_int_type();
            let min_v = i64_type.const_int(min as u64, true);
            let max_v = i64_type.const_int(max as u64, true);

            // clamp: max(min, min(val, max))
            let cmp_max = self
                .builder
                .build_int_compare(inkwell::IntPredicate::SLT, int_val, max_v, "cmp_max")
                .map_err(|e| format!("icmp failed: {}", e))?;
            let sel_max = self
                .builder
                .build_select(cmp_max, int_val, max_v, "sel_max")
                .map_err(|e| format!("select failed: {}", e))?;

            if let BasicValueEnum::IntValue(clamped_high) = sel_max {
                let cmp_min = self
                    .builder
                    .build_int_compare(inkwell::IntPredicate::SGT, clamped_high, min_v, "cmp_min")
                    .map_err(|e| format!("icmp failed: {}", e))?;
                let sel_min = self
                    .builder
                    .build_select(cmp_min, clamped_high, min_v, "sel_min")
                    .map_err(|e| format!("select failed: {}", e))?;
                self.set(dest, sel_min);
            } else {
                self.set(dest, val);
            }
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    // =========================================================================
    // Pointers — delegate to runtime
    // =========================================================================
    fn emit_pointer_new(&mut self, dest: VReg, _kind: PointerKind, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_pointer_new", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_pointer_ref(&mut self, dest: VReg, _kind: PointerKind, source: VReg) -> Result<(), String> {
        let val = self.get(source)?;
        let result = self.call_runtime("rt_pointer_ref", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_pointer_deref(&mut self, dest: VReg, pointer: VReg, _kind: PointerKind) -> Result<(), String> {
        let val = self.get(pointer)?;
        let result = self.call_runtime("rt_pointer_deref", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Memory safety — no-ops (use trait defaults)
    // =========================================================================
    fn emit_drop(&mut self, _value: VReg, _ty: TypeId) -> Result<(), String> {
        Ok(())
    }

    fn emit_end_scope(&mut self, _local_index: usize) -> Result<(), String> {
        Ok(())
    }

    // =========================================================================
    // Boxing (SFFI boundary) — inline LLVM IR
    // =========================================================================
    fn emit_box_int(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let mut val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let val_type = int_val.get_type();
            let rv_type = self.backend.runtime_int_type();
            let rv_width = rv_type.get_bit_width();
            let mut int_v = int_val;
            if val_type.get_bit_width() < rv_width {
                int_v = self
                    .builder
                    .build_int_s_extend(int_val, rv_type, "sext")
                    .map_err(|e| format!("sext failed: {}", e))?;
            } else if val_type.get_bit_width() > rv_width {
                int_v = self
                    .builder
                    .build_int_truncate(int_val, rv_type, "trunc")
                    .map_err(|e| format!("trunc failed: {}", e))?;
            }
            let three = rv_type.const_int(3, false);
            let boxed = self
                .builder
                .build_left_shift(int_v, three, "box_shl")
                .map_err(|e| format!("shl failed: {}", e))?;
            self.set(dest, boxed.into());
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_box_float(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let boxed = self
            .backend
            .build_box_float_value(val, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, boxed.into());
        Ok(())
    }

    fn emit_unbox_int(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let i64_type = self.backend.runtime_int_type();
            let three = i64_type.const_int(3, false);
            let unboxed = self
                .builder
                .build_right_shift(int_val, three, true, "unbox_sshr")
                .map_err(|e| format!("sshr failed: {}", e))?;
            self.set(dest, unboxed.into());
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_unbox_float(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let unboxed = self
            .backend
            .build_unbox_float_value(val, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, unboxed.into());
        Ok(())
    }

    // =========================================================================
    // GPU instructions — delegate to LlvmBackend helpers
    // =========================================================================
    fn emit_gpu_global_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_global_id(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_local_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_local_id(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_group_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_group_id(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_global_size(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_global_size(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_local_size(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_local_size(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_num_groups(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_num_groups(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_barrier(&mut self) -> Result<(), String> {
        self.backend
            .compile_gpu_barrier(self.builder, self.module)
            .map_err(|e| e.to_string())
    }

    fn emit_gpu_mem_fence(&mut self, scope: GpuMemoryScope) -> Result<(), String> {
        self.backend
            .compile_gpu_mem_fence(scope, self.builder, self.module)
            .map_err(|e| e.to_string())
    }

    fn emit_gpu_shared_alloc(&mut self, dest: VReg, _element_type: TypeId, size: u32) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_shared_alloc(size, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_atomic(&mut self, dest: VReg, op: GpuAtomicOp, ptr: VReg, value: VReg) -> Result<(), String> {
        let ptr_val = self.get(ptr)?;
        let value_val = self.get(value)?;
        let result = self
            .backend
            .compile_gpu_atomic(op, ptr_val, value_val, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_atomic_cmpxchg(&mut self, dest: VReg, ptr: VReg, expected: VReg, desired: VReg) -> Result<(), String> {
        let ptr_val = self.get(ptr)?;
        let expected_val = self.get(expected)?;
        let desired_val = self.get(desired)?;
        let result = self
            .backend
            .compile_gpu_atomic_cmpxchg(ptr_val, expected_val, desired_val, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }
    fn emit_gpu_load_f64(&mut self, dest: VReg, _ptr: VReg, _index: VReg) -> Result<(), String> {
        // GPU memory ops not used in LLVM AOT path — stub
        let val = self.backend.runtime_int_type().const_int(0, false);
        self.set(dest, val.into());
        Ok(())
    }
    fn emit_gpu_store_f64(&mut self, _ptr: VReg, _index: VReg, _value: VReg) -> Result<(), String> {
        // GPU memory ops not used in LLVM AOT path — stub
        Ok(())
    }
    fn emit_gpu_load_i64(&mut self, dest: VReg, _ptr: VReg, _index: VReg) -> Result<(), String> {
        // GPU memory ops not used in LLVM AOT path — stub
        let val = self.backend.runtime_int_type().const_int(0, false);
        self.set(dest, val.into());
        Ok(())
    }
    fn emit_gpu_store_i64(&mut self, _ptr: VReg, _index: VReg, _value: VReg) -> Result<(), String> {
        // GPU memory ops not used in LLVM AOT path — stub
        Ok(())
    }

    // =========================================================================
    // Parallel iterators — delegate to runtime
    // =========================================================================
    fn emit_par_map(
        &mut self,
        dest: VReg,
        input: VReg,
        closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let cls = self.get(closure)?;
        let result = self.call_runtime("rt_par_map", &[inp, cls])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_par_reduce(
        &mut self,
        dest: VReg,
        input: VReg,
        initial: VReg,
        closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let init = self.get(initial)?;
        let cls = self.get(closure)?;
        let result = self.call_runtime("rt_par_reduce", &[inp, init, cls])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_par_filter(
        &mut self,
        dest: VReg,
        input: VReg,
        predicate: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let pred = self.get(predicate)?;
        let result = self.call_runtime("rt_par_filter", &[inp, pred])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_par_for_each(
        &mut self,
        input: VReg,
        closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let cls = self.get(closure)?;
        self.call_runtime_void("rt_par_for_each", &[inp, cls])
    }
}

#[cfg(all(test, feature = "llvm"))]
mod tests {
    use super::LlvmEmitter;

    #[test]
    fn llvm_runtime_method_name_covers_freestanding_leaks() {
        assert_eq!(LlvmEmitter::runtime_method_name("rfind"), Some("rt_string_rfind"));
        assert_eq!(LlvmEmitter::runtime_method_name("has"), Some("rt_contains"));
        assert_eq!(LlvmEmitter::runtime_method_name("repeat"), None);
        assert_eq!(LlvmEmitter::runtime_method_name("unwrap_err"), Some("rt_enum_payload"));
        assert_eq!(LlvmEmitter::runtime_method_name("to_string"), Some("rt_to_string"));
    }

    /// The type-BLIND table must not send a receiver-polymorphic method to a
    /// receiver-SPECIFIC helper. Each assertion pairs the dead name being gone
    /// with the live emission still being there, so deleting an arm cannot
    /// satisfy this test.
    #[test]
    fn llvm_bare_names_route_polymorphic_methods_to_polymorphic_helpers() {
        // `find`: `rt_string_find` answers -1 for every array receiver.
        assert_eq!(LlvmEmitter::runtime_method_name("find"), Some("rt_find"));
        // ...but the text-only spelling still goes straight to the text helper.
        assert_eq!(LlvmEmitter::runtime_method_name("find_str"), Some("rt_string_find"));

        // `reverse`: `rt_array_reverse` reverses IN PLACE and returns a bool.
        // `reverse` is the MUTATING spelling and must NOT share a helper with
        // `rev`/`reversed`. This assertion used to demand `rt_reverse` for
        // `reverse`, pinning the divergence: only `reverse` is in the
        // interpreter's `MUTATING_METHODS`, so only it rebinds the receiver.
        assert_eq!(LlvmEmitter::runtime_method_name("reverse"), Some("rt_reverse_mut"));
        assert_ne!(
            LlvmEmitter::runtime_method_name("reverse"),
            Some("rt_reverse"),
            "the copying helper is the rev/reversed contract, not reverse's"
        );
        // NOTE: this table has no `rev`/`reversed` arm at all, unlike the two
        // Cranelift tables. That gap is recorded in the bug tracker; it is NOT
        // filled here because this lane has no measurement of the LLVM path for
        // those spellings, and adding an unverified route would be the same
        // class of mistake this change is undoing.

        // `sort`: same shape — `rt_array_sort` sorts IN PLACE, returns a bool,
        // and does not exist in runtime_native.c at all.
        assert_eq!(LlvmEmitter::runtime_method_name("sort"), Some("rt_sort"));

        // Already-fixed siblings, asserted here so the family stays together.
        assert_eq!(LlvmEmitter::runtime_method_name("map"), Some("rt_map"));
        assert_eq!(LlvmEmitter::runtime_method_name("index_of"), Some("rt_index_of"));
        assert_eq!(LlvmEmitter::runtime_method_name("at"), Some("rt_at"));

        // Receiver-SPECIFIC methods must stay on their specific helpers; this is
        // the true-positive control that stops the test passing on a table that
        // simply routed everything through a polymorphic name.
        assert_eq!(LlvmEmitter::runtime_method_name("push"), Some("rt_array_push"));
        assert_eq!(LlvmEmitter::runtime_method_name("split"), Some("rt_string_split"));
        assert_eq!(LlvmEmitter::runtime_method_name("keys"), Some("rt_dict_keys"));
    }

    /// `call_runtime_void` used to declare every parameter as
    /// `runtime_int_type()`. These are the specs it now reads instead; if the
    /// spec table stops carrying the real widths, the narrowing it does becomes
    /// a no-op again and this catches it.
    #[test]
    fn runtime_sffi_specs_carry_the_real_void_call_widths() {
        use crate::codegen::runtime_sffi::spec_for;
        use cranelift_codegen::ir::types;

        // rt_decision_probe(decision_id: u64, result: bool)
        let d = spec_for("rt_decision_probe").expect("rt_decision_probe spec");
        assert_eq!(d.params, &[types::I64, types::I8]);
        assert!(d.returns.is_empty(), "rt_decision_probe is void");

        // rt_condition_probe(decision_id: u64, condition_id: u32, result: bool)
        let c = spec_for("rt_condition_probe").expect("rt_condition_probe spec");
        assert_eq!(c.params, &[types::I64, types::I32, types::I8]);

        // rt_actor_reply RETURNS a value; call_runtime_void used to declare it
        // void, leaving two disagreeing declarations of one symbol in play.
        let r = spec_for("rt_actor_reply").expect("rt_actor_reply spec");
        assert_eq!(r.returns, &[types::I64]);

        // rt_par_for_each: the emitter passes 2 operands against 4 declared.
        // The arity check in call_runtime_void must therefore FAIL CLOSED and
        // leave the symbol loud rather than quietly declaring the 4-arg form.
        let p = spec_for("rt_par_for_each").expect("rt_par_for_each spec");
        assert_eq!(p.params.len(), 4, "operand-dropping emitter must stay visible");

        // Symbols with no spec at all must report None rather than a guess.
        assert!(spec_for("rt_contract_check").is_none());
        assert!(spec_for("rt_unit_bound_check").is_none());
        assert!(spec_for("rt_generator_yield").is_none());

        // Positive control: the lookup really does find things.
        assert_eq!(spec_for("rt_find").map(|s| s.params.len()), Some(2));
        assert!(spec_for("rt_this_symbol_does_not_exist").is_none());
    }

    #[test]
    fn llvm_method_leaf_name_handles_qualified_symbols() {
        assert_eq!(LlvmEmitter::method_leaf_name("Result.unwrap_err"), "unwrap_err");
        assert_eq!(LlvmEmitter::method_leaf_name("to_u32"), "to_u32");
    }

    /// Regression guard for native receipt-qualified coverage lowering.
    ///
    /// The core-C runtime is the only admitted ML-KEM coverage bundle.  Its
    /// probe ABI includes a source pointer and span; the old two/three-argument
    /// helpers cannot be used because they lose the owner identity needed by
    /// the receipt composer.  Check both native calls and the retained file
    /// conversion so deleting instrumentation cannot satisfy the test.
    #[test]
    fn llvm_emitter_probes_call_core_c_coverage_abi_with_source_identity() {
        // Search the EMITTER code only, never this test module — otherwise the
        // assertions below would match their own text and be vacuous in both
        // directions.
        let src = include_str!("emitter.rs");
        let split = src
            .find("#[cfg(all(test, feature = \"llvm\"))]")
            .expect("test module marker");
        let code = &src[..split];

        // Negative: legacy helpers omit file/line/column and cannot yield an
        // owner-qualified core-C row.  Names are assembled to exclude this test
        // body itself from the source scan.
        for suffix in ["decision", "condition"] {
            let legacy = format!("\"rt_{}_probe\"", suffix);
            assert!(
                !code.contains(&legacy),
                "legacy rt_{}_probe drops the source location required by core-C coverage",
                suffix
            );
        }

        // Positive control: decision and condition calls must retain every ABI
        // field, including an immutable source name converted to the runtime
        // pointer slot.
        for kind in ["decision", "condition"] {
            let live = format!("\"rt_coverage_{}_probe\"", kind);
            assert!(
                code.contains(&live),
                "rt_coverage_{}_probe must still be emitted; a silent probe path would \
                 satisfy the negative assertions above without fixing anything",
                kind
            );
        }
        assert!(
            code.contains("fn coverage_file_value")
                && code.contains("build_ptr_to_int(pointer")
                && code.contains("bytes.push(0)"),
            "coverage lowering must retain a NUL-terminated immutable file name"
        );
        assert!(
            code.contains(&format!(
                "{}\"rt_coverage_decision_probe\", &[id, res, file_value, line_value, column_value]",
                "call_runtime_void("
            )),
            "decision coverage must pass id, result, file, line, and column"
        );
        assert!(
            code.contains(&format!(
                "{}\"rt_coverage_condition_probe\", &[did, cid, res, file_value, line_value, column_value]",
                "call_runtime_void("
            )),
            "condition coverage must pass id, condition id, result, file, line, and column"
        );
    }
}
