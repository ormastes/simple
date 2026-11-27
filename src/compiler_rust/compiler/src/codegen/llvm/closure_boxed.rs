//! Boxed-entry closure thunks and uniform `RuntimeClosure` ABI helpers for LLVM.
//!
//! Mirrors `codegen/closure_boxed_entry.rs` + `codegen/instr/closures_structs.rs`:
//! every outlined lambda `L` and first-class function value `F` gets an
//! all-`RuntimeValue` companion thunk `L$boxed(ctx, arg0, ...) -> RuntimeValue`,
//! and `compile_closure_create` / `GlobalLoad` / `generate_module_init` allocate
//! a tagged `RuntimeClosure` via `rt_closure_new` / `rt_closure_set_capture`.
//! Runtime helpers (`rt_array_map`, `rt_option_map`, `rt_map`, ...) and
//! `compile_indirect_call` then enter through `rt_closure_func_ptr` cleanly.

use super::LlvmBackend;
use crate::error::CompileError;
use crate::hir::TypeId;
use crate::mir::{MirFunction, MirModule};

#[cfg(feature = "llvm")]
use crate::codegen::closure_boxed_entry::{
    boxed_entry_name, imported_fn_value_targets, is_outlined_lambda, is_raw_scalar, named_fn_value_targets,
};
#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::{Linkage, Module};
#[cfg(feature = "llvm")]
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue};
#[cfg(feature = "llvm")]
use inkwell::IntPredicate;

#[cfg(feature = "llvm")]
impl LlvmBackend {
    pub(in crate::codegen::llvm) fn declare_rt_closure_new(
        &self,
        module: &Module<'static>,
    ) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        module
            .get_function("rt_closure_new")
            .unwrap_or_else(|| module.add_function("rt_closure_new", rv.fn_type(&[rv.into(), rv.into()], false), None))
    }

    pub(in crate::codegen::llvm) fn declare_rt_closure_set_capture(
        &self,
        module: &Module<'static>,
    ) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        let i8_ty = self.context_ref().i8_type();
        module.get_function("rt_closure_set_capture").unwrap_or_else(|| {
            module.add_function(
                "rt_closure_set_capture",
                i8_ty.fn_type(&[rv.into(), rv.into(), rv.into()], false),
                None,
            )
        })
    }

    pub(in crate::codegen::llvm) fn declare_rt_closure_get_capture(
        &self,
        module: &Module<'static>,
    ) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        module.get_function("rt_closure_get_capture").unwrap_or_else(|| {
            module.add_function("rt_closure_get_capture", rv.fn_type(&[rv.into(), rv.into()], false), None)
        })
    }

    pub(in crate::codegen::llvm) fn declare_rt_closure_func_ptr(
        &self,
        module: &Module<'static>,
    ) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        module
            .get_function("rt_closure_func_ptr")
            .unwrap_or_else(|| module.add_function("rt_closure_func_ptr", rv.fn_type(&[rv.into()], false), None))
    }

    fn declare_rt_value_int(&self, module: &Module<'static>) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        module
            .get_function("rt_value_int")
            .unwrap_or_else(|| module.add_function("rt_value_int", rv.fn_type(&[rv.into()], false), None))
    }

    fn declare_rt_value_bool(&self, module: &Module<'static>) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        module
            .get_function("rt_value_bool")
            .unwrap_or_else(|| module.add_function("rt_value_bool", rv.fn_type(&[rv.into()], false), None))
    }

    fn declare_rt_value_float(&self, module: &Module<'static>) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        let f64_ty = self.context_ref().f64_type();
        module
            .get_function("rt_value_float")
            .unwrap_or_else(|| module.add_function("rt_value_float", rv.fn_type(&[f64_ty.into()], false), None))
    }

    fn declare_rt_value_unbox_int(&self, module: &Module<'static>) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        module
            .get_function("rt_value_unbox_int")
            .unwrap_or_else(|| module.add_function("rt_value_unbox_int", rv.fn_type(&[rv.into()], false), None))
    }

    fn declare_rt_value_as_float(&self, module: &Module<'static>) -> FunctionValue<'static> {
        let rv = self.runtime_int_type();
        let f64_ty = self.context_ref().f64_type();
        module
            .get_function("rt_value_as_float")
            .unwrap_or_else(|| module.add_function("rt_value_as_float", f64_ty.fn_type(&[rv.into()], false), None))
    }

    /// Emit `L$boxed` / `F$boxed` entry thunks for every outlined lambda and
    /// first-class function value in `mir`.
    pub(in crate::codegen::llvm) fn emit_boxed_closure_entries(&self, mir: &MirModule) -> Result<(), CompileError> {
        for func in &mir.functions {
            if !func.blocks.is_empty() && is_outlined_lambda(func) {
                self.emit_boxed_entry_for_mir_fn(func, true)?;
            }
        }
        for name in named_fn_value_targets(mir) {
            if let Some(func) = mir.functions.iter().find(|f| f.name == name) {
                self.emit_boxed_entry_for_mir_fn(func, false)?;
            }
        }
        for (name, params, ret) in imported_fn_value_targets(mir) {
            self.emit_boxed_import_entry(mir, &name, &params, ret)?;
        }
        let mut init_functions: Vec<(&String, &String)> = mir.global_init_functions.iter().collect();
        init_functions.sort();
        for (global_name, func_name) in init_functions {
            if mir.extern_fn_names.contains(func_name.as_str()) {
                continue;
            }
            if let Some(func) = mir
                .functions
                .iter()
                .find(|f| &f.name == func_name && !f.blocks.is_empty())
            {
                self.emit_boxed_entry_for_mir_fn(func, false)?;
                continue;
            }
            let fn_ty = mir
                .globals
                .iter()
                .find(|(name, _, _)| name == global_name)
                .and_then(|(_, ty, _)| mir.type_registry.get(*ty));
            if let Some(crate::hir::HirType::Function { params, ret }) = fn_ty {
                self.emit_boxed_import_entry(mir, func_name, params, *ret)?;
            }
        }
        Ok(())
    }

    /// Lazily emit a boxed entry thunk for `raw_target` when a unit test calls
    /// `compile_closure_create` outside `LlvmBackend::compile`.
    pub(in crate::codegen::llvm) fn ensure_boxed_entry_for_existing_fn(
        &self,
        func_name: &str,
        arg_count: usize,
        module: &Module<'static>,
        builder: &Builder<'static>,
    ) -> Result<Option<FunctionValue<'static>>, CompileError> {
        let boxed_name = boxed_entry_name(func_name);
        if let Some(existing) = module.get_function(&boxed_name) {
            return Ok(Some(existing));
        }
        let sanitized = func_name.replace('.', "_dot_");
        if let Some(existing) = module.get_function(&boxed_entry_name(&sanitized)) {
            return Ok(Some(existing));
        }
        let Some(target) = module
            .get_function(func_name)
            .or_else(|| module.get_function(&sanitized))
        else {
            return Ok(None);
        };
        let target_params = target.count_params() as usize;
        let has_ctx = target_params > arg_count;
        let user_param_count = if has_ctx {
            target_params - 1
        } else {
            target_params
        };
        let user_params = vec![TypeId::ANY; user_param_count];
        let saved_block = builder.get_insert_block();
        let thunk = self.emit_boxed_thunk(&boxed_name, target, &user_params, TypeId::ANY, has_ctx, module, builder)?;
        if let Some(bb) = saved_block {
            builder.position_at_end(bb);
        }
        Ok(Some(thunk))
    }

    fn emit_boxed_entry_for_mir_fn(&self, func: &MirFunction, has_ctx: bool) -> Result<(), CompileError> {
        let module_ref = self.module.borrow();
        let module = module_ref
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;
        let builder_ref = self.builder.borrow();
        let builder = builder_ref
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_builder_not_created)?;
        let boxed_name = boxed_entry_name(&func.name);
        if module.get_function(&boxed_name).is_some() {
            return Ok(());
        }
        let Some(target) = module.get_function(&func.name) else {
            return Ok(());
        };
        let skip = usize::from(has_ctx);
        let user_params: Vec<TypeId> = func.params.iter().skip(skip).map(|p| p.ty).collect();
        let returns_bool = func
            .outlined_bodies
            .get(&func.entry_block)
            .is_some_and(|meta| meta.lambda_returns_bool);
        let ret_ty = if returns_bool {
            TypeId::BOOL
        } else {
            func.return_type
        };
        self.emit_boxed_thunk(&boxed_name, target, &user_params, ret_ty, has_ctx, module, builder)?;
        Ok(())
    }

    fn emit_boxed_import_entry(
        &self,
        mir: &MirModule,
        name: &str,
        user_params: &[TypeId],
        ret_ty: TypeId,
    ) -> Result<(), CompileError> {
        let module_ref = self.module.borrow();
        let module = module_ref
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;
        let builder_ref = self.builder.borrow();
        let builder = builder_ref
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_builder_not_created)?;
        let boxed_name = boxed_entry_name(name);
        if module.get_function(&boxed_name).is_some() {
            return Ok(());
        }
        let resolved = self
            .use_map
            .get(name)
            .or_else(|| self.import_map.get(name))
            .map(|s| s.as_str())
            .unwrap_or(name);
        let sanitized = resolved.replace('.', "_dot_");
        if self.data_exports.contains(resolved) || self.data_exports.contains(&sanitized) {
            return Ok(());
        }
        let rv = self.runtime_int_type();
        let target = module
            .get_function(name)
            .or_else(|| module.get_function(resolved))
            .or_else(|| module.get_function(&sanitized))
            .unwrap_or_else(|| {
                let param_tys: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    user_params.iter().map(|_| rv.into()).collect();
                let fn_ty = rv.fn_type(&param_tys, false);
                let f = module.add_function(&sanitized, fn_ty, Some(Linkage::External));
                let _ = mir;
                f
            });
        self.emit_boxed_thunk(&boxed_name, target, user_params, ret_ty, false, module, builder)?;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_boxed_thunk(
        &self,
        boxed_name: &str,
        target: FunctionValue<'static>,
        user_params: &[TypeId],
        ret_ty: TypeId,
        has_ctx: bool,
        module: &Module<'static>,
        builder: &Builder<'static>,
    ) -> Result<FunctionValue<'static>, CompileError> {
        if let Some(existing) = module.get_function(boxed_name) {
            return Ok(existing);
        }

        let rv = self.runtime_int_type();
        let mut thunk_params: Vec<inkwell::types::BasicMetadataTypeEnum> = vec![rv.into()];
        thunk_params.extend(
            user_params
                .iter()
                .map(|_| inkwell::types::BasicMetadataTypeEnum::from(rv)),
        );
        let thunk_ty = rv.fn_type(&thunk_params, false);
        let thunk = module.add_function(boxed_name, thunk_ty, Some(Linkage::Internal));
        let entry = self.context_ref().append_basic_block(thunk, "entry");
        builder.position_at_end(entry);

        let closure_rv = thunk
            .get_nth_param(0)
            .ok_or_else(|| CompileError::semantic("boxed thunk missing closure parameter"))?;
        let mut call_args: Vec<BasicMetadataValueEnum> = if has_ctx {
            let expected = target.get_nth_param(0).map(|p| p.get_type());
            vec![self.coerce_value_to_type(closure_rv, expected, builder)?.into()]
        } else {
            Vec::new()
        };

        let ctx_offset = usize::from(has_ctx);
        for (i, ty) in user_params.iter().enumerate() {
            let tagged = thunk
                .get_nth_param((i + 1) as u32)
                .ok_or_else(|| CompileError::semantic("boxed thunk missing user parameter"))?;
            let unboxed = self.unbox_closure_boundary_value(tagged, *ty, builder, module)?;
            let want = target
                .get_nth_param((i + ctx_offset) as u32)
                .map(|p| p.get_type());
            call_args.push(self.coerce_value_to_type(unboxed, want, builder)?.into());
        }

        let call = builder
            .build_call(target, &call_args, "boxed_target_call")
            .map_err(|e| crate::error::factory::llvm_build_failed("boxed target call", &e))?;
        let boxed_ret = match call.try_as_basic_value().basic() {
            Some(_) if ret_ty == TypeId::VOID => rv.const_int(3, false).into(),
            Some(val) => self.box_closure_boundary_value(val, ret_ty, builder, module)?,
            None => rv.const_int(3, false).into(),
        };
        let boxed_rv = self.coerce_value_to_type(boxed_ret, Some(rv.into()), builder)?;
        builder
            .build_return(Some(&boxed_rv))
            .map_err(|e| crate::error::factory::llvm_build_failed("boxed thunk return", &e))?;
        Ok(thunk)
    }

    /// Encode a raw MIR/LLVM value into a tagged `RuntimeValue` (`rv_type`) for
    /// a boxed closure boundary (`ClosureCreate` thunk return or `IndirectCall` arg).
    pub(in crate::codegen::llvm) fn box_closure_boundary_value(
        &self,
        val: BasicValueEnum<'static>,
        ty: TypeId,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<BasicValueEnum<'static>, CompileError> {
        let rv = self.runtime_int_type();
        let f64_ty = self.context_ref().f64_type();
        match ty {
            TypeId::F32 | TypeId::F64 => {
                let float_val = self.coerce_value_to_type(val, Some(f64_ty.into()), builder)?;
                let box_fn = self.declare_rt_value_float(module);
                let call = builder
                    .build_call(box_fn, &[float_val.into()], "box_closure_float")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_float", &e))?;
                call.try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_float returned void"))
            }
            TypeId::BOOL => {
                let raw = self.coerce_value_to_type(val, Some(rv.into()), builder)?.into_int_value();
                let flag = builder
                    .build_int_compare(IntPredicate::NE, raw, rv.const_zero(), "bool_nz")
                    .map_err(|e| crate::error::factory::llvm_build_failed("icmp bool", &e))?;
                let widened = builder
                    .build_int_z_extend(flag, rv, "bool_rv")
                    .map_err(|e| crate::error::factory::llvm_build_failed("zext bool", &e))?;
                let box_fn = self.declare_rt_value_bool(module);
                let call = builder
                    .build_call(box_fn, &[widened.into()], "box_closure_bool")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_bool", &e))?;
                call.try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_bool returned void"))
            }
            t if is_raw_scalar(t) => {
                let raw = self.coerce_value_to_type(val, Some(rv.into()), builder)?;
                let box_fn = self.declare_rt_value_int(module);
                let call = builder
                    .build_call(box_fn, &[raw.into()], "box_closure_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_int", &e))?;
                call.try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_int returned void"))
            }
            TypeId::ANY if matches!(val, BasicValueEnum::FloatValue(_)) => {
                let float_val = self.coerce_value_to_type(val, Some(f64_ty.into()), builder)?;
                let box_fn = self.declare_rt_value_float(module);
                let call = builder
                    .build_call(box_fn, &[float_val.into()], "box_closure_any_float")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_float", &e))?;
                call.try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_float returned void"))
            }
            _ => self.coerce_value_to_type(val, Some(rv.into()), builder),
        }
    }

    /// Decode a tagged `RuntimeValue` (`rv_type`) from a boxed closure boundary
    /// back to LLVM's `rv_type` raw slot representation (bitcast `f64` bits in `i64` for floats).
    pub(in crate::codegen::llvm) fn unbox_closure_boundary_value(
        &self,
        tagged: BasicValueEnum<'static>,
        ty: TypeId,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<BasicValueEnum<'static>, CompileError> {
        let rv = self.runtime_int_type();
        let tagged_rv = self.coerce_value_to_type(tagged, Some(rv.into()), builder)?;
        match ty {
            TypeId::F32 | TypeId::F64 => {
                let unbox_fn = self.declare_rt_value_as_float(module);
                let call = builder
                    .build_call(unbox_fn, &[tagged_rv.into()], "unbox_closure_float")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_as_float", &e))?;
                let fval = call
                    .try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_as_float returned void"))?;
                self.coerce_value_to_type(fval, Some(rv.into()), builder)
            }
            TypeId::BOOL => {
                let unbox_fn = self.declare_rt_value_unbox_int(module);
                let call = builder
                    .build_call(unbox_fn, &[tagged_rv.into()], "unbox_closure_bool")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_unbox_int", &e))?;
                let raw = call
                    .try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_unbox_int returned void"))?
                    .into_int_value();
                let flag = builder
                    .build_int_compare(IntPredicate::NE, raw, rv.const_zero(), "unboxed_bool")
                    .map_err(|e| crate::error::factory::llvm_build_failed("icmp unboxed bool", &e))?;
                let widened = builder
                    .build_int_z_extend(flag, rv, "unboxed_bool_rv")
                    .map_err(|e| crate::error::factory::llvm_build_failed("zext unboxed bool", &e))?;
                Ok(widened.into())
            }
            t if is_raw_scalar(t) => {
                let unbox_fn = self.declare_rt_value_unbox_int(module);
                let call = builder
                    .build_call(unbox_fn, &[tagged_rv.into()], "unbox_closure_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_unbox_int", &e))?;
                call.try_as_basic_value()
                    .basic()
                    .ok_or_else(|| CompileError::semantic("rt_value_unbox_int returned void"))
            }
            _ => Ok(tagged_rv),
        }
    }

    /// Build a zero-capture `RuntimeClosure` via `rt_closure_new(fn_ptr, 0)` for a
    /// named function's `$boxed` entry, or `None` if no boxed entry exists.
    pub(in crate::codegen::llvm) fn build_zero_capture_boxed_closure(
        &self,
        boxed_fn: FunctionValue<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<BasicValueEnum<'static>, CompileError> {
        let rv = self.runtime_int_type();
        let closure_new = self.declare_rt_closure_new(module);
        let fn_addr = builder
            .build_ptr_to_int(boxed_fn.as_global_value().as_pointer_value(), rv, "boxed_fn_addr")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
        let call = builder
            .build_call(closure_new, &[fn_addr.into(), rv.const_zero().into()], "fn_closure")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_closure_new", &e))?;
        call.try_as_basic_value()
            .basic()
            .ok_or_else(|| CompileError::semantic("rt_closure_new returned void"))
    }
}

#[cfg(all(test, feature = "llvm"))]
mod tests {
    use super::*;
    use crate::codegen::backend_trait::NativeBackend;
    use simple_common::target::{Target, TargetArch, TargetOS};
    use simple_parser::Parser;

    fn compile_source_to_llvm_ir(source: &str) -> String {
        let ast = Parser::new(source).parse().expect("parse failed");
        let hir = crate::hir::lower(&ast).expect("hir lower failed");
        let mir = crate::mir::lower_to_mir(&hir).expect("mir lower failed");
        let mut backend = LlvmBackend::new(Target::new(TargetArch::X86_64, TargetOS::Linux)).unwrap();
        backend.compile(&mir).expect("llvm compile failed");
        backend.verify().expect("llvm ir verify failed");
        backend.get_ir().expect("get_ir failed")
    }

    #[test]
    fn array_map_method_ref_emits_runtime_closure_boxed_and_rt_map() {
        let ir = compile_source_to_llvm_ir(
            "fn parse_cols(raw_cols: [text]) -> [text]:\n    raw_cols.map(&:trim)\n",
        );
        assert!(ir.contains("@rt_closure_new("), "expected rt_closure_new in LLVM IR:\n{ir}");
        assert!(ir.contains("$boxed\""), "expected $boxed lambda thunk in LLVM IR:\n{ir}");
        assert!(ir.contains("@rt_map("), "expected rt_map call in LLVM IR:\n{ir}");
        assert!(
            !ir.contains("@rt_option_map("),
            "MethodCallStatic .map must route through rt_map, not rt_option_map:\n{ir}"
        );
        assert!(
            !ir.contains("@rt_alloc("),
            "zero-capture closure must not fall back to raw rt_alloc:\n{ir}"
        );
    }

    #[test]
    fn result_map_field_placeholder_emits_runtime_closure_and_rt_map() {
        let ir = compile_source_to_llvm_ir(
            "struct StorageRootResolution:\n    roots: text\n\nenum Result<T, E>:\n    Ok(T)\n    Err(E)\n\nfn inspect() -> Result<StorageRootResolution, text>:\n    Result.Ok(StorageRootResolution(roots: \"ok\"))\n\nfn resolve_roots():\n    inspect().map(_.roots)\n",
        );
        assert!(ir.contains("@rt_closure_new("), "expected rt_closure_new:\n{ir}");
        assert!(ir.contains("$boxed\""), "expected $boxed lambda thunk:\n{ir}");
        assert!(ir.contains("@rt_map("), "expected rt_map call:\n{ir}");
        assert!(
            !ir.contains("@rt_option_map("),
            "Result.map must route through rt_map:\n{ir}"
        );
    }

    #[test]
    fn captured_scalar_closure_uses_rt_closure_capture_apis_and_boxed_indirect_call() {
        let ir = compile_source_to_llvm_ir(
            "fn scale_all(xs: [i64], offset: i64) -> [bool]:\n    val pred = \\x: (x + offset) > 0\n    val _checked = pred(5)\n    xs.map(\\y: (y + offset) > 0)\n",
        );
        assert!(ir.contains("@rt_closure_new("), "expected rt_closure_new:\n{ir}");
        assert!(ir.contains("@rt_closure_set_capture("), "expected rt_closure_set_capture:\n{ir}");
        assert!(ir.contains("@rt_closure_get_capture("), "expected rt_closure_get_capture:\n{ir}");
        assert!(ir.contains("@rt_closure_func_ptr("), "expected rt_closure_func_ptr in IndirectCall:\n{ir}");
        assert!(ir.contains("@rt_value_unbox_int("), "expected rt_value_unbox_int in $boxed:\n{ir}");
        assert!(ir.contains("@rt_value_bool("), "expected rt_value_bool in $boxed:\n{ir}");
    }
}
