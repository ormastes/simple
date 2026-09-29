//! Adapt named native functions to the implicit-context closure calling ABI.

#[cfg(feature = "llvm")]
impl super::LlvmBackend {
    pub(in crate::codegen::llvm) fn named_callable_adapter(
        &self,
        module: &inkwell::module::Module<'static>,
        callee: inkwell::values::FunctionValue<'static>,
    ) -> Result<inkwell::values::FunctionValue<'static>, crate::error::CompileError> {
        use crate::error::CompileError;
        use inkwell::attributes::AttributeLoc;
        use inkwell::module::Linkage;
        use inkwell::types::BasicType;

        const TARGET_ATTRIBUTE: &str = "simple.named_callable.target";
        let target = callee
            .get_name()
            .to_str()
            .map_err(|_| CompileError::semantic("non-UTF8 callable name"))?;
        // Probe only this target's generated names, preserving user symbols
        // without scanning every function for each function-value load.
        let preferred_name = format!("__simple_named_callable__{target}");
        let mut adapter_name = preferred_name.clone();
        let mut collision = 0;
        while let Some(existing) = module.get_function(&adapter_name) {
            if existing
                .get_string_attribute(AttributeLoc::Function, TARGET_ATTRIBUTE)
                .is_some_and(|attribute| attribute.get_string_value().to_bytes() == target.as_bytes())
            {
                return Ok(existing);
            }
            collision += 1;
            adapter_name = format!("{preferred_name}.{collision}");
        }

        let original_type = callee.get_type();
        if original_type.is_var_arg() {
            return Err(CompileError::semantic(
                "variadic named function values require an explicit wrapper",
            ));
        }
        let mut params = vec![self.runtime_int_type().into()];
        params.extend(original_type.get_param_types());
        let adapter_type = match original_type.get_return_type() {
            Some(ret) => ret.fn_type(&params, false),
            None => self.context_ref().void_type().fn_type(&params, false),
        };
        let adapter = module.add_function(&adapter_name, adapter_type, Some(Linkage::Private));
        // Ordinary closure indirect calls use C ABI; the inner call retains
        // the named target's calling convention.
        adapter.set_call_conventions(0);
        adapter.add_attribute(
            AttributeLoc::Function,
            self.context_ref().create_string_attribute(TARGET_ATTRIBUTE, target),
        );
        let entry = self.context_ref().append_basic_block(adapter, "entry");
        let builder = self.context_ref().create_builder();
        builder.position_at_end(entry);
        let args: Vec<_> = adapter.get_param_iter().skip(1).map(Into::into).collect();
        let call = builder
            .build_call(callee, &args, "named_call")
            .map_err(|error| crate::error::factory::llvm_build_failed("named callable call", &error))?;
        call.set_call_convention(callee.get_call_conventions());
        match call.try_as_basic_value().basic() {
            Some(value) => builder.build_return(Some(&value)),
            None => builder.build_return(None),
        }
        .map_err(|error| crate::error::factory::llvm_build_failed("named callable return", &error))?;
        Ok(adapter)
    }
}

#[cfg(all(test, feature = "llvm"))]
mod tests {
    use super::super::LlvmBackend;
    use inkwell::module::Linkage;
    use simple_common::target::{Target, TargetArch, TargetOS};

    #[test]
    fn named_adapter_preserves_native_signature_void_convention_and_name_collision() {
        let backend = LlvmBackend::new(Target::new(TargetArch::X86_64, TargetOS::Linux)).unwrap();
        backend.create_module("adapter_abi").unwrap();
        let module_ref = backend.module.borrow();
        let module = module_ref.as_ref().unwrap();
        let context = backend.context_ref();
        let target = module.add_function(
            "target",
            context.f64_type().fn_type(&[context.i32_type().into()], false),
            None,
        );
        target.set_call_conventions(8); // LLVM fastcc: retain the target ABI.
        let collision = module.add_function(
            "__simple_named_callable__target",
            context.void_type().fn_type(&[], false),
            None,
        );
        let adapter = backend.named_callable_adapter(module, target).unwrap();
        assert_ne!(adapter, collision);
        assert_eq!(adapter.get_linkage(), Linkage::Private);
        assert_eq!(adapter.get_call_conventions(), 0);
        assert_eq!(
            adapter.get_type().get_return_type(),
            target.get_type().get_return_type()
        );
        assert_eq!(
            adapter.get_type().get_param_types()[1..],
            target.get_type().get_param_types()
        );
        assert_eq!(backend.named_callable_adapter(module, target).unwrap(), adapter);
        let void_target = module.add_function(
            "void_target",
            context.void_type().fn_type(&[context.i64_type().into()], false),
            None,
        );
        let void_adapter = backend.named_callable_adapter(module, void_target).unwrap();
        assert!(void_adapter.get_type().get_return_type().is_none());
        module.verify().unwrap();
        let ir = module.print_to_string().to_string();
        assert!(ir.contains("call fastcc double @target(i32 %1)"), "{ir}");
        assert!(ir.contains("call void @void_target(i64 %1)"), "{ir}");
        assert!(ir.contains("ret void"), "{ir}");
    }
}
