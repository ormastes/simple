/// LLVM function compilation - main compile_function implementation

use super::LlvmBackend;
use crate::error::CompileError;
use crate::mir::MirFunction;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

impl LlvmBackend {
    /// Compile a MIR function to LLVM IR (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_function(&self, func: &MirFunction) -> Result<(), CompileError> {
        use crate::hir::TypeId;
        use crate::mir::MirInst;
        use std::collections::HashMap;

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;

        // Map parameter types
        let param_types: Result<Vec<_>, _> = func
            .params
            .iter()
            .map(|p| self.llvm_type(&p.ty).map(|t| t.into()))
            .collect();
        let param_types = param_types?;

        // Create function type
        let fn_type = if func.return_type == TypeId::VOID {
            self.context.void_type().fn_type(&param_types, false)
        } else {
            let ret_llvm = self.llvm_type(&func.return_type)?;
            match ret_llvm {
                BasicTypeEnum::IntType(t) => t.fn_type(&param_types, false),
                BasicTypeEnum::FloatType(t) => t.fn_type(&param_types, false),
                BasicTypeEnum::PointerType(t) => t.fn_type(&param_types, false),
                _ => {
                    return Err(CompileError::Semantic(
                        "Unsupported return type".to_string(),
                    ))
                }
            }
        };

        // Add function to module
        let function = module.add_function(&func.name, fn_type, None);

        // Create basic blocks for each MIR block
        let mut llvm_blocks = HashMap::new();
        for block in &func.blocks {
            let bb = self
                .context
                .append_basic_block(function, &format!("bb{}", block.id.0));
            llvm_blocks.insert(block.id, bb);
        }

        // Map virtual registers to LLVM values
        let mut vreg_map: HashMap<crate::mir::VReg, inkwell::values::BasicValueEnum<'static>> =
            HashMap::new();

        // Map function parameters to virtual registers
        for (i, param) in func.params.iter().enumerate() {
            if let Some(llvm_param) = function.get_nth_param(i as u32) {
                // Params are mapped to vregs starting from VReg(0)
                vreg_map.insert(crate::mir::VReg(i as u32), llvm_param.into());
            }
        }

        // Compile each block
        for block in &func.blocks {
            let bb = llvm_blocks[&block.id];
            builder.position_at_end(bb);

            // Emit coverage counter increment if coverage is enabled
            if self.coverage_enabled {
                self.emit_coverage_counter(module, builder, &func.name, block.id.0)?;
            }

            // Compile each instruction
            for inst in &block.instructions {
                match inst {
                    MirInst::ConstInt { dest, value } => {
                        let const_val = self.context.i64_type().const_int(*value as u64, true);
                        vreg_map.insert(*dest, const_val.into());
                    }
                    MirInst::ConstBool { dest, value } => {
                        let const_val = self.context.bool_type().const_int(*value as u64, false);
                        vreg_map.insert(*dest, const_val.into());
                    }
                    MirInst::Copy { dest, src } => {
                        if let Some(val) = vreg_map.get(src) {
                            vreg_map.insert(*dest, *val);
                        }
                    }
                    MirInst::BinOp {
                        dest,
                        op,
                        left,
                        right,
                    } => {
                        let left_val = vreg_map.get(left).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", left))
                        })?;
                        let right_val = vreg_map.get(right).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", right))
                        })?;

                        let result = self.compile_binop(*op, *left_val, *right_val, builder)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::ConstFloat { dest, value } => {
                        let const_val = self.context.f64_type().const_float(*value);
                        vreg_map.insert(*dest, const_val.into());
                    }
                    MirInst::UnaryOp { dest, op, operand } => {
                        let operand_val = vreg_map.get(operand).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", operand))
                        })?;

                        let result = self.compile_unaryop(*op, *operand_val, builder)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::Load { dest, addr, ty } => {
                        let addr_val = vreg_map.get(addr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", addr))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
                            let loaded = builder
                                .build_load(self.llvm_type(ty)?, *ptr, "load")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build load: {}", e))
                                })?;
                            vreg_map.insert(*dest, loaded);
                        } else {
                            return Err(CompileError::Semantic(
                                "Load requires pointer".to_string(),
                            ));
                        }
                    }
                    MirInst::Store { addr, value, ty: _ } => {
                        let addr_val = vreg_map.get(addr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", addr))
                        })?;
                        let value_val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
                            builder.build_store(*ptr, *value_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        } else {
                            return Err(CompileError::Semantic(
                                "Store requires pointer".to_string(),
                            ));
                        }
                    }
                    MirInst::GcAlloc { dest, ty } => {
                        // Allocate on stack for now (proper GC integration later)
                        let llvm_ty = self.llvm_type(ty)?;
                        let alloc = builder.build_alloca(llvm_ty, "gc_alloc").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;
                        vreg_map.insert(*dest, alloc.into());
                    }
                    MirInst::ConstString { dest, value } => {
                        // Create global string constant
                        let str_val = self.context.const_string(value.as_bytes(), false);
                        let global = module.add_global(str_val.get_type(), None, "str");
                        global.set_initializer(&str_val);
                        global.set_constant(true);
                        vreg_map.insert(*dest, global.as_pointer_value().into());
                    }
                    MirInst::Call { dest, target, args } => {
                        // Get or declare the called function
                        let func_name = target.name();
                        let called_func = module.get_function(func_name).ok_or_else(|| {
                            // Function not found, try to declare it
                            // For now, assume all functions return i64 and take i64 params
                            let i64_type = self.context.i64_type();
                            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                                args.iter().map(|_| i64_type.into()).collect();
                            let fn_type = i64_type.fn_type(&param_types, false);
                            module.add_function(func_name, fn_type, None)
                        });

                        let called_func = match called_func {
                            Ok(f) => f,
                            Err(f) => f, // Use the declared function
                        };

                        // Collect argument values
                        let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                        for arg in args {
                            let val = vreg_map.get(arg).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", arg))
                            })?;
                            arg_vals.push((*val).into());
                        }

                        // Build the call
                        let call_site = builder
                            .build_call(called_func, &arg_vals, "call")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build call: {}", e))
                            })?;

                        // Store result if there's a destination
                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            }
                        }
                    }
                    MirInst::ArrayLit { dest, elements } => {
                        // Create array on stack and initialize elements
                        let i64_type = self.context.i64_type();
                        let array_type = i64_type.array_type(elements.len() as u32);
                        let alloc = builder.build_alloca(array_type, "array").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;

                        // Store each element
                        for (i, elem) in elements.iter().enumerate() {
                            let elem_val = vreg_map.get(elem).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", elem))
                            })?;

                            let indices = [
                                self.context.i32_type().const_int(0, false),
                                self.context.i32_type().const_int(i as u64, false),
                            ];
                            let gep = unsafe {
                                builder.build_gep(array_type, alloc, &indices, "elem_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;

                            builder.build_store(gep, *elem_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, alloc.into());
                    }
                    MirInst::TupleLit { dest, elements } => {
                        // Tuples are similar to arrays - create struct on stack
                        let i64_type = self.context.i64_type();
                        let field_types: Vec<BasicTypeEnum> =
                            elements.iter().map(|_| i64_type.into()).collect();
                        let struct_type = self.context.struct_type(&field_types, false);
                        let alloc = builder.build_alloca(struct_type, "tuple").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;

                        // Store each element
                        for (i, elem) in elements.iter().enumerate() {
                            let elem_val = vreg_map.get(elem).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", elem))
                            })?;

                            let gep = builder
                                .build_struct_gep(struct_type, alloc, i as u32, "tuple_elem")
                                .map_err(|e| {
                                    CompileError::Semantic(format!(
                                        "Failed to build struct gep: {}",
                                        e
                                    ))
                                })?;

                            builder.build_store(gep, *elem_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, alloc.into());
                    }
                    MirInst::IndexGet {
                        dest,
                        collection,
                        index,
                    } => {
                        let coll_val = vreg_map.get(collection).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", collection))
                        })?;
                        let idx_val = vreg_map.get(index).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", index))
                        })?;

                        // Collection should be a pointer to array
                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
                            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                                let i64_type = self.context.i64_type();
                                let arr_type = i64_type.array_type(0); // Dynamic size

                                let indices = [
                                    self.context.i32_type().const_int(0, false),
                                    *idx,
                                ];
                                let gep = unsafe {
                                    builder.build_gep(arr_type, *ptr, &indices, "elem_ptr")
                                }
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build gep: {}", e))
                                })?;

                                let loaded = builder
                                    .build_load(i64_type, gep, "elem")
                                    .map_err(|e| {
                                        CompileError::Semantic(format!(
                                            "Failed to build load: {}",
                                            e
                                        ))
                                    })?;

                                vreg_map.insert(*dest, loaded);
                            }
                        }
                    }
                    MirInst::IndexSet {
                        collection,
                        index,
                        value,
                    } => {
                        let coll_val = vreg_map.get(collection).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", collection))
                        })?;
                        let idx_val = vreg_map.get(index).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", index))
                        })?;
                        let val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;

                        // Collection should be a pointer to array
                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
                            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                                let i64_type = self.context.i64_type();
                                let arr_type = i64_type.array_type(0);

                                let indices = [
                                    self.context.i32_type().const_int(0, false),
                                    *idx,
                                ];
                                let gep = unsafe {
                                    builder.build_gep(arr_type, *ptr, &indices, "elem_ptr")
                                }
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build gep: {}", e))
                                })?;

                                builder.build_store(gep, *val).map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build store: {}", e))
                                })?;
                            }
                        }
                    }
                    MirInst::InterpCall {
                        dest,
                        func_name,
                        args,
                    } => {
                        // Call interpreter bridge function rt_interp_call
                        let i64_type = self.context.i64_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                        // Declare rt_interp_call if not exists
                        let interp_call = module.get_function("rt_interp_call").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(
                                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i8_ptr_type.into()],
                                false,
                            );
                            module.add_function("rt_interp_call", fn_type, None)
                        });

                        // Create string constant for function name
                        let name_bytes = func_name.as_bytes();
                        let name_const = self.context.const_string(name_bytes, false);
                        let name_global = module.add_global(name_const.get_type(), None, "func_name");
                        name_global.set_initializer(&name_const);
                        name_global.set_constant(true);
                        let name_ptr = name_global.as_pointer_value();
                        let name_len = i64_type.const_int(name_bytes.len() as u64, false);

                        // For now, pass null for args array (simplified)
                        let argc = i64_type.const_int(args.len() as u64, false);
                        let argv = i8_ptr_type.const_null();

                        let call_args = [
                            name_ptr.into(),
                            name_len.into(),
                            argc.into(),
                            argv.into(),
                        ];

                        let call_site = builder
                            .build_call(interp_call, &call_args, "interp_call")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build call: {}", e))
                            })?;

                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            }
                        }
                    }
                    MirInst::DictLit { dest, keys, values } => {
                        // Dictionaries are represented as a struct with keys array and values array
                        let i64_type = self.context.i64_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                        // Declare rt_dict_new if not exists
                        let dict_new = module.get_function("rt_dict_new").unwrap_or_else(|| {
                            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_dict_new", fn_type, None)
                        });

                        // Declare rt_dict_insert if not exists
                        let dict_insert = module.get_function("rt_dict_insert").unwrap_or_else(|| {
                            let fn_type = self.context.void_type().fn_type(
                                &[i8_ptr_type.into(), i64_type.into(), i64_type.into()],
                                false,
                            );
                            module.add_function("rt_dict_insert", fn_type, None)
                        });

                        // Create new dict with initial capacity
                        let capacity = i64_type.const_int(keys.len() as u64, false);
                        let dict_ptr = builder
                            .build_call(dict_new, &[capacity.into()], "dict")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build dict_new call: {}", e))
                            })?
                            .try_as_basic_value()
                            .left()
                            .ok_or_else(|| {
                                CompileError::Semantic("dict_new returned void".to_string())
                            })?;

                        // Insert each key-value pair
                        for (key, value) in keys.iter().zip(values.iter()) {
                            let key_val = vreg_map.get(key).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", key))
                            })?;
                            let value_val = vreg_map.get(value).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                            })?;

                            builder
                                .build_call(
                                    dict_insert,
                                    &[dict_ptr.into(), (*key_val).into(), (*value_val).into()],
                                    "",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!(
                                        "Failed to build dict_insert call: {}",
                                        e
                                    ))
                                })?;
                        }

                        vreg_map.insert(*dest, dict_ptr);
                    }
                    MirInst::StructInit {
                        dest,
                        struct_size,
                        field_offsets,
                        field_types,
                        field_values,
                        ..
                    } => {
                        let i8_type = self.context.i8_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                        let array_type = i8_type.array_type(*struct_size);
                        let alloc = builder.build_alloca(array_type, "struct").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;
                        let struct_ptr = builder
                            .build_pointer_cast(alloc, i8_ptr_type, "struct_ptr")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast struct ptr: {}", e))
                            })?;

                        for ((offset, field_type), value) in field_offsets
                            .iter()
                            .zip(field_types.iter())
                            .zip(field_values.iter())
                        {
                            let field_val = vreg_map.get(value).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                            })?;
                            let offset_val =
                                self.context.i32_type().const_int(*offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "field_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast field ptr: {}", e))
                                })?;
                            builder.build_store(typed_ptr, *field_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, struct_ptr.into());
                    }
                    MirInst::FieldGet {
                        dest,
                        object,
                        byte_offset,
                        field_type,
                    } => {
                        let obj_val = vreg_map.get(object).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", object))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
                            let i8_type = self.context.i8_type();
                            let i8_ptr_type =
                                self.context.ptr_type(inkwell::AddressSpace::default());
                            let base_ptr = builder
                                .build_pointer_cast(*ptr, i8_ptr_type, "struct_ptr")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast struct ptr: {}", e))
                                })?;
                            let offset_val =
                                self.context.i32_type().const_int(*byte_offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "field_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast field ptr: {}", e))
                                })?;
                            let loaded = builder
                                .build_load(llvm_field_ty, typed_ptr, "field")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build load: {}", e))
                                })?;

                            vreg_map.insert(*dest, loaded);
                        } else {
                            return Err(CompileError::Semantic(
                                "FieldGet requires pointer to struct".to_string(),
                            ));
                        }
                    }
                    MirInst::FieldSet {
                        object,
                        byte_offset,
                        field_type,
                        value,
                    } => {
                        let obj_val = vreg_map.get(object).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", object))
                        })?;
                        let val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
                            let i8_type = self.context.i8_type();
                            let i8_ptr_type =
                                self.context.ptr_type(inkwell::AddressSpace::default());
                            let base_ptr = builder
                                .build_pointer_cast(*ptr, i8_ptr_type, "struct_ptr")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast struct ptr: {}", e))
                                })?;
                            let offset_val =
                                self.context.i32_type().const_int(*byte_offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "field_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast field ptr: {}", e))
                                })?;
                            builder.build_store(typed_ptr, *val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        } else {
                            return Err(CompileError::Semantic(
                                "FieldSet requires pointer to struct".to_string(),
                            ));
                        }
                    }
                    MirInst::ClosureCreate {
                        dest,
                        func_name,
                        closure_size,
                        capture_offsets,
                        capture_types,
                        captures,
                    } => {
                        let i8_type = self.context.i8_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                        let array_type = i8_type.array_type(*closure_size);
                        let alloc = builder.build_alloca(array_type, "closure").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;
                        let closure_ptr = builder
                            .build_pointer_cast(alloc, i8_ptr_type, "closure_ptr")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast closure ptr: {}", e))
                            })?;

                        let func_ptr = module
                            .get_function(func_name)
                            .map(|f| f.as_global_value().as_pointer_value())
                            .unwrap_or_else(|| i8_ptr_type.const_null());
                        let func_ptr_cast = builder
                            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast fn ptr: {}", e))
                            })?;
                        let fn_slot = builder
                            .build_pointer_cast(
                                closure_ptr,
                                i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                                "fn_slot",
                            )
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast fn slot: {}", e))
                            })?;
                        builder.build_store(fn_slot, func_ptr_cast).map_err(|e| {
                            CompileError::Semantic(format!("Failed to build store: {}", e))
                        })?;

                        for ((offset, field_type), value) in capture_offsets
                            .iter()
                            .zip(capture_types.iter())
                            .zip(captures.iter())
                        {
                            let capture_val = vreg_map.get(value).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                            })?;
                            let offset_val =
                                self.context.i32_type().const_int(*offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "cap_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast cap ptr: {}", e))
                                })?;
                            builder.build_store(typed_ptr, *capture_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, closure_ptr.into());
                    }
                    MirInst::IndirectCall {
                        dest,
                        callee,
                        param_types,
                        return_type,
                        args,
                        ..
                    } => {
                        let i8_type = self.context.i8_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                        let callee_val = vreg_map.get(callee).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", callee))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(closure_ptr) =
                            callee_val
                        {
                            let base_ptr = builder
                                .build_pointer_cast(*closure_ptr, i8_ptr_type, "closure_ptr")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast closure ptr: {}", e))
                                })?;
                            let offset_val = self.context.i32_type().const_int(0, false);
                            let fn_ptr_slot = unsafe {
                                builder.build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let fn_ptr_slot = builder
                                .build_pointer_cast(
                                    fn_ptr_slot,
                                    i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                                    "fn_ptr_slot_cast",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!(
                                        "Failed to cast fn slot ptr: {}",
                                        e
                                    ))
                                })?;
                            let func_ptr = builder
                                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build load: {}", e))
                                })?;

                            if let inkwell::values::BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> =
                                    Vec::new();
                                for arg in args {
                                    let val = vreg_map.get(arg).ok_or_else(|| {
                                        CompileError::Semantic(format!("Undefined vreg: {:?}", arg))
                                    })?;
                                    arg_vals.push((*val).into());
                                }

                                let llvm_param_types: Result<
                                    Vec<inkwell::types::BasicMetadataTypeEnum>,
                                    CompileError,
                                > = param_types
                                    .iter()
                                    .map(|ty| self.llvm_type(ty).map(|t| t.into()))
                                    .collect();
                                let llvm_param_types = llvm_param_types?;

                                let fn_type = if *return_type == TypeId::VOID {
                                    self.context
                                        .void_type()
                                        .fn_type(&llvm_param_types, false)
                                } else {
                                    let ret_llvm = self.llvm_type(return_type)?;
                                    match ret_llvm {
                                        BasicTypeEnum::IntType(t) => {
                                            t.fn_type(&llvm_param_types, false)
                                        }
                                        BasicTypeEnum::FloatType(t) => {
                                            t.fn_type(&llvm_param_types, false)
                                        }
                                        BasicTypeEnum::PointerType(t) => {
                                            t.fn_type(&llvm_param_types, false)
                                        }
                                        _ => {
                                            return Err(CompileError::Semantic(
                                                "Unsupported return type".to_string(),
                                            ))
                                        }
                                    }
                                };

                                let call_site = builder
                                    .build_indirect_call(fn_type, fn_ptr, &arg_vals, "indirect_call")
                                    .map_err(|e| {
                                        CompileError::Semantic(format!(
                                            "Failed to build indirect call: {}",
                                            e
                                        ))
                                    })?;

                                if let Some(d) = dest {
                                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                        vreg_map.insert(*d, ret_val);
                                    }
                                }
                            }
                        } else {
                            return Err(CompileError::Semantic(
                                "IndirectCall requires closure pointer".to_string(),
                            ));
                        }
                    }
                    MirInst::ConstSymbol { dest, value } => {
                        // Symbols are represented as interned string pointers
                        let str_val = self.context.const_string(value.as_bytes(), false);
                        let global =
                            module.add_global(str_val.get_type(), None, &format!("sym_{}", value));
                        global.set_initializer(&str_val);
                        global.set_constant(true);
                        vreg_map.insert(*dest, global.as_pointer_value().into());
                    }
                    MirInst::SliceOp {
                        dest,
                        collection,
                        start,
                        end,
                        step,
                    } => {
                        let i64_type = self.context.i64_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                        // Declare rt_slice if not exists
                        let slice_fn = module.get_function("rt_slice").unwrap_or_else(|| {
                            let fn_type = i8_ptr_type.fn_type(
                                &[
                                    i8_ptr_type.into(),
                                    i64_type.into(),
                                    i64_type.into(),
                                    i64_type.into(),
                                ],
                                false,
                            );
                            module.add_function("rt_slice", fn_type, None)
                        });

                        let coll_val = vreg_map.get(collection).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", collection))
                        })?;

                        // Get start index (default to 0 if None)
                        let start_val = if let Some(s) = start {
                            vreg_map.get(s).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", s))
                            })?
                        } else {
                            &inkwell::values::BasicValueEnum::IntValue(
                                i64_type.const_int(0, false),
                            )
                        };

                        // Get end index (default to -1 meaning end of collection)
                        let end_val = if let Some(e) = end {
                            vreg_map.get(e).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", e))
                            })?
                        } else {
                            &inkwell::values::BasicValueEnum::IntValue(
                                i64_type.const_int(i64::MAX as u64, false),
                            )
                        };

                        // Get step (default to 1)
                        let step_val = if let Some(s) = step {
                            vreg_map.get(s).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", s))
                            })?
                        } else {
                            &inkwell::values::BasicValueEnum::IntValue(
                                i64_type.const_int(1, false),
                            )
                        };

                        let call_site = builder
                            .build_call(
                                slice_fn,
                                &[
                                    (*coll_val).into(),
                                    (*start_val).into(),
                                    (*end_val).into(),
                                    (*step_val).into(),
                                ],
                                "slice",
                            )
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build slice call: {}", e))
                            })?;

                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*dest, ret_val);
                        }
                    }
                    MirInst::InterpEval { dest, expr_index } => {
                        // Call interpreter to evaluate expression by index
                        let i64_type = self.context.i64_type();

                        // Declare rt_interp_eval if not exists
                        let interp_eval = module.get_function("rt_interp_eval").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_interp_eval", fn_type, None)
                        });

                        let expr_index_val =
                            i64_type.const_int(*expr_index as u64, true);
                        let call_site = builder
                            .build_call(interp_eval, &[expr_index_val.into()], "eval")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build call: {}", e))
                            })?;

                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*dest, ret_val);
                        }
                    }
                    // GPU instructions - call runtime FFI functions
                    MirInst::GpuGlobalId { dest, dim } => {
                        let result = self.compile_gpu_global_id(*dim, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuLocalId { dest, dim } => {
                        let result = self.compile_gpu_local_id(*dim, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuGroupId { dest, dim } => {
                        let result = self.compile_gpu_group_id(*dim, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuGlobalSize { dest, dim } => {
                        let result = self.compile_gpu_global_size(*dim, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuLocalSize { dest, dim } => {
                        let result = self.compile_gpu_local_size(*dim, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuNumGroups { dest, dim } => {
                        let result = self.compile_gpu_num_groups(*dim, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuBarrier => {
                        self.compile_gpu_barrier(builder, module)?;
                    }
                    MirInst::GpuMemFence { scope } => {
                        self.compile_gpu_mem_fence(*scope, builder, module)?;
                    }
                    MirInst::GpuAtomic { dest, op, ptr, value } => {
                        let ptr_val = vreg_map.get(ptr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", ptr))
                        })?;
                        let value_val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;
                        let result = self.compile_gpu_atomic(*op, *ptr_val, *value_val, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuAtomicCmpXchg { dest, ptr, expected, desired } => {
                        let ptr_val = vreg_map.get(ptr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", ptr))
                        })?;
                        let expected_val = vreg_map.get(expected).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", expected))
                        })?;
                        let desired_val = vreg_map.get(desired).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", desired))
                        })?;
                        let result = self.compile_gpu_atomic_cmpxchg(*ptr_val, *expected_val, *desired_val, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuSharedAlloc { dest, element_type: _, size } => {
                        let result = self.compile_gpu_shared_alloc(*size, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    _ => {
                        // Other instructions not yet implemented
                    }
                }
            }

            // Compile terminator
            self.compile_terminator(&block.terminator, &llvm_blocks, &vreg_map, builder)?;
        }

        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_function(&self, _func: &MirFunction) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }
}
