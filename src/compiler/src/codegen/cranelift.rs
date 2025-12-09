use std::collections::HashMap;

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, Signature, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use target_lexicon::Triple;
use thiserror::Error;

use crate::hir::{TypeId, BinOp};
use crate::mir::{MirFunction, MirInst, MirModule, Terminator, VReg};

#[derive(Error, Debug)]
pub enum CodegenError {
    #[error("Cranelift error: {0}")]
    Cranelift(String),

    #[error("Unsupported type: {0:?}")]
    UnsupportedType(TypeId),

    #[error("Unknown function: {0}")]
    UnknownFunction(String),

    #[error("Module error: {0}")]
    ModuleError(String),
}

pub type CodegenResult<T> = Result<T, CodegenError>;

/// Codegen context for translating MIR to machine code
pub struct Codegen {
    module: ObjectModule,
    ctx: Context,
    func_ids: HashMap<String, cranelift_module::FuncId>,
}

impl Codegen {
    pub fn new() -> CodegenResult<Self> {
        let mut settings_builder = settings::builder();
        settings_builder.set("opt_level", "speed").unwrap();

        let flags = Flags::new(settings_builder);
        let triple = Triple::host();

        let isa = cranelift_codegen::isa::lookup(triple.clone())
            .map_err(|e| CodegenError::Cranelift(e.to_string()))?
            .finish(flags)
            .map_err(|e| CodegenError::Cranelift(e.to_string()))?;

        let builder = ObjectBuilder::new(
            isa,
            "simple_module",
            cranelift_module::default_libcall_names(),
        )
        .map_err(|e| CodegenError::ModuleError(e.to_string()))?;

        let module = ObjectModule::new(builder);
        let ctx = module.make_context();

        Ok(Self {
            module,
            ctx,
            func_ids: HashMap::new(),
        })
    }

    pub fn compile_module(mut self, mir: &MirModule) -> CodegenResult<Vec<u8>> {
        // First pass: declare all functions
        for func in &mir.functions {
            let sig = Self::build_signature(func);
            let linkage = if func.is_public {
                Linkage::Export
            } else {
                Linkage::Local
            };

            let func_id = self
                .module
                .declare_function(&func.name, linkage, &sig)
                .map_err(|e| CodegenError::ModuleError(e.to_string()))?;

            self.func_ids.insert(func.name.clone(), func_id);
        }

        // Second pass: compile function bodies
        for func in &mir.functions {
            self.compile_function(func)?;
        }

        // Emit object code
        let product = self.module.finish();
        Ok(product.emit().map_err(|e| CodegenError::ModuleError(e.to_string()))?)
    }

    fn build_signature(func: &MirFunction) -> Signature {
        let call_conv = CallConv::SystemV;
        let mut sig = Signature::new(call_conv);

        // Add parameters
        for param in &func.params {
            let ty = Self::type_to_cranelift(param.ty);
            sig.params.push(AbiParam::new(ty));
        }

        // Add return type
        if func.return_type != TypeId::VOID {
            let ret_ty = Self::type_to_cranelift(func.return_type);
            sig.returns.push(AbiParam::new(ret_ty));
        }

        sig
    }

    fn type_to_cranelift(ty: TypeId) -> types::Type {
        match ty {
            TypeId::VOID => types::I64, // Placeholder
            TypeId::BOOL => types::I8,
            TypeId::I8 | TypeId::U8 => types::I8,
            TypeId::I16 | TypeId::U16 => types::I16,
            TypeId::I32 | TypeId::U32 => types::I32,
            TypeId::I64 | TypeId::U64 => types::I64,
            TypeId::F32 => types::F32,
            TypeId::F64 => types::F64,
            _ => types::I64, // Default to pointer-sized
        }
    }

    fn compile_function(&mut self, func: &MirFunction) -> CodegenResult<()> {
        let func_id = *self.func_ids.get(&func.name)
            .ok_or_else(|| CodegenError::UnknownFunction(func.name.clone()))?;

        let sig = Self::build_signature(func);
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        let mut func_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut func_ctx);

        // Create variables for parameters and locals
        let mut variables = HashMap::new();
        let mut var_idx = 0u32;

        for (i, param) in func.params.iter().enumerate() {
            let var = Variable::from_u32(var_idx);
            let ty = Self::type_to_cranelift(param.ty);
            builder.declare_var(var, ty);
            variables.insert(i, var);
            var_idx += 1;
        }

        for (i, local) in func.locals.iter().enumerate() {
            let var = Variable::from_u32(var_idx);
            let ty = Self::type_to_cranelift(local.ty);
            builder.declare_var(var, ty);
            variables.insert(func.params.len() + i, var);
            var_idx += 1;
        }

        // Create blocks
        let mut blocks = HashMap::new();
        for mir_block in &func.blocks {
            let cl_block = builder.create_block();
            blocks.insert(mir_block.id, cl_block);
        }

        // Entry block gets parameters
        let entry_block = *blocks.get(&func.entry_block).unwrap();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        // Initialize parameter variables
        for (i, _param) in func.params.iter().enumerate() {
            let val = builder.block_params(entry_block)[i];
            let var = variables[&i];
            builder.def_var(var, val);
        }

        // Compile each block
        let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();

        for mir_block in &func.blocks {
            let cl_block = *blocks.get(&mir_block.id).unwrap();

            if mir_block.id != func.entry_block {
                builder.switch_to_block(cl_block);
            }

            // Compile instructions
            for inst in &mir_block.instructions {
                match inst {
                    MirInst::ConstInt { dest, value } => {
                        let val = builder.ins().iconst(types::I64, *value);
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::ConstFloat { dest, value } => {
                        let val = builder.ins().f64const(*value);
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::ConstBool { dest, value } => {
                        let val = builder.ins().iconst(types::I8, if *value { 1 } else { 0 });
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::Copy { dest, src } => {
                        let val = vreg_values[src];
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::BinOp { dest, op, left, right } => {
                        let lhs = vreg_values[left];
                        let rhs = vreg_values[right];

                        let val = match op {
                            BinOp::Add => builder.ins().iadd(lhs, rhs),
                            BinOp::Sub => builder.ins().isub(lhs, rhs),
                            BinOp::Mul => builder.ins().imul(lhs, rhs),
                            BinOp::Div => builder.ins().sdiv(lhs, rhs),
                            BinOp::Mod => builder.ins().srem(lhs, rhs),
                            BinOp::BitAnd => builder.ins().band(lhs, rhs),
                            BinOp::BitOr => builder.ins().bor(lhs, rhs),
                            BinOp::BitXor => builder.ins().bxor(lhs, rhs),
                            BinOp::ShiftLeft => builder.ins().ishl(lhs, rhs),
                            BinOp::ShiftRight => builder.ins().sshr(lhs, rhs),
                            BinOp::Lt => {
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::SignedLessThan,
                                    lhs, rhs
                                )
                            }
                            BinOp::Gt => {
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan,
                                    lhs, rhs
                                )
                            }
                            BinOp::LtEq => {
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::SignedLessThanOrEqual,
                                    lhs, rhs
                                )
                            }
                            BinOp::GtEq => {
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThanOrEqual,
                                    lhs, rhs
                                )
                            }
                            BinOp::Eq => {
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::Equal,
                                    lhs, rhs
                                )
                            }
                            BinOp::NotEq => {
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                    lhs, rhs
                                )
                            }
                            _ => lhs, // TODO: handle remaining ops
                        };
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::LocalAddr { dest, local_index } => {
                        // For now, just use the variable value
                        if let Some(&var) = variables.get(local_index) {
                            let val = builder.use_var(var);
                            vreg_values.insert(*dest, val);
                        }
                    }

                    MirInst::Load { dest, addr, .. } => {
                        // Simplified: just copy the value
                        let val = vreg_values[addr];
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::Store { addr: _, value, .. } => {
                        // Would need to track which local this corresponds to
                        let _ = value;
                    }

                    MirInst::Call { dest, func: func_name, args } => {
                        if let Some(&callee_id) = self.func_ids.get(func_name) {
                            let callee_ref = self.module.declare_func_in_func(
                                callee_id,
                                builder.func
                            );

                            let arg_vals: Vec<_> = args.iter()
                                .map(|a| vreg_values[a])
                                .collect();

                            let call = builder.ins().call(callee_ref, &arg_vals);
                            if let Some(d) = dest {
                                let results = builder.inst_results(call);
                                if !results.is_empty() {
                                    vreg_values.insert(*d, results[0]);
                                }
                            }
                        }
                    }

                    _ => {}
                }
            }

            // Compile terminator
            match &mir_block.terminator {
                Terminator::Return(val) => {
                    if let Some(v) = val {
                        let ret_val = vreg_values[v];
                        builder.ins().return_(&[ret_val]);
                    } else if func.return_type == TypeId::VOID {
                        builder.ins().return_(&[]);
                    } else {
                        // Return(None) on a non-void function is unreachable
                        builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                    }
                }

                Terminator::Jump(target) => {
                    let target_block = *blocks.get(target).unwrap();
                    builder.ins().jump(target_block, &[]);
                }

                Terminator::Branch { cond, then_block, else_block } => {
                    let cond_val = vreg_values[cond];
                    let then_bl = *blocks.get(then_block).unwrap();
                    let else_bl = *blocks.get(else_block).unwrap();

                    // brif expects I8 (boolean) condition
                    // If cond_val is already I8, use it directly; otherwise truncate
                    builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
                }

                Terminator::Unreachable => {
                    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                }
            }
        }

        // Seal all blocks after all predecessors are known
        for mir_block in &func.blocks {
            let cl_block = *blocks.get(&mir_block.id).unwrap();
            builder.seal_block(cl_block);
        }

        builder.finalize();

        // Verify the function before defining
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            return Err(CodegenError::ModuleError(format!("Verifier errors:\n{}", errors)));
        }

        // Define the function
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| CodegenError::ModuleError(format!("Compilation error: {}", e)))?;

        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    pub fn get_object_code(self) -> Vec<u8> {
        let product = self.module.finish();
        product.emit().unwrap()
    }
}

impl Default for Codegen {
    fn default() -> Self {
        Self::new().expect("Failed to create codegen")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir;
    use crate::mir::lower_to_mir;
    use simple_parser::Parser;

    fn compile_to_object(source: &str) -> CodegenResult<Vec<u8>> {
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");
        let mir_module = lower_to_mir(&hir_module).expect("mir lower failed");
        Codegen::new()?.compile_module(&mir_module)
    }

    #[test]
    fn test_compile_simple_function() {
        let obj = compile_to_object("fn answer() -> i64:\n    return 42\n").unwrap();
        assert!(!obj.is_empty());
    }

    #[test]
    fn test_compile_add_function() {
        let obj = compile_to_object("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();
        assert!(!obj.is_empty());
    }

    #[test]
    fn test_compile_comparison() {
        let obj = compile_to_object(
            "fn is_positive(x: i64) -> bool:\n    return x > 0\n"
        ).unwrap();
        assert!(!obj.is_empty());
    }

    #[test]
    fn test_compile_if_else() {
        let obj = compile_to_object(
            "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
        ).unwrap();
        assert!(!obj.is_empty());
    }
}
