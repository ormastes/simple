# AOT Compilation: HIR to MIR and Cranelift Backend

Part of [Ahead of Time Compilation Plan](05_ahead_of_time_compile.md).

### HIR to MIR Lowering (mir/lower.rs)

```rust
// crates/compiler/src/mir/lower.rs

use crate::hir::*;
use crate::mir::*;

pub struct MirLowering {
    current_block: BlockId,
    blocks: Vec<BasicBlock>,
    locals: Vec<LocalVar>,
    next_local: u32,
    next_block: u32,
}

impl MirLowering {
    pub fn new() -> Self {
        Self {
            current_block: BlockId(0),
            blocks: Vec::new(),
            locals: Vec::new(),
            next_local: 0,
            next_block: 0,
        }
    }

    pub fn lower_function(&mut self, func: &HirFunction) -> MirFunction {
        self.reset();

        // Create entry block
        let entry = self.create_block();
        self.current_block = entry;

        // Create locals for parameters
        let param_locals: Vec<LocalId> = func.params.iter()
            .map(|p| self.create_local(self.lower_type(&p.ty), Some(p.name.clone())))
            .collect();

        // Lower body
        let result = self.lower_block(&func.body);

        // Add return terminator if needed
        if !self.current_block_terminated() {
            let term = match result {
                Some(local) => Terminator::Return(Some(local)),
                None => Terminator::Return(None),
            };
            self.set_terminator(term);
        }

        MirFunction {
            name: func.name.clone(),
            signature: FunctionSignature {
                params: func.params.iter()
                    .map(|p| self.lower_type(&p.ty))
                    .collect(),
                returns: self.lower_type(&func.return_type),
                calling_conv: CallingConv::Simple,
            },
            blocks: std::mem::take(&mut self.blocks),
            locals: std::mem::take(&mut self.locals),
            is_public: func.is_public,
        }
    }

    fn lower_block(&mut self, block: &HirBlock) -> Option<LocalId> {
        // Lower statements
        for stmt in &block.stmts {
            self.lower_stmt(stmt);
        }

        // Lower final expression
        block.expr.as_ref().map(|e| self.lower_expr(e))
    }

    fn lower_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Let { name, ty, init, is_mutable } => {
                let local = self.create_local(self.lower_type(ty), Some(name.clone()));

                if let Some(init_expr) = init {
                    let init_local = self.lower_expr(init_expr);
                    self.emit(MirInst::Copy(local, init_local));
                }
            }

            HirStmt::Assign { target, value } => {
                let value_local = self.lower_expr(value);
                self.lower_assign(target, value_local);
            }

            HirStmt::Return(expr) => {
                let local = expr.as_ref().map(|e| self.lower_expr(e));
                self.set_terminator(Terminator::Return(local));
            }

            HirStmt::Expr(expr) => {
                self.lower_expr(expr);
            }

            _ => {}
        }
    }

    fn lower_expr(&mut self, expr: &HirExpr) -> LocalId {
        match expr {
            HirExpr::IntLit(n, ty) => {
                let local = self.create_local(self.lower_type(ty), None);
                self.emit(MirInst::ConstInt(local, *n));
                local
            }

            HirExpr::FloatLit(f, ty) => {
                let local = self.create_local(self.lower_type(ty), None);
                self.emit(MirInst::ConstFloat(local, *f));
                local
            }

            HirExpr::BoolLit(b) => {
                let local = self.create_local(MirType::Bool, None);
                self.emit(MirInst::ConstBool(local, *b));
                local
            }

            HirExpr::Binary { op, left, right, ty } => {
                let left_local = self.lower_expr(left);
                let right_local = self.lower_expr(right);
                let result = self.create_local(self.lower_type(ty), None);

                let inst = match op {
                    BinOp::Add => MirInst::Add(result, left_local, right_local),
                    BinOp::Sub => MirInst::Sub(result, left_local, right_local),
                    BinOp::Mul => MirInst::Mul(result, left_local, right_local),
                    BinOp::Div => MirInst::Div(result, left_local, right_local),
                    BinOp::Eq => MirInst::Eq(result, left_local, right_local),
                    BinOp::Ne => MirInst::Ne(result, left_local, right_local),
                    BinOp::Lt => MirInst::Lt(result, left_local, right_local),
                    BinOp::Le => MirInst::Le(result, left_local, right_local),
                    BinOp::Gt => MirInst::Gt(result, left_local, right_local),
                    BinOp::Ge => MirInst::Ge(result, left_local, right_local),
                    BinOp::And => MirInst::And(result, left_local, right_local),
                    BinOp::Or => MirInst::Or(result, left_local, right_local),
                    _ => todo!(),
                };

                self.emit(inst);
                result
            }

            HirExpr::If { condition, then_branch, else_branch, ty } => {
                let cond = self.lower_expr(condition);
                let result = self.create_local(self.lower_type(ty), None);

                let then_block = self.create_block();
                let else_block = self.create_block();
                let merge_block = self.create_block();

                self.set_terminator(Terminator::CondBranch {
                    cond,
                    then_block,
                    else_block,
                });

                // Then branch
                self.current_block = then_block;
                let then_result = self.lower_block(then_branch);
                if let Some(r) = then_result {
                    self.emit(MirInst::Copy(result, r));
                }
                self.set_terminator(Terminator::Branch(merge_block));

                // Else branch
                self.current_block = else_block;
                if let Some(else_branch) = else_branch {
                    let else_result = self.lower_block(else_branch);
                    if let Some(r) = else_result {
                        self.emit(MirInst::Copy(result, r));
                    }
                }
                self.set_terminator(Terminator::Branch(merge_block));

                self.current_block = merge_block;
                result
            }

            HirExpr::Call { func, args, ty } => {
                let arg_locals: Vec<LocalId> = args.iter()
                    .map(|a| self.lower_expr(a))
                    .collect();
                let result = self.create_local(self.lower_type(ty), None);

                // Get function name (simplified)
                if let HirExpr::Var(name, _) = func.as_ref() {
                    self.emit(MirInst::Call(result, name.clone(), arg_locals));
                }

                result
            }

            // ... more expressions
            _ => {
                let local = self.create_local(MirType::Void, None);
                local
            }
        }
    }

    // Helper methods
    fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        self.blocks.push(BasicBlock {
            id,
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        });
        id
    }

    fn create_local(&mut self, ty: MirType, name: Option<String>) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        self.locals.push(LocalVar { id, ty, name });
        id
    }

    fn emit(&mut self, inst: MirInst) {
        let block = &mut self.blocks[self.current_block.0 as usize];
        block.instructions.push(inst);
    }

    fn set_terminator(&mut self, term: Terminator) {
        let block = &mut self.blocks[self.current_block.0 as usize];
        block.terminator = term;
    }

    fn lower_type(&self, ty: &TypeId) -> MirType {
        // TODO: Look up in type table
        MirType::I64
    }

    fn reset(&mut self) {
        self.blocks.clear();
        self.locals.clear();
        self.next_local = 0;
        self.next_block = 0;
    }
}
```

---

## Code Generation with Cranelift

### Cranelift Backend (codegen/cranelift.rs)

```rust
// crates/compiler/src/codegen/cranelift.rs

use cranelift::prelude::*;
use cranelift_module::{Module, Linkage, FuncId};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::mir::*;

pub struct CraneliftCodegen {
    module: ObjectModule,
    ctx: codegen::Context,
    func_ids: HashMap<String, FuncId>,
}

impl CraneliftCodegen {
    pub fn new(target: &str) -> Result<Self, String> {
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "speed").unwrap();

        let isa_builder = cranelift_native::builder()
            .map_err(|e| format!("ISA error: {}", e))?;
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .map_err(|e| format!("ISA finish error: {}", e))?;

        let builder = ObjectBuilder::new(
            isa,
            "simple_module",
            cranelift_module::default_libcall_names(),
        )
        .map_err(|e| format!("ObjectBuilder error: {}", e))?;

        let module = ObjectModule::new(builder);

        Ok(Self {
            module,
            ctx: module.make_context(),
            func_ids: HashMap::new(),
        })
    }

    pub fn compile_module(&mut self, mir: &MirModule) -> Result<Vec<u8>, String> {
        // Declare all functions first
        for func in &mir.functions {
            let sig = self.translate_signature(&func.signature);
            let linkage = if func.is_public {
                Linkage::Export
            } else {
                Linkage::Local
            };

            let id = self.module
                .declare_function(&func.name, linkage, &sig)
                .map_err(|e| format!("Declare error: {}", e))?;

            self.func_ids.insert(func.name.clone(), id);
        }

        // Compile each function
        for func in &mir.functions {
            self.compile_function(func)?;
        }

        // Finish and get object code
        let product = self.module.finish();
        Ok(product.emit().map_err(|e| format!("Emit error: {}", e))?)
    }

    fn compile_function(&mut self, func: &MirFunction) -> Result<(), String> {
        let func_id = self.func_ids[&func.name];

        self.ctx.func.signature = self.translate_signature(&func.signature);
        self.ctx.func.name = ExternalName::user(0, func_id.as_u32());

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut builder_ctx);

        // Create entry block
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Map MIR blocks to Cranelift blocks
        let mut block_map: HashMap<BlockId, Block> = HashMap::new();
        block_map.insert(BlockId(0), entry_block);

        for mir_block in &func.blocks[1..] {
            let cl_block = builder.create_block();
            block_map.insert(mir_block.id, cl_block);
        }

        // Map MIR locals to Cranelift variables
        let mut var_map: HashMap<LocalId, Variable> = HashMap::new();
        for (i, local) in func.locals.iter().enumerate() {
            let var = Variable::new(i);
            let ty = self.translate_type(&local.ty);
            builder.declare_var(var, ty);
            var_map.insert(local.id, var);
        }

        // Translate each block
        for mir_block in &func.blocks {
            if mir_block.id != BlockId(0) {
                builder.switch_to_block(block_map[&mir_block.id]);
            }

            // Translate instructions
            for inst in &mir_block.instructions {
                self.translate_instruction(&mut builder, inst, &var_map)?;
            }

            // Translate terminator
            self.translate_terminator(&mut builder, &mir_block.terminator, &block_map, &var_map)?;
        }

        builder.seal_all_blocks();
        builder.finalize();

        // Compile and define
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| format!("Define error: {}", e))?;

        self.module.clear_context(&mut self.ctx);
        Ok(())
    }

    fn translate_instruction(
        &self,
        builder: &mut FunctionBuilder,
        inst: &MirInst,
        vars: &HashMap<LocalId, Variable>,
    ) -> Result<(), String> {
        match inst {
            MirInst::ConstInt(dest, value) => {
                let val = builder.ins().iconst(types::I64, *value);
                builder.def_var(vars[dest], val);
            }

            MirInst::ConstFloat(dest, value) => {
                let val = builder.ins().f64const(*value);
                builder.def_var(vars[dest], val);
            }

            MirInst::ConstBool(dest, value) => {
                let val = builder.ins().iconst(types::I8, *value as i64);
                builder.def_var(vars[dest], val);
            }

            MirInst::Add(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().iadd(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Sub(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().isub(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Mul(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().imul(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Div(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().sdiv(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Lt(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let cmp = builder.ins().icmp(IntCC::SignedLessThan, l, r);
                builder.def_var(vars[dest], cmp);
            }

            MirInst::Call(dest, name, args) => {
                let func_id = self.func_ids.get(name)
                    .ok_or_else(|| format!("Unknown function: {}", name))?;
                let func_ref = self.module.declare_func_in_func(*func_id, builder.func);

                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| builder.use_var(vars[a]))
                    .collect();

                let call = builder.ins().call(func_ref, &arg_vals);
                let results = builder.inst_results(call);
                if !results.is_empty() {
                    builder.def_var(vars[dest], results[0]);
                }
            }

            MirInst::Copy(dest, src) => {
                let val = builder.use_var(vars[src]);
                builder.def_var(vars[dest], val);
            }

            // ... more instructions
            _ => {}
        }

        Ok(())
    }

    fn translate_terminator(
        &self,
        builder: &mut FunctionBuilder,
        term: &Terminator,
        blocks: &HashMap<BlockId, Block>,
        vars: &HashMap<LocalId, Variable>,
    ) -> Result<(), String> {
        match term {
            Terminator::Return(Some(local)) => {
                let val = builder.use_var(vars[local]);
                builder.ins().return_(&[val]);
            }

            Terminator::Return(None) => {
                builder.ins().return_(&[]);
            }

            Terminator::Branch(target) => {
                builder.ins().jump(blocks[target], &[]);
            }

            Terminator::CondBranch { cond, then_block, else_block } => {
                let cond_val = builder.use_var(vars[cond]);
                builder.ins().brif(cond_val, blocks[then_block], &[], blocks[else_block], &[]);
            }

            Terminator::Unreachable => {
                builder.ins().trap(TrapCode::UnreachableCodeReached);
            }

            _ => {}
        }

        Ok(())
    }

    fn translate_signature(&self, sig: &FunctionSignature) -> Signature {
        let mut cl_sig = Signature::new(CallConv::SystemV);

        for param in &sig.params {
            cl_sig.params.push(AbiParam::new(self.translate_type(param)));
        }

        if sig.returns != MirType::Void {
            cl_sig.returns.push(AbiParam::new(self.translate_type(&sig.returns)));
        }

        cl_sig
    }

    fn translate_type(&self, ty: &MirType) -> types::Type {
        match ty {
            MirType::I8 => types::I8,
            MirType::I16 => types::I16,
            MirType::I32 => types::I32,
            MirType::I64 => types::I64,
            MirType::F32 => types::F32,
            MirType::F64 => types::F64,
            MirType::Bool => types::I8,
            MirType::Ptr(_) => types::I64,  // Pointer is 64-bit
            MirType::Void => types::I64,    // Placeholder
            _ => types::I64,
        }
    }
}
```

---

---

Next: [SMF Linker and Pipeline](05_ahead_of_time_compile_smf.md)
