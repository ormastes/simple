# How to Implement Codegen

Part of [Codegen Technical Documentation](codegen_technical.md).

## How to Implement in Another Project

This section provides a step-by-step guide for implementing a similar codegen system in a different compiler project.

### Prerequisites

Before starting, you need:
1. A parser that produces an AST
2. A type system (can be simple or complex)
3. Understanding of your target language's semantics

### Step 1: Define Your IR Hierarchy

Design your intermediate representations. The Simple Language uses three stages:

```
┌─────────────────────────────────────────────────────────────────────┐
│                           IR Design                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  1. AST (Abstract Syntax Tree)                                       │
│     - Mirrors source syntax                                          │
│     - Nodes: Statement, Expression, Declaration, etc.                │
│     - Purpose: Parsing, error reporting, syntax highlighting         │
│                                                                      │
│  2. HIR (High-level IR)                                              │
│     - Type-annotated expressions                                     │
│     - Desugared constructs (for loops → while loops)                 │
│     - Purpose: Type checking, trait resolution, generics             │
│                                                                      │
│  3. MIR (Mid-level IR)                                               │
│     - Control flow graph (CFG) with basic blocks                     │
│     - SSA-like virtual registers                                     │
│     - Explicit instructions (no nested expressions)                  │
│     - Purpose: Optimization, analysis, codegen                       │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

#### Minimal MIR Definition

```rust
// Basic block identifier
pub struct BlockId(pub u32);

// Virtual register (SSA-style value)
pub struct VReg(pub u32);

// Basic block with instructions and terminator
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

// Block terminator (control flow)
pub enum Terminator {
    Return(Option<VReg>),
    Jump(BlockId),
    Branch { cond: VReg, then_block: BlockId, else_block: BlockId },
    Unreachable,
}

// Instructions - start simple, add more as needed
pub enum Instruction {
    // Constants
    ConstInt { dest: VReg, value: i64 },
    ConstFloat { dest: VReg, value: f64 },
    ConstBool { dest: VReg, value: bool },

    // Operations
    BinOp { dest: VReg, op: BinOp, left: VReg, right: VReg },
    UnaryOp { dest: VReg, op: UnaryOp, operand: VReg },

    // Control
    Call { dest: Option<VReg>, func: String, args: Vec<VReg> },

    // Memory (add later)
    Load { dest: VReg, addr: VReg },
    Store { addr: VReg, value: VReg },
}

// Function definition
pub struct Function {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub return_type: Type,
    pub blocks: Vec<BasicBlock>,
    pub entry_block: BlockId,
}
```

### Step 2: Set Up Cranelift

Add Cranelift dependencies to your project:

```toml
# Cargo.toml
[dependencies]
cranelift-codegen = "0.111"      # Core codegen
cranelift-frontend = "0.111"     # SSA builder helpers
cranelift-module = "0.111"       # Module/linking support
cranelift-object = "0.111"       # Object file emission
cranelift-jit = "0.111"          # Optional: JIT compilation
target-lexicon = "0.12"          # Target triple handling
```

#### Basic Cranelift Setup

```rust
use cranelift_codegen::ir::{AbiParam, Function, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub struct Codegen {
    module: ObjectModule,
    ctx: cranelift_codegen::Context,
    func_ctx: FunctionBuilderContext,
}

impl Codegen {
    pub fn new() -> Self {
        // 1. Configure settings
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "speed").unwrap();
        let flags = settings::Flags::new(flag_builder);

        // 2. Create target ISA
        let isa_builder = cranelift_native::builder().unwrap();
        let isa = isa_builder.finish(flags).unwrap();

        // 3. Create module
        let builder = ObjectBuilder::new(
            isa,
            "my_module",
            cranelift_module::default_libcall_names(),
        ).unwrap();
        let module = ObjectModule::new(builder);

        Self {
            module,
            ctx: cranelift_codegen::Context::new(),
            func_ctx: FunctionBuilderContext::new(),
        }
    }
}
```

### Step 3: Implement Basic Codegen

Start with the simplest possible function: returning a constant.

```rust
impl Codegen {
    /// Compile a function that returns a constant integer.
    pub fn compile_const_function(&mut self, name: &str, value: i64) -> Result<(), String> {
        // 1. Create function signature: fn() -> i64
        let mut sig = self.module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        // 2. Declare function in module
        let func_id = self.module
            .declare_function(name, Linkage::Export, &sig)
            .map_err(|e| e.to_string())?;

        // 3. Set up function context
        self.ctx.func.signature = sig;
        self.ctx.func.name = cranelift_codegen::ir::UserFuncName::user(0, func_id.as_u32());

        // 4. Build function body
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);

        // Create entry block
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Generate: return constant
        let const_val = builder.ins().iconst(types::I64, value);
        builder.ins().return_(&[const_val]);

        builder.finalize();

        // 5. Define function
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| e.to_string())?;

        // 6. Clear context for next function
        self.module.clear_context(&mut self.ctx);

        Ok(())
    }
}
```

### Step 4: Implement MIR → Cranelift Translation

Now connect your MIR to Cranelift:

```rust
impl Codegen {
    pub fn compile_function(&mut self, func: &Function) -> Result<(), String> {
        // 1. Create signature from function params/return
        let mut sig = self.module.make_signature();
        for (_name, ty) in &func.params {
            sig.params.push(AbiParam::new(type_to_cranelift(ty)));
        }
        if func.return_type != Type::Void {
            sig.returns.push(AbiParam::new(type_to_cranelift(&func.return_type)));
        }

        // 2. Declare function
        let func_id = self.module
            .declare_function(&func.name, Linkage::Export, &sig)
            .map_err(|e| e.to_string())?;

        self.ctx.func.signature = sig;

        // 3. Build function
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);

        // Create Cranelift blocks for each MIR block
        let mut blocks: HashMap<BlockId, cranelift_codegen::ir::Block> = HashMap::new();
        for mir_block in &func.blocks {
            let cl_block = builder.create_block();
            blocks.insert(mir_block.id, cl_block);
        }

        // Map virtual registers to Cranelift values
        let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();

        // Set up entry block with parameters
        let entry_block = blocks[&func.entry_block];
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        // Map function parameters to vregs
        for (i, (name, _ty)) in func.params.iter().enumerate() {
            let param_val = builder.block_params(entry_block)[i];
            // Assume params are VReg(0), VReg(1), etc.
            vreg_values.insert(VReg(i as u32), param_val);
        }

        // 4. Compile each block
        for mir_block in &func.blocks {
            let cl_block = blocks[&mir_block.id];
            builder.switch_to_block(cl_block);

            // Compile instructions
            for inst in &mir_block.instructions {
                self.compile_instruction(inst, &mut builder, &mut vreg_values)?;
            }

            // Compile terminator
            self.compile_terminator(&mir_block.terminator, &mut builder, &vreg_values, &blocks)?;
        }

        // 5. Seal all blocks and finalize
        for mir_block in &func.blocks {
            builder.seal_block(blocks[&mir_block.id]);
        }
        builder.finalize();

        // 6. Define function
        self.module.define_function(func_id, &mut self.ctx)?;
        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    fn compile_instruction(
        &self,
        inst: &Instruction,
        builder: &mut FunctionBuilder,
        vreg_values: &mut HashMap<VReg, cranelift_codegen::ir::Value>,
    ) -> Result<(), String> {
        match inst {
            Instruction::ConstInt { dest, value } => {
                let val = builder.ins().iconst(types::I64, *value);
                vreg_values.insert(*dest, val);
            }

            Instruction::ConstFloat { dest, value } => {
                let val = builder.ins().f64const(*value);
                vreg_values.insert(*dest, val);
            }

            Instruction::ConstBool { dest, value } => {
                let val = builder.ins().iconst(types::I8, if *value { 1 } else { 0 });
                vreg_values.insert(*dest, val);
            }

            Instruction::BinOp { dest, op, left, right } => {
                let lhs = vreg_values[left];
                let rhs = vreg_values[right];

                let result = match op {
                    BinOp::Add => builder.ins().iadd(lhs, rhs),
                    BinOp::Sub => builder.ins().isub(lhs, rhs),
                    BinOp::Mul => builder.ins().imul(lhs, rhs),
                    BinOp::Div => builder.ins().sdiv(lhs, rhs),
                    BinOp::Lt => {
                        let cmp = builder.ins().icmp(
                            cranelift_codegen::ir::condcodes::IntCC::SignedLessThan,
                            lhs, rhs
                        );
                        builder.ins().uextend(types::I64, cmp)
                    }
                    // Add more operators as needed
                };
                vreg_values.insert(*dest, result);
            }

            Instruction::Call { dest, func, args } => {
                // Look up function, call it, store result
                // (Implementation depends on your function registry)
                todo!("Implement function calls");
            }

            _ => todo!("Implement other instructions"),
        }
        Ok(())
    }

    fn compile_terminator(
        &self,
        term: &Terminator,
        builder: &mut FunctionBuilder,
        vreg_values: &HashMap<VReg, cranelift_codegen::ir::Value>,
        blocks: &HashMap<BlockId, cranelift_codegen::ir::Block>,
    ) -> Result<(), String> {
        match term {
            Terminator::Return(None) => {
                builder.ins().return_(&[]);
            }

            Terminator::Return(Some(val)) => {
                let ret_val = vreg_values[val];
                builder.ins().return_(&[ret_val]);
            }

            Terminator::Jump(target) => {
                let target_block = blocks[target];
                builder.ins().jump(target_block, &[]);
            }

            Terminator::Branch { cond, then_block, else_block } => {
                let cond_val = vreg_values[cond];
                let then_bl = blocks[then_block];
                let else_bl = blocks[else_block];
                builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
            }

            Terminator::Unreachable => {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
            }
        }
        Ok(())
    }
}

fn type_to_cranelift(ty: &Type) -> types::Type {
    match ty {
        Type::I64 => types::I64,
        Type::F64 => types::F64,
        Type::Bool => types::I8,
        Type::Void => types::I64, // Use I64 for void ABI
        _ => types::I64, // Default to pointer-sized
    }
}
```

### Step 5: Implement Runtime FFI

For complex operations, define runtime functions in Rust and call them from generated code:

```rust
// runtime/src/lib.rs
#[no_mangle]
pub extern "C" fn rt_array_new(capacity: i64) -> *mut Vec<i64> {
    let v = Vec::with_capacity(capacity as usize);
    Box::into_raw(Box::new(v))
}

#[no_mangle]
pub extern "C" fn rt_array_push(arr: *mut Vec<i64>, value: i64) {
    unsafe {
        (*arr).push(value);
    }
}

#[no_mangle]
pub extern "C" fn rt_array_get(arr: *mut Vec<i64>, index: i64) -> i64 {
    unsafe {
        (*arr).get(index as usize).copied().unwrap_or(0)
    }
}
```

Register FFI functions in codegen:

```rust
impl Codegen {
    fn register_runtime_functions(&mut self) -> HashMap<String, FuncId> {
        let mut funcs = HashMap::new();

        // rt_array_new: (i64) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = self.module.declare_function(
            "rt_array_new",
            Linkage::Import,
            &sig
        ).unwrap();
        funcs.insert("rt_array_new".to_string(), id);

        // Add more runtime functions...

        funcs
    }

    fn call_runtime(
        &self,
        name: &str,
        args: &[cranelift_codegen::ir::Value],
        builder: &mut FunctionBuilder,
        runtime_funcs: &HashMap<String, FuncId>,
    ) -> cranelift_codegen::ir::Value {
        let func_id = runtime_funcs[name];
        let func_ref = self.module.declare_func_in_func(func_id, builder.func);
        let call = builder.ins().call(func_ref, args);
        builder.inst_results(call)[0]
    }
}
```

### Step 6: Implement Body Block Outlining

For async constructs (futures, generators, actors), implement outlining:

```rust
impl Codegen {
    /// Extract a block into a standalone function.
    fn outline_block(
        &self,
        parent: &Function,
        body_block: BlockId,
        live_ins: &[VReg],
    ) -> Function {
        // 1. Create new function
        let mut outlined = Function {
            name: format!("{}_outlined_{}", parent.name, body_block.0),
            params: vec![("ctx".to_string(), Type::Ptr)], // Context parameter
            return_type: Type::I64,
            blocks: vec![],
            entry_block: body_block,
        };

        // 2. Copy only reachable blocks from body_block
        let reachable = self.compute_reachable(parent, body_block);
        for block in &parent.blocks {
            if reachable.contains(&block.id) {
                outlined.blocks.push(block.clone());
            }
        }

        // 3. Add capture-loading prologue to entry block
        let entry = outlined.blocks.iter_mut()
            .find(|b| b.id == body_block)
            .unwrap();

        // Insert loads from ctx array at the beginning
        let mut prologue = Vec::new();
        for (idx, vreg) in live_ins.iter().enumerate() {
            prologue.push(Instruction::RuntimeCall {
                dest: Some(*vreg),
                func: "rt_array_get".to_string(),
                args: vec![VReg(0), VReg::constant(idx as i64)], // ctx, index
            });
        }
        prologue.append(&mut entry.instructions);
        entry.instructions = prologue;

        outlined
    }

    fn compute_reachable(&self, func: &Function, start: BlockId) -> HashSet<BlockId> {
        let mut reachable = HashSet::new();
        let mut stack = vec![start];

        while let Some(id) = stack.pop() {
            if !reachable.insert(id) {
                continue;
            }
            if let Some(block) = func.blocks.iter().find(|b| b.id == id) {
                for succ in block.terminator.successors() {
                    stack.push(succ);
                }
            }
        }
        reachable
    }
}
```

### Step 7: Implement Generator State Machine

The most complex part - transform generators into state machines:

```rust
/// Generator state machine transformation.
pub struct GeneratorLowering {
    pub rewritten: Function,
    pub states: Vec<GeneratorState>,
}

pub struct GeneratorState {
    pub state_id: u32,
    pub yield_block: BlockId,
    pub resume_block: BlockId,
    pub live_after_yield: Vec<VReg>,
}

pub fn lower_generator(func: &Function, body_block: BlockId) -> GeneratorLowering {
    let mut rewritten = func.clone();
    let mut states = Vec::new();
    let mut state_id = 0;

    // 1. Find all Yield instructions
    for block in &func.blocks {
        for (inst_idx, inst) in block.instructions.iter().enumerate() {
            if let Instruction::Yield { value } = inst {
                // Compute live variables after this yield
                let live_after = compute_live_at(func, block.id, inst_idx + 1);

                // Create resume block for instructions after yield
                let resume_block = split_block_after(&mut rewritten, block.id, inst_idx);

                states.push(GeneratorState {
                    state_id,
                    yield_block: block.id,
                    resume_block,
                    live_after_yield: live_after,
                });

                state_id += 1;
            }
        }
    }

    // 2. Create dispatcher block at entry
    let dispatcher = create_dispatcher(&mut rewritten, body_block, &states);
    rewritten.entry_block = dispatcher;

    // 3. Create completion block
    let completion = create_completion_block(&mut rewritten);

    // 4. Transform each Yield into: save state, return value
    for state in &states {
        transform_yield(&mut rewritten, state);
    }

    GeneratorLowering { rewritten, states }
}

fn create_dispatcher(
    func: &mut Function,
    body_start: BlockId,
    states: &[GeneratorState],
) -> BlockId {
    let dispatcher_id = func.new_block();
    let dispatcher = func.block_mut(dispatcher_id).unwrap();

    // gen_param = parameter 0 (the generator object)
    // state = rt_generator_get_state(gen_param)
    dispatcher.instructions.push(Instruction::RuntimeCall {
        dest: Some(VReg::STATE),
        func: "rt_generator_get_state".to_string(),
        args: vec![VReg::GEN_PARAM],
    });

    // Switch on state: 0 → body_start, 1 → resume_1, 2 → resume_2, ...
    // (Implemented as chain of conditional branches)

    dispatcher_id
}

fn transform_yield(func: &mut Function, state: &GeneratorState) {
    let block = func.block_mut(state.yield_block).unwrap();

    // Find and replace Yield instruction with:
    // 1. Store live variables to frame slots
    // 2. Set next state
    // 3. Return yielded value

    let mut new_instructions = Vec::new();

    for inst in &block.instructions {
        if let Instruction::Yield { value } = inst {
            // Store each live variable
            for (idx, vreg) in state.live_after_yield.iter().enumerate() {
                new_instructions.push(Instruction::RuntimeCall {
                    dest: None,
                    func: "rt_generator_store_slot".to_string(),
                    args: vec![VReg::GEN_PARAM, VReg::constant(idx as i64), *vreg],
                });
            }

            // Set next state
            new_instructions.push(Instruction::RuntimeCall {
                dest: None,
                func: "rt_generator_set_state".to_string(),
                args: vec![VReg::GEN_PARAM, VReg::constant((state.state_id + 1) as i64)],
            });

            // Return yielded value
            block.terminator = Terminator::Return(Some(*value));
        } else {
            new_instructions.push(inst.clone());
        }
    }

    block.instructions = new_instructions;
}
```

### Step 8: Emit and Link

Finally, emit the object file and link:

```rust
impl Codegen {
    /// Emit object file
    pub fn emit_object(self) -> Vec<u8> {
        let product = self.module.finish();
        product.emit().unwrap()
    }

    /// Write to file
    pub fn write_object(&self, path: &str) -> Result<(), std::io::Error> {
        let bytes = self.emit_object();
        std::fs::write(path, bytes)
    }
}

// Linking (using system linker)
fn link_executable(object_path: &str, output_path: &str, runtime_lib: &str) {
    std::process::Command::new("cc")
        .args(&[
            object_path,
            "-o", output_path,
            "-L", "path/to/runtime",
            "-l", runtime_lib,
        ])
        .status()
        .expect("Failed to link");
}
```

### Complete Implementation Checklist

```
□ Phase 1: Basic Infrastructure
  □ Define MIR data structures (blocks, instructions, terminators)
  □ Set up Cranelift module and context
  □ Implement type conversion (your types → Cranelift types)
  □ Compile a function that returns a constant

□ Phase 2: Core Instructions
  □ ConstInt, ConstFloat, ConstBool
  □ BinOp (arithmetic, comparison)
  □ UnaryOp (negation, not)
  □ Copy (register to register)

□ Phase 3: Control Flow
  □ Jump (unconditional branch)
  □ Branch (conditional branch)
  □ Return (with/without value)
  □ Block parameter passing (phi nodes)

□ Phase 4: Function Calls
  □ Direct function calls
  □ Register function signatures
  □ Handle return values

□ Phase 5: Runtime FFI
  □ Define runtime functions in Rust
  □ Import runtime functions in Cranelift
  □ Implement collection operations (array, tuple, dict)

□ Phase 6: Memory Operations
  □ Load/Store instructions
  □ Stack allocation for locals
  □ Heap allocation (GC integration)

□ Phase 7: Closures
  □ ClosureCreate (allocate + store fn_ptr + captures)
  □ IndirectCall (load fn_ptr + call)
  □ Capture loading

□ Phase 8: Objects/Structs
  □ StructInit (allocate + store fields)
  □ FieldGet (load at offset)
  □ FieldSet (store at offset)

□ Phase 9: Outlining (for async constructs)
  □ Compute live-ins via liveness analysis
  □ Create outlined functions from blocks
  □ Pack/unpack captures via ctx array

□ Phase 10: Generators
  □ Discover yield points
  □ Compute live-after-yield sets
  □ Create dispatcher block
  □ Transform yields into state saves + returns
  □ Implement resume logic

□ Phase 11: Testing & Parity
  □ Unit tests for each instruction type
  □ Integration tests for function calls
  □ System tests for full programs
  □ Parity tests (compiled vs. interpreted)
```

### Common Pitfalls and Solutions

| Problem | Symptom | Solution |
|---------|---------|----------|
| Block not sealed | Cranelift panic: "block not sealed" | Call `builder.seal_block()` after all predecessors are defined |
| Wrong type | Cranelift panic: "type mismatch" | Use correct Cranelift type (I8 for bool, I64 for pointers) |
| Missing return | Cranelift panic: "block has no terminator" | Every block must end with a terminator |
| FFI signature mismatch | Runtime crash or wrong values | Ensure Rust function signature matches Cranelift signature exactly |
| Capture not loaded | Variable has wrong value | Load captures at outlined function entry before use |
| Generator state corruption | Wrong values after yield | Store ALL live variables, not just those explicitly used |

### Performance Tips

1. **Minimize FFI calls**: Inline simple operations, batch complex ones
2. **Use native types**: I64 for integers, F64 for floats, avoid boxing
3. **Compute offsets at compile time**: Store byte offsets in MIR, not at runtime
4. **Seal blocks early**: Call `seal_block()` as soon as all predecessors are known
5. **Clear context between functions**: Reuse `Context` and `FunctionBuilderContext`

---

## References

- `doc/status/generator_state_machine_codegen.md` - Feature 101 status
- `doc/status/future_body_execution.md` - Feature 102 status
- `doc/status/capture_buffer_vreg_remapping.md` - Feature 100 status
- `doc/status/codegen_parity_completion.md` - Feature 103 status
- `doc/features/feature.md` - Complete feature list with ratings
- [Cranelift Documentation](https://cranelift.dev/)
- [Cranelift IR Reference](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md)

---

Back to: [Codegen Technical Documentation](codegen_technical.md)
