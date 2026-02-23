# Phase 3: LLVM Backend - Implementation Guide

**Status:** 20% Complete (Type mapper done, IR builder scaffolded)
**Timeline:** 4-5 weeks (3 parallel tracks)
**Goal:** Complete LLVM backend to enable 32-bit embedded targets (Arduino, ESP32, STM32)

---

## Table of Contents

1. [Overview](#overview)
2. [Why LLVM Matters](#why-llvm-matters)
3. [Current State](#current-state)
4. [Architecture Overview](#architecture-overview)
5. [Track A: MIR → LLVM IR Translation](#track-a-mir--llvm-ir-translation)
6. [Track B: Runtime FFI Integration](#track-b-runtime-ffi-integration)
7. [Track C: Cross-Compilation Support](#track-c-cross-compilation-support)
8. [Testing Strategy](#testing-strategy)
9. [Timeline & Milestones](#timeline--milestones)
10. [File Reference](#file-reference)

---

## Overview

Phase 3 completes the LLVM backend to unlock 32-bit embedded platforms. Cranelift (our current backend) dropped 32-bit support in 2022, making LLVM the only viable option for:

- **Arduino** (AVR, ARM Cortex-M)
- **ESP32** (Xtensa, RISC-V)
- **STM32** (ARM Cortex-M series)
- **Raspberry Pi Zero** (ARMv6)

The LLVM backend shares the same MIR intermediate representation and runtime FFI as Cranelift, so 80% of the compiler pipeline remains unchanged. We're only implementing the final backend layer.

---

## Why LLVM Matters

### Cranelift Limitations

Cranelift deliberately dropped 32-bit support in April 2022:

- **No i686** (Intel 32-bit)
- **No armv7** (ARM Cortex-A 32-bit)
- **No riscv32** (RISC-V embedded)

This blocks us from:
- Embedded systems (most use 32-bit MCUs)
- Legacy hardware support
- Educational platforms (Arduino, Raspberry Pi Zero)

### LLVM Advantages

- **Universal platform support:** 6 architectures (3 x 64-bit + 3 x 32-bit)
- **Battle-tested:** Production compiler for C/C++/Rust
- **Mature optimization:** 100+ optimization passes
- **Bare-metal support:** No OS required (perfect for embedded)

---

## Current State

### Completed (20%)

| Component | File | Status | LOC |
|-----------|------|--------|-----|
| Type mapper | `llvm_type_mapper.spl` | ✅ Complete | 305 |
| Target config | `llvm_target.spl` | ✅ Complete | 364 |
| IR builder scaffold | `llvm_ir_builder.spl` | ✅ Scaffolded | 1123 |
| Backend API | `llvm_backend.spl` | ✅ Basic impl | 400 |

**Total:** ~2200 lines, basic structure in place

### Remaining (80%)

| Track | Component | Status | Estimated LOC |
|-------|-----------|--------|---------------|
| A | MIR → IR translation | 🚧 Partial | +2000 |
| B | Runtime FFI bridge | ❌ Not started | +500 |
| C | Cross-compilation | ❌ Not started | +300 |

**Total:** ~2800 lines of new code

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────┐
│                 Simple Source Code                   │
└─────────────────┬───────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────┐
│          Parser → AST → HIR → MIR                   │
│         (shared with Cranelift backend)             │
└─────────────────┬───────────────────────────────────┘
                  │
                  ▼
          ┌───────┴────────┐
          │                │
    ┌─────▼─────┐   ┌──────▼──────┐
    │ Cranelift │   │    LLVM     │  ◄─── Phase 3
    │  Backend  │   │   Backend   │
    └─────┬─────┘   └──────┬──────┘
          │                │
          ▼                ▼
    ┌──────────────────────────┐
    │  Machine Code (64-bit)   │
    └──────────────────────────┘
                  ▲
                  │
          ┌───────┴────────┐
          │                │
    ┌─────▼─────┐   ┌──────▼──────┐
    │  x86_64   │   │   i686      │  ◄─── New!
    │  aarch64  │   │   armv7     │  ◄─── New!
    │  riscv64  │   │   riscv32   │  ◄─── New!
    └───────────┘   └─────────────┘
```

### Component Diagram

```
LlvmBackend
    │
    ├─ LlvmTargetConfig
    │   ├─ LlvmTargetTriple (arch-vendor-os-env)
    │   └─ CPU selection (x86-64-v3, cortex-a7, etc.)
    │
    ├─ LlvmTypeMapper
    │   └─ MirType → LLVM IR type strings
    │
    └─ MirToLlvm (translator)
        ├─ LlvmIRBuilder (instruction emission)
        └─ Runtime bridge (rt_* function declarations)
```

---

## Track A: MIR → LLVM IR Translation

**Duration:** 3 weeks
**Deliverable:** Translate all 50+ MIR opcodes to LLVM IR
**File:** `src/compiler/backend/llvm_ir_builder.spl`

### Week 1: Core IR Translation (800 LOC)

#### Current State

```simple
struct LLVMIRBuilder:
    module_name: text
    target: LlvmTargetTriple
    instructions: [text]
    current_function: text?
    local_counter: i64
    debug_counter: i64
    size_type: text            # "i32" for 32-bit, "i64" for 64-bit
```

The IR builder has scaffolding for basic instruction emission (`emit_add`, `emit_load`, etc.) but needs full MIR translation.

#### Implementation Tasks

**1. Function Translation**

Add to `MirToLlvm` class:

```simple
me translate_function(name: text, body: MirBody):
    """Translate a MIR function to LLVM IR."""
    # Build local type map from function locals
    self.local_types = {}
    for local in body.locals:
        val llvm_ty = self.type_mapper.map_type(local.type_)
        self.local_types[local.id.id] = llvm_ty

    # Build parameter list
    var params: [text] = []
    for i in 0..body.arg_count:
        val param_ty = self.get_local_type(i)
        params = params.push("{param_ty} %arg{i}")

    val ret_ty = self.type_mapper.map_type(body.return_ty)

    self.builder.start_function(name, params, ret_ty)

    # Translate basic blocks
    for block in body.blocks:
        self.translate_block(block)

    self.builder.end_function()

fn get_local_type(id: i64) -> text:
    """Get LLVM type for a local variable."""
    match self.local_types.get(id):
        case Some(ty): ty
        case nil: self.native_int()  # Default to i64/i32
```

**2. Basic Block Translation**

```simple
me translate_block(block: MirBasicBlock):
    """Translate a MIR basic block."""
    self.builder.emit_label("bb{block.id}")

    # Translate instructions
    for inst in block.instructions:
        self.translate_instruction(inst)

    # Translate terminator
    self.translate_terminator(block.terminator)
```

**3. Instruction Translation (Core)**

```simple
me translate_instruction(inst: MirInst):
    """Translate a MIR instruction to LLVM IR."""
    match inst.kind:
        # === Constants ===
        case Const(dest, value, type_):
            val dest_name = self.get_local(dest.id)
            val ty = self.type_mapper.map_type(type_)
            val const_val = self.translate_const_value(value)
            self.builder.emit("  {dest_name} = add {ty} {const_val}, 0")

        # === Memory Operations ===
        case Alloc(dest, type_):
            val dest_name = self.get_local(dest.id)
            val ty = self.type_mapper.map_type(type_)
            self.builder.emit_alloca(dest_name, ty)

        case Load(dest, ptr):
            val dest_name = self.get_local(dest.id)
            val ptr_val = self.translate_operand(ptr)
            val load_ty = self.get_local_type(dest.id)
            self.builder.emit_load(dest_name, load_ty, ptr_val)

        case Store(ptr, value):
            val ptr_val = self.translate_operand(ptr)
            val value_val = self.translate_operand(value)
            val store_ty = self.get_operand_type(value)
            self.builder.emit_store(store_ty, value_val, ptr_val)

        # === Binary Operations ===
        case BinOp(dest, op, left, right):
            self.translate_binop(dest, op, left, right)

        # ... (continue for all instruction types)
```

**4. Operand Translation**

```simple
me translate_operand(operand: MirOperand) -> text:
    """Translate MIR operand to LLVM value."""
    match operand.kind:
        case Copy(local):
            self.get_local(local)
        case Move(local):
            self.get_local(local)
        case Const(value, type_):
            self.translate_const_value(value)

fn get_local(id: i64) -> text:
    """Get LLVM local name for MIR local."""
    match self.local_map.get(id):
        case Some(name): name
        case nil:
            val name = "%l{id}"
            self.local_map[id] = name
            name
```

#### Testing Week 1

Create `test/compiler/backend/llvm_basic_spec.spl`:

```simple
describe "LLVM IR Builder - Basic Translation":
    it "translates function with parameters":
        val mir = create_test_function(2)  # 2 parameters
        val translator = MirToLlvm__create("test", CodegenTarget.X86_64, nil)
        val ir = translator.translate_function("test_fn", mir)

        expect(ir).to_contain("define i64 @test_fn(i64 %arg0, i64 %arg1)")

    it "translates alloca instruction":
        val mir = create_alloca_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("alloca i64")

    it "translates load/store instructions":
        val mir = create_load_store_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("load i64, ptr")
        expect(ir).to_contain("store i64")
```

**Goal:** 10/10 tests passing (functions, basic blocks, memory ops)

---

### Week 2: Control Flow (600 LOC)

#### Implementation Tasks

**1. Terminators**

```simple
me translate_terminator(term: MirTerminator):
    """Translate block terminator to LLVM IR."""
    match term:
        case Return(value):
            if value.?:
                val val_str = self.translate_operand(value.unwrap())
                val nit = self.native_int()
                self.builder.emit_ret(nit, val_str)
            else:
                self.builder.emit_ret_void()

        case Goto(target):
            self.builder.emit_br("bb{target}")

        case If(cond, then_, else_):
            val cond_val = self.translate_operand(cond)
            val nit = self.native_int()
            # Convert to i1 if needed
            val i1_cond = self.builder.fresh_local()
            self.builder.emit("  {i1_cond} = icmp ne {nit} {cond_val}, 0")
            self.builder.emit_cond_br(i1_cond, "bb{then_}", "bb{else_}")

        case Switch(value, targets, default):
            val discr_val = self.translate_operand(value)
            val nit = self.native_int()
            var cases: [(text, text)] = []
            for switch_case in targets:
                val case_value = "{switch_case.value}"
                val case_label = "bb{switch_case.target}"
                cases = cases.push((case_value, case_label))
            self.builder.emit_switch(discr_val, nit, "bb{default}", cases)

        case Unreachable:
            self.builder.emit("  unreachable")

        case Abort(message):
            self.builder.emit("  call void @abort()  ; {message}")
            self.builder.emit("  unreachable")
```

**2. Conditional Branch Helper**

```simple
me emit_conditional_branch(cond: text, then_label: text, else_label: text):
    """Emit conditional branch with proper i1 conversion."""
    val nit = self.native_int()
    val i1_cond = self.builder.fresh_local()
    self.builder.emit("  {i1_cond} = icmp ne {nit} {cond}, 0")
    self.builder.emit_cond_br(i1_cond, then_label, else_label)
```

**3. Switch Table Generation**

```simple
me emit_switch_table(value: text, cases: [(i64, text)], default: text):
    """Generate efficient switch table."""
    val nit = self.native_int()
    var case_strs: [(text, text)] = []
    for (case_val, label) in cases:
        case_strs = case_strs.push(("{case_val}", label))
    self.builder.emit_switch(value, nit, default, case_strs)
```

#### Testing Week 2

Create `test/compiler/backend/llvm_control_flow_spec.spl`:

```simple
describe "LLVM Control Flow":
    it "translates if-else branches":
        val mir = create_if_else_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("br i1")
        expect(ir).to_contain("label %bb")

    it "translates switch statements":
        val mir = create_switch_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("switch i64")
        expect(ir).to_contain("label %")

    it "translates loops":
        val mir = create_loop_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("br label %loop_header")
```

**Goal:** 15/15 tests passing (if/else, loops, match/switch)

---

### Week 3: Operations & Intrinsics (600 LOC)

#### Implementation Tasks

**1. Arithmetic Operations**

```simple
me translate_binop(dest: LocalId, op: MirBinOp, left: MirOperand, right: MirOperand):
    """Translate binary operation."""
    val dest_name = self.get_local(dest.id)
    val left_val = self.translate_operand(left)
    val right_val = self.translate_operand(right)
    val ty = self.get_local_type(dest.id)

    match op:
        # Integer arithmetic
        case Add: self.builder.emit_add(dest_name, ty, left_val, right_val)
        case Sub: self.builder.emit_sub(dest_name, ty, left_val, right_val)
        case Mul: self.builder.emit_mul(dest_name, ty, left_val, right_val)
        case Div:
            if is_signed_type(ty):
                self.builder.emit_div(dest_name, ty, left_val, right_val)
            else:
                self.builder.emit_udiv(dest_name, ty, left_val, right_val)
        case Rem: self.builder.emit_rem(dest_name, ty, left_val, right_val)

        # Floating-point (auto-selected by type)
        # LLVM uses fadd/fsub/fmul/fdiv for float/double types

        # Bitwise
        case BitAnd: self.builder.emit_and(dest_name, ty, left_val, right_val)
        case BitOr: self.builder.emit_or(dest_name, ty, left_val, right_val)
        case BitXor: self.builder.emit_xor(dest_name, ty, left_val, right_val)
        case Shl: self.builder.emit_shl(dest_name, ty, left_val, right_val)
        case Shr: self.builder.emit_ashr(dest_name, ty, left_val, right_val)

        # Comparisons
        case Eq: self.builder.emit_icmp_eq(dest_name, ty, left_val, right_val)
        case Ne: self.builder.emit_icmp_ne(dest_name, ty, left_val, right_val)
        case Lt: self.builder.emit_icmp_slt(dest_name, ty, left_val, right_val)
        case Le: self.builder.emit_icmp_sle(dest_name, ty, left_val, right_val)
        case Gt: self.builder.emit_icmp_sgt(dest_name, ty, left_val, right_val)
        case Ge: self.builder.emit_icmp_sge(dest_name, ty, left_val, right_val)
```

**2. Unary Operations**

```simple
me translate_unaryop(dest: LocalId, op: MirUnaryOp, operand: MirOperand):
    """Translate unary operation."""
    val dest_name = self.get_local(dest.id)
    val operand_val = self.translate_operand(operand)
    val ty = self.get_local_type(dest.id)

    match op:
        case Neg:
            self.builder.emit_neg(dest_name, ty, operand_val)
        case Not:
            # Logical NOT: compare with 0
            self.builder.emit_icmp_eq(dest_name, ty, operand_val, "0")
        case BitNot:
            self.builder.emit_not(dest_name, ty, operand_val)
```

**3. Function Calls**

```simple
me translate_call(dest: LocalId?, func: MirOperand, args: [MirOperand]):
    """Translate function call."""
    val dest_name = if dest.?: Some(self.get_local(dest.unwrap().id)) else: nil
    val func_name = self.translate_operand(func)

    # Build argument list with types
    var arg_parts: [text] = []
    for arg in args:
        val arg_val = self.translate_operand(arg)
        val arg_ty = self.get_operand_type(arg)
        arg_parts = arg_parts.push("{arg_ty} {arg_val}")

    val args_str = arg_parts.join(", ")

    # Determine return type
    var ret_ty = "void"
    if dest.?:
        ret_ty = self.get_local_type(dest.unwrap().id)

    # Emit call
    if dest_name.?:
        self.builder.emit("  {dest_name.unwrap()} = call {ret_ty} {func_name}({args_str})")
    else:
        self.builder.emit("  call {ret_ty} {func_name}({args_str})")
```

**4. Type Conversions**

```simple
me translate_cast(dest: LocalId, operand: MirOperand, target: MirType):
    """Translate type cast."""
    val dest_name = self.get_local(dest.id)
    val operand_val = self.translate_operand(operand)
    val src_ty = self.get_operand_type(operand)
    val target_ty = self.type_mapper.map_type(target)

    val cast_inst = self.select_cast_instruction(src_ty, target_ty)
    self.builder.emit("  {dest_name} = {cast_inst} {src_ty} {operand_val} to {target_ty}")

fn select_cast_instruction(src_ty: text, target_ty: text) -> text:
    """Select appropriate LLVM cast instruction."""
    # Integer widening (sign-extend)
    if src_ty == "i8" and (target_ty == "i16" or target_ty == "i32" or target_ty == "i64"):
        return "sext"
    if src_ty == "i16" and (target_ty == "i32" or target_ty == "i64"):
        return "sext"
    if src_ty == "i32" and target_ty == "i64":
        return "sext"

    # Integer narrowing (truncate)
    if src_ty == "i64" and (target_ty == "i32" or target_ty == "i16" or target_ty == "i8"):
        return "trunc"

    # Integer to float
    if (src_ty == "i32" or src_ty == "i64") and (target_ty == "float" or target_ty == "double"):
        return "sitofp"

    # Float to integer
    if (src_ty == "float" or src_ty == "double") and (target_ty == "i32" or target_ty == "i64"):
        return "fptosi"

    # Pointer conversions
    if src_ty == "ptr" and (target_ty == "i32" or target_ty == "i64"):
        return "ptrtoint"
    if (src_ty == "i32" or src_ty == "i64") and target_ty == "ptr":
        return "inttoptr"

    # Default fallback
    "bitcast"
```

#### Testing Week 3

Create `test/compiler/backend/llvm_operations_spec.spl`:

```simple
describe "LLVM Operations":
    it "translates arithmetic operations":
        val mir = create_arithmetic_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("add i64")
        expect(ir).to_contain("sub i64")
        expect(ir).to_contain("mul i64")

    it "translates comparisons":
        val mir = create_comparison_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("icmp eq")
        expect(ir).to_contain("icmp slt")

    it "translates function calls":
        val mir = create_call_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("call i64 @")

    it "translates type casts":
        val mir = create_cast_test()
        val ir = translate_to_ir(mir)

        expect(ir).to_contain("sext i32")
        expect(ir).to_contain("trunc i64")
```

**Goal:** 25/25 tests passing (all MIR operations)

---

### Track A Summary

**Total LOC:** ~2000
**Total Tests:** 50 tests across 3 files
**Completion Criteria:**
- ✅ All 50+ MIR opcodes translate to valid LLVM IR
- ✅ Type system correctly maps MIR types to LLVM types
- ✅ Control flow (branches, loops, switches) generates correct IR
- ✅ All operations (arithmetic, bitwise, comparisons) work
- ✅ Function calls with proper ABI conventions

---

## Track B: Runtime FFI Integration

**Duration:** 1 week
**Deliverable:** Link LLVM-generated code with Simple runtime
**File:** `src/compiler/backend/llvm_runtime_bridge.spl` (new)

### Overview

The Simple runtime provides:
- **Garbage collection** (`rt_gc_malloc`, `rt_gc_collect`)
- **Value boxing** (`rt_value_int`, `rt_value_string`)
- **I/O operations** (`rt_print`, `rt_file_read`)
- **String operations** (`rt_string_concat`, `rt_string_len`)

We need to declare these as `extern` functions in LLVM IR so generated code can call them.

### Implementation

Create `src/compiler/backend/llvm_runtime_bridge.spl`:

```simple
# LLVM Runtime Bridge - Runtime Function Declarations
#
# Declares all rt_* functions as extern for LLVM IR.
# These link against libsimple_runtime.a at link time.

use compiler.backend.llvm_ir_builder.LlvmIRBuilder

fn declare_runtime_functions(builder: LlvmIRBuilder):
    """Declare all runtime functions as extern in LLVM IR."""

    # === Garbage Collection ===
    builder.emit("declare void @rt_gc_init()")
    builder.emit("declare ptr @rt_gc_malloc(i64)")
    builder.emit("declare void @rt_gc_collect()")
    builder.emit("declare void @rt_gc_register_root(ptr)")

    # === Value Boxing ===
    builder.emit("declare ptr @rt_value_int(i64)")
    builder.emit("declare ptr @rt_value_float(double)")
    builder.emit("declare ptr @rt_value_string(ptr, i64)")
    builder.emit("declare ptr @rt_value_bool(i1)")
    builder.emit("declare ptr @rt_value_nil()")

    # === Value Unboxing ===
    builder.emit("declare i64 @rt_value_as_int(ptr)")
    builder.emit("declare double @rt_value_as_float(ptr)")
    builder.emit("declare ptr @rt_value_as_string(ptr)")
    builder.emit("declare i1 @rt_value_as_bool(ptr)")

    # === Print Functions ===
    builder.emit("declare void @rt_print(ptr)")
    builder.emit("declare void @rt_println(ptr)")
    builder.emit("declare void @rt_eprint(ptr)")
    builder.emit("declare void @rt_eprintln(ptr)")

    # === String Functions ===
    builder.emit("declare ptr @rt_string_concat(ptr, ptr)")
    builder.emit("declare i64 @rt_string_len(ptr)")
    builder.emit("declare ptr @rt_string_slice(ptr, i64, i64)")
    builder.emit("declare i1 @rt_string_eq(ptr, ptr)")
    builder.emit("declare ptr @rt_string_from_int(i64)")

    # === Array Functions ===
    builder.emit("declare ptr @rt_array_new(i64)")
    builder.emit("declare i64 @rt_array_len(ptr)")
    builder.emit("declare ptr @rt_array_get(ptr, i64)")
    builder.emit("declare void @rt_array_set(ptr, i64, ptr)")
    builder.emit("declare ptr @rt_array_push(ptr, ptr)")

    # === I/O Functions ===
    builder.emit("declare ptr @rt_file_read_text(ptr)")
    builder.emit("declare void @rt_file_write_text(ptr, ptr)")
    builder.emit("declare i64 @rt_shell(ptr)")

    # === Math Functions ===
    builder.emit("declare double @rt_sqrt(double)")
    builder.emit("declare double @rt_sin(double)")
    builder.emit("declare double @rt_cos(double)")
    builder.emit("declare double @rt_pow(double, double)")

    # === Type Checking ===
    builder.emit("declare i1 @rt_value_is_int(ptr)")
    builder.emit("declare i1 @rt_value_is_string(ptr)")
    builder.emit("declare i1 @rt_value_is_nil(ptr)")

    # === Error Handling ===
    builder.emit("declare void @rt_panic(ptr)")
    builder.emit("declare void @rt_assert(i1, ptr)")

    builder.emit("")  # Blank line after declarations

export declare_runtime_functions
```

### Integration

Modify `MirToLlvm.translate_module()` to emit declarations:

```simple
me translate_module(module: MirModule) -> text:
    """Translate MIR module to LLVM IR."""
    self.builder.emit_module_header()

    # Emit runtime function declarations
    declare_runtime_functions(self.builder)

    # Translate user functions
    for name, body in module.functions:
        self.translate_function(name, body)

    self.builder.build()
```

### Linking

Add to `LlvmBackend.compile_module()`:

```simple
fn compile_module(module: MirModule) -> CompiledModule:
    """Compile MIR module to native code."""
    # Generate LLVM IR
    val translator = MirToLlvm__create(module.name, self.target, self.cpu_override)
    val llvm_ir = translator.translate_module(module)

    # Write IR to temp file
    val ir_path = "/tmp/simple_{getpid()}.ll"
    file_write(ir_path, llvm_ir)

    # Compile IR to object code
    val obj_path = "/tmp/simple_{getpid()}.o"
    val compile_result = shell("llc -filetype=obj {ir_path} -o {obj_path}")

    # Link with runtime library
    val exe_path = "/tmp/simple_{getpid()}"
    val runtime_lib = "bin/bootstrap/libsimple_runtime.a"
    val link_result = shell("clang {obj_path} {runtime_lib} -o {exe_path}")

    # Return compiled module
    CompiledModule(
        name: module.name,
        symbols: [CompiledSymbol(name: "main", address: 0, size: 0)],
        code: rt_file_read_bytes(exe_path)
    )
```

### Testing

Create `test/compiler/backend/llvm_runtime_spec.spl`:

```simple
describe "LLVM Runtime Integration":
    it "links with GC functions":
        val code = "
            fn main():
                val x = 42
                print x
        "
        val exe = compile_and_link(code)
        val output = run_exe(exe)

        expect(output).to_equal("42\n")

    it "links with string functions":
        val code = "
            fn main():
                val s = \"Hello\"
                print s
        "
        val exe = compile_and_link(code)
        val output = run_exe(exe)

        expect(output).to_equal("Hello\n")

    it "links with array functions":
        val code = "
            fn main():
                val arr = [1, 2, 3]
                print arr.len()
        "
        val exe = compile_and_link(code)
        val output = run_exe(exe)

        expect(output).to_equal("3\n")
```

**Goal:** 10/10 tests passing (runtime integration)

---

## Track C: Cross-Compilation Support

**Duration:** 2 weeks
**Deliverable:** Support 6 architectures (3 x 64-bit + 3 x 32-bit)
**Files:** `llvm_target.spl` (already exists), test suite

### Week 1: 64-bit Target Validation

#### Supported Targets

| Target | Triple | CPU | Features |
|--------|--------|-----|----------|
| x86_64 | `x86_64-unknown-linux-gnu` | x86-64-v3 | AVX2, FMA |
| aarch64 | `aarch64-unknown-linux-gnu` | cortex-a53 | NEON |
| riscv64 | `riscv64gc-unknown-linux-gnu` | generic-rv64 | IMAFDC |

#### Implementation

The target system is already implemented in `llvm_target.spl`. We need comprehensive testing.

Create `test/compiler/backend/llvm_target_64bit_spec.spl`:

```simple
describe "LLVM 64-bit Targets":
    it "generates correct triple for x86_64":
        val triple = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
        expect(triple.to_text()).to_equal("x86_64-unknown-linux-gnu")
        expect(triple.is_32bit()).to_equal(false)

    it "generates correct datalayout for x86_64":
        val triple = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
        val layout = triple.datalayout()
        expect(layout).to_contain("e-m:e")  # Little-endian, ELF mangling
        expect(layout).to_contain("p270:32:32")  # Program counter

    it "compiles hello world for x86_64":
        val code = "fn main(): print \"Hello\""
        val backend = LlvmBackend__create(CodegenTarget.X86_64, OptimizationLevel.Debug)
        val result = compile_code(backend, code)

        expect(result.code.len()).to_be_greater_than(0)

    it "supports aarch64 target":
        val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
        expect(triple.to_text()).to_equal("aarch64-unknown-linux-gnu")

    it "supports riscv64 target":
        val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
        expect(triple.to_text()).to_equal("riscv64-unknown-linux-gnu")
```

**Goal:** 15/15 tests passing (all 64-bit targets)

---

### Week 2: 32-bit Target Support

#### New Targets

| Target | Triple | CPU | Features | Use Case |
|--------|--------|-----|----------|----------|
| i686 | `i686-unknown-linux-gnu` | i686 | SSE2 | Legacy PCs |
| armv7 | `armv7-unknown-linux-gnueabihf` | cortex-a7 | NEON, VFP4 | Raspberry Pi 2/3 |
| riscv32 | `riscv32imac-unknown-none-elf` | generic-rv32 | IMAFC | Embedded MCUs |

#### Implementation Tasks

**1. ABI Handling**

Add to `llvm_target.spl`:

```simple
fn get_calling_convention(arch: text) -> text:
    """Get LLVM calling convention for architecture."""
    match arch:
        case "i686": "fastcc"      # Fast call for 32-bit x86
        case "armv7": "aapcs"      # ARM Procedure Call Standard
        case "riscv32": "cc 10"    # RISC-V calling convention
        case _: "ccc"              # C calling convention (default)

fn get_pointer_size(arch: text) -> i64:
    """Get pointer size in bytes."""
    match arch:
        case "i686" | "armv7" | "riscv32" | "wasm32": 4
        case _: 8
```

**2. Size Type Handling**

Modify `LlvmIRBuilder.__init__`:

```simple
static fn create(name: text, target: LlvmTargetTriple) -> LlvmIRBuilder:
    val size_ty = if target.is_32bit(): "i32" else: "i64"
    LlvmIRBuilder(
        module_name: name,
        target: target,
        instructions: [],
        current_function: nil,
        local_counter: 0,
        debug_counter: 10,
        size_type: size_ty  # Use i32 for 32-bit targets
    )
```

**3. Test 32-bit Targets**

Create `test/compiler/backend/llvm_target_32bit_spec.spl`:

```simple
describe "LLVM 32-bit Targets":
    it "generates correct triple for i686":
        val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
        expect(triple.to_text()).to_equal("i686-unknown-linux-gnu")
        expect(triple.is_32bit()).to_equal(true)

    it "uses i32 size type for i686":
        val builder = LlvmIRBuilder__create("test",
            LlvmTargetTriple__from_target(CodegenTarget.X86))
        expect(builder.size_type).to_equal("i32")

    it "generates correct datalayout for armv7":
        val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
        val layout = triple.datalayout()
        expect(layout).to_contain("p:32:32")  # 32-bit pointers

    it "compiles hello world for i686":
        val code = "fn main(): print \"Hello from i686\""
        val backend = LlvmBackend__create(CodegenTarget.X86, OptimizationLevel.Debug)
        val result = compile_code(backend, code)

        expect(result.code.len()).to_be_greater_than(0)

    it "supports bare-metal riscv32":
        val triple = LlvmTargetTriple__from_target_baremetal(CodegenTarget.Riscv32)
        expect(triple.to_text()).to_equal("riscv32-unknown-none-eabi")
```

**Goal:** 15/15 tests passing (all 32-bit targets)

---

### Cross-Compilation Validation

**End-to-end test:** Compile same program for all 6 targets

```simple
describe "LLVM Cross-Compilation":
    it "compiles fibonacci for all targets":
        val code = "
            fn fib(n: i64) -> i64:
                if n <= 1: n
                else: fib(n - 1) + fib(n - 2)

            fn main():
                print fib(10)
        "

        val targets = [
            CodegenTarget.X86_64,
            CodegenTarget.AArch64,
            CodegenTarget.Riscv64,
            CodegenTarget.X86,
            CodegenTarget.Arm,
            CodegenTarget.Riscv32
        ]

        for target in targets:
            val backend = LlvmBackend__create(target, OptimizationLevel.Speed)
            val result = compile_code(backend, code)

            expect(result.code.len()).to_be_greater_than(0)
            # Output should be "55" for fib(10) on all platforms
```

---

## Testing Strategy

### Unit Tests (60 tests)

| Component | Tests | File |
|-----------|-------|------|
| Type mapper | 10 | `llvm_type_mapper_spec.spl` (exists) |
| IR builder basics | 10 | `llvm_basic_spec.spl` |
| Control flow | 15 | `llvm_control_flow_spec.spl` |
| Operations | 25 | `llvm_operations_spec.spl` |

### Integration Tests (20 tests)

| Component | Tests | File |
|-----------|-------|------|
| Runtime FFI | 10 | `llvm_runtime_spec.spl` |
| 64-bit targets | 5 | `llvm_target_64bit_spec.spl` |
| 32-bit targets | 5 | `llvm_target_32bit_spec.spl` |

### End-to-End Tests (10 tests)

| Component | Tests | File |
|-----------|-------|------|
| Cross-compilation | 6 | `llvm_cross_compile_spec.spl` |
| Optimization levels | 4 | `llvm_optimization_spec.spl` |

**Total:** 90 tests

### Running Tests

```bash
# All LLVM tests
bin/simple test test/compiler/backend/llvm*.spl

# Specific track
bin/simple test test/compiler/backend/llvm_basic_spec.spl
bin/simple test test/compiler/backend/llvm_runtime_spec.spl
bin/simple test test/compiler/backend/llvm_target_32bit_spec.spl

# End-to-end
bin/simple test test/compiler/backend/llvm_cross_compile_spec.spl
```

---

## Timeline & Milestones

### Week 1: Core IR Translation

| Day | Task | Deliverable |
|-----|------|-------------|
| 1-2 | Function/block translation | Basic IR generation works |
| 3-4 | Memory operations (alloc/load/store) | 10/10 unit tests pass |
| 5 | Testing & refinement | Clean IR output |

**Milestone:** Functions and basic blocks translate correctly

---

### Week 2: Control Flow

| Day | Task | Deliverable |
|-----|------|-------------|
| 1-2 | If/else branches | Conditional branches work |
| 3 | Switch statements | Switch tables generate |
| 4 | Loops & jumps | All terminators work |
| 5 | Testing | 15/15 control flow tests pass |

**Milestone:** All control flow constructs translate correctly

---

### Week 3: Operations & Intrinsics

| Day | Task | Deliverable |
|-----|------|-------------|
| 1-2 | Arithmetic & bitwise ops | All binops work |
| 3 | Comparisons & casts | Type conversions work |
| 4 | Function calls | ABI conventions correct |
| 5 | Testing | 25/25 operation tests pass |

**Milestone:** All MIR operations supported

---

### Week 4: Runtime Integration + 64-bit Targets

| Day | Task | Deliverable |
|-----|------|-------------|
| 1-2 | Runtime bridge implementation | All rt_* functions declared |
| 3 | Linking with runtime | Executables run successfully |
| 4-5 | 64-bit target validation | 15/15 target tests pass |

**Milestone:** Generated code links with runtime and executes

---

### Week 5: 32-bit Targets + Final Integration

| Day | Task | Deliverable |
|-----|------|-------------|
| 1-2 | 32-bit ABI handling | i686/armv7/riscv32 work |
| 3-4 | Cross-compilation testing | All 6 targets validated |
| 5 | End-to-end validation | Feature #97 complete ✅ |

**Milestone:** Phase 3 complete, LLVM backend production-ready

---

## Success Criteria

### Functional Requirements

- ✅ **MIR Translation:** All 50+ MIR opcodes translate to valid LLVM IR
- ✅ **Runtime Integration:** Generated code links with `libsimple_runtime.a`
- ✅ **Cross-Compilation:** Support 6 targets (3 x 64-bit + 3 x 32-bit)
- ✅ **Optimization:** 5 optimization levels (Debug, Size, Speed, Aggressive)
- ✅ **Bare Metal:** Support embedded targets (no OS, no stdlib)

### Performance Requirements

- **Compilation Speed:** < 2x slower than Cranelift (acceptable tradeoff)
- **Runtime Performance:** Match or exceed Cranelift on 64-bit targets
- **Code Size:** Within 10% of Cranelift for equivalent optimization levels

### Test Coverage

- **Unit Tests:** 60/60 passing (IR generation)
- **Integration Tests:** 20/20 passing (runtime + targets)
- **End-to-End Tests:** 10/10 passing (cross-compilation)

**Total:** 90/90 tests passing (100%)

---

## File Reference

### Source Files

| File | Purpose | Lines | Status |
|------|---------|-------|--------|
| `src/compiler/backend/llvm_backend.spl` | Main backend API | 400 | ✅ Basic |
| `src/compiler/backend/llvm_type_mapper.spl` | Type mapping | 305 | ✅ Complete |
| `src/compiler/backend/llvm_target.spl` | Target config | 364 | ✅ Complete |
| `src/compiler/backend/llvm_ir_builder.spl` | IR generation | 1123 → 3100 | 🚧 +2000 LOC |
| `src/compiler/backend/llvm_runtime_bridge.spl` | Runtime FFI | 0 → 500 | ❌ New file |
| `src/compiler/backend/llvm_tools.spl` | LLVM tool wrappers | 150 | ✅ Exists |

**Total Source:** ~4800 lines

### Test Files

| File | Tests | Status |
|------|-------|--------|
| `test/compiler/backend/llvm_type_mapper_spec.spl` | 10 | ✅ Exists |
| `test/compiler/backend/llvm_basic_spec.spl` | 10 | ❌ New |
| `test/compiler/backend/llvm_control_flow_spec.spl` | 15 | ❌ New |
| `test/compiler/backend/llvm_operations_spec.spl` | 25 | ❌ New |
| `test/compiler/backend/llvm_runtime_spec.spl` | 10 | ❌ New |
| `test/compiler/backend/llvm_target_64bit_spec.spl` | 15 | ❌ New |
| `test/compiler/backend/llvm_target_32bit_spec.spl` | 15 | ❌ New |
| `test/compiler/backend/llvm_cross_compile_spec.spl` | 10 | ❌ New |

**Total Tests:** 110 (10 existing + 100 new)

---

## Next Steps

### Immediate Actions

1. **Start Track A Week 1** - Implement core IR translation
2. **Set up test infrastructure** - Create test helper functions
3. **Create milestone tracking** - Use task system to track progress

### Commands

```bash
# Start development
cd /home/ormastes/dev/pub/simple

# Run existing tests
bin/simple test test/compiler/backend/llvm_type_mapper_spec.spl

# Create first new test file
touch test/compiler/backend/llvm_basic_spec.spl

# Monitor progress
bin/simple test test/compiler/backend/llvm*.spl
```

### Task Tracking

Use the task system to track milestones:

```
/task add "Week 1: Core IR Translation (10 tests)"
/task add "Week 2: Control Flow (15 tests)"
/task add "Week 3: Operations (25 tests)"
/task add "Week 4: Runtime Integration (10 tests)"
/task add "Week 5: 32-bit Targets (15 tests)"
```

---

## Resources

### LLVM Documentation

- **LLVM Language Reference:** https://llvm.org/docs/LangRef.html
- **LLVM Target Triples:** https://clang.llvm.org/docs/CrossCompilation.html
- **LLVM Optimization Passes:** https://llvm.org/docs/Passes.html

### Simple Compiler Resources

- **MIR Specification:** `doc/design/mir_specification.md`
- **Backend API:** `src/compiler/backend/backend_api.spl`
- **Runtime FFI:** `src/compiler_seed/runtime.h` (C headers for rt_* functions)

### Related Guides

- **Backend Completeness Guide:** `doc/guide/backend_completeness_next_steps.md`
- **Compiler Architecture:** `doc/guide/compiler_architecture.md`
- **Testing Guide:** `doc/guide/comprehensive_testing.md`

---

## Conclusion

Phase 3 represents the final 80% of LLVM backend implementation. By completing all 3 tracks, we'll unlock:

- **32-bit embedded platforms** (Arduino, ESP32, STM32)
- **Broader platform coverage** (6 architectures vs 3)
- **Production-ready compilation** (full optimization pipeline)
- **Bare-metal support** (kernels, firmware, bootloaders)

The 5-week timeline is aggressive but achievable with focused implementation and comprehensive testing. Each week builds on the previous, with clear milestones and test criteria.

**Feature #97 completion:** End of Week 5 (20% → 100%) ✅
