# Phase 2: Native Binary Compilation - Implementation Guide

## Overview

**Current State:** Native backend generates ELF .o object files with complete machine code
**Goal:** Complete linking pipeline to produce executable binaries from .o files
**Timeline:** 2-3 weeks across 5 sub-phases
**Completion:** Will increase Feature #101 from 70% → 100%

The native backend currently produces valid ELF relocatable object files (.o) with:
- x86_64, AArch64, and RISC-V 64 instruction encoding
- Symbol tables and section headers
- Relocations for external references
- Layout optimization (4KB page alignment)

**Missing:** The linking step to combine .o files into executable binaries.

## Architecture Context

### Current Pipeline (70% Complete)

```
Source → Parser → HIR → MIR → ISel → RegAlloc → Encode → ELF .o
                                                              ↓
                                                         [MISSING]
                                                              ↓
                                                         Executable
```

### Target Pipeline (100% Complete)

```
Source → Parser → HIR → MIR → ISel → RegAlloc → Encode → ELF .o → Linker → Executable
```

### Existing Components

1. **ELF Writer** (`src/compiler/backend/native/elf_writer.spl`):
   - Generates valid ELF64 relocatable object files
   - Supports .text, .data, .rodata, .bss sections
   - Symbol tables (local + global)
   - Relocations: R_X86_64_PC32, R_X86_64_PLT32, R_X86_64_64

2. **Mold Linker Integration** (`src/compiler/linker/mold.spl`):
   - Detects linkers: mold → lld → ld
   - Invokes linker with correct arguments
   - **CURRENT BUG:** Converts ELF bytes → assembly → reassembles (inefficient)

3. **Linker Wrapper** (`src/compiler/linker/linker_wrapper.spl`):
   - High-level API for native linking
   - Platform detection (Linux, macOS, Windows)
   - CRT file discovery

---

## Sub-Phase 2.1: Direct ELF Linking (2-3 days)

### Problem

File: `/home/ormastes/dev/pub/simple/src/compiler/linker/mold.spl` (lines 60-108)

```simple
fn write_elf_object(code: [i64], name: text, output_path: text) -> Result<(), text>:
    # Generate assembly source with .byte directives
    var asm_lines = ".section .text\n"
    asm_lines = asm_lines + ".globl " + name + "\n"
    # ... convert bytes to assembly ...

    # Assemble with GNU as
    val (stdout, stderr, exit_code) = process_run("as", ["--64", "-o", output_path, asm_path])
```

**Inefficiency:** Native backend produces complete ELF .o files, but mold.spl throws away the ELF structure and regenerates it via assembler.

### Solution

#### Step 1: Add Direct Binary Writer

**File:** `src/compiler/linker/linker_wrapper.spl` (add ~50 lines)

```simple
fn write_elf_bytes_to_file(path: text, bytes: [i64]) -> Result<(), text>:
    """Write raw ELF bytes directly to file without assembler.

    Uses file_write_bytes() to write binary data efficiently.
    No intermediate assembly step needed.
    """
    # Convert [i64] byte array to binary file
    val success = rt_file_write_bytes(path, bytes)
    if not success:
        return Err("Failed to write ELF file: {path}")

    # Verify ELF magic number (0x7f 'E' 'L' 'F')
    if bytes.len() >= 4:
        if bytes[0] != 0x7f or bytes[1] != 0x45 or bytes[2] != 0x4c or bytes[3] != 0x46:
            return Err("Invalid ELF magic number in output")

    Ok(())

export write_elf_bytes_to_file
```

#### Step 2: Update Driver to Skip Assembler

**File:** `src/compiler/driver.spl` (modify compile_to_native function, ~497-536)

```simple
me compile_to_native(output: text) -> CompileResult:
    # ... existing code ...

    for name in self.ctx.mir_modules.keys():
        val mir_module = self.ctx.mir_modules[name]
        val compiled = compile_module_with_backend(backend_name, mir_module, is_release)

        val module = compiled.unwrap()
        if module.object_code.?:
            val obj_path = "{output}.{name}.o"

            # NEW: Direct binary write (no assembler)
            match write_elf_bytes_to_file(obj_path, module.object_code.unwrap()):
                case Ok(_):
                    object_files = object_files.push(obj_path)
                case Err(e):
                    return CompileResult.CodegenError("Failed to write {obj_path}: {e}")
```

#### Step 3: Update Mold Backend

**File:** `src/compiler/linker/mold.spl` (lines 328-456, MoldBackend.link method)

Remove assembly generation for native backend objects:

```simple
impl MoldBackend:
    fn link(objects: [ResolvedObject], output: text) -> Result<(), text>:
        # ... existing CRT discovery code ...

        var obj_paths: [text] = []
        for (idx, obj) in objects.enumerate():
            # Check if obj.code is already ELF (from native backend)
            val is_elf = (obj.code.len() >= 4 and
                          obj.code[0] == 0x7f and
                          obj.code[1] == 0x45)

            val obj_path = "{temp_dir}/obj_{idx}.o"

            if is_elf:
                # NEW PATH: Direct binary write
                write_elf_bytes_to_file(obj_path, obj.code)?
            else:
                # OLD PATH: Assembly generation (for non-native backends)
                write_elf_object(obj.code, obj.name, obj_path)?

            obj_paths = obj_paths.push(obj_path)

        # ... existing linker invocation code ...
```

### Testing

**File:** `test/integration/native_link_spec.spl` (new file, ~100 lines)

```simple
use std.spec
use compiler.backend.native.mod.{compile_native}
use compiler.linker.linker_wrapper.{link_to_native, NativeLinkConfig__default, write_elf_bytes_to_file}
use app.io.{file_exists, file_delete, file_read}

describe "Phase 2.1: Direct ELF Linking":
    it "writes ELF bytes without assembler":
        # Generate minimal ELF object
        val elf_bytes = generate_minimal_elf_object()
        val path = "/tmp/test_direct.o"

        val result = write_elf_bytes_to_file(path, elf_bytes)
        expect(result.is_ok()).to_equal(true)
        expect(file_exists(path)).to_equal(true)

        # Verify ELF magic
        val content = file_read(path)
        expect(content[0]).to_equal(0x7f)

        file_delete(path)

    it "links hello world without external symbols":
        # Compile minimal program with no libc calls
        val source = """
        fn main():
            pass  # No-op, just return 0
        """

        # Compile to .o
        val mir = parse_and_lower(source)
        val elf_bytes = compile_native(mir, CodegenTarget.X86_64)

        val obj_path = "/tmp/hello_noext.o"
        write_elf_bytes_to_file(obj_path, elf_bytes)

        # Link (should succeed with no external deps)
        var config = NativeLinkConfig__default()
        val result = link_to_native([obj_path], "/tmp/hello_noext", config)

        expect(result.is_ok()).to_equal(true)
        expect(file_exists("/tmp/hello_noext")).to_equal(true)

        # Cleanup
        file_delete(obj_path)
        file_delete("/tmp/hello_noext")

fn generate_minimal_elf_object() -> [i64]:
    # Minimal ELF with just a 'ret' instruction
    var writer = elf_writer_x86_64()
    val text = new_text_section([0xc3])  # ret
    writer = elf_add_section(writer, text)
    val main_sym = new_func_symbol("main", 1, 0, 1)
    writer = elf_add_symbol(writer, main_sym)
    write_elf64(writer)
```

**Success Criteria:**
- ✅ No `as` (assembler) invocation in logs
- ✅ Direct binary write completes in <1ms
- ✅ Linked binary runs without errors
- ✅ 10x faster linking (no assembly generation overhead)

---

## Sub-Phase 2.2: GOT/PLT Generation (3-4 days) 🔥 CRITICAL

### Background

**GOT (Global Offset Table):** Holds addresses of external symbols (libc functions, global variables)
**PLT (Procedure Linkage Table):** Stubs for dynamic function calls (lazy binding)

Without GOT/PLT, programs cannot call `printf`, `malloc`, or any libc function.

### Current Limitation

File: `src/compiler/backend/native/elf_writer.spl` generates relocations but no GOT/PLT sections:

```simple
# Supports relocations but no GOT/PLT:
# - R_X86_64_PC32 (PC-relative calls to same object)
# - R_X86_64_PLT32 (PC-relative, expects PLT stub)
# - R_X86_64_64 (absolute 64-bit address)
```

When linking with libc, the linker expects:
1. `.got.plt` section with space for symbol addresses
2. `.plt` section with jump stubs
3. `.rela.plt` relocations for dynamic linker

### Implementation

#### Part A: Data Structures

**File:** `src/compiler/backend/native/elf_writer.spl` (add after line 181)

```simple
struct GotPltBuilder:
    """Builder for GOT/PLT sections.

    The Global Offset Table (GOT) holds addresses of external symbols.
    The Procedure Linkage Table (PLT) contains jump stubs for lazy binding.
    """
    got_entries: Dict<text, i64>      # symbol → GOT offset
    plt_stubs: Dict<text, [i64]>      # symbol → PLT bytecode
    dynamic_relocs: [ElfReloc]        # Relocations for dynamic linker

fn new_got_plt_builder() -> GotPltBuilder:
    GotPltBuilder(
        got_entries: {},
        plt_stubs: {},
        dynamic_relocs: []
    )
```

#### Part B: PLT Stub Generation (x86_64)

**File:** `src/compiler/backend/native/elf_writer.spl` (add ~150 lines)

```simple
fn build_got_plt(extern_symbols: [text]) -> GotPltBuilder:
    """Generate GOT entries and PLT stubs for external symbols.

    For each symbol 'foo':
    1. Allocate 8-byte GOT entry
    2. Generate 16-byte PLT stub:
       - jmpq *GOT[offset](%rip)  (6 bytes)
       - pushq $index             (5 bytes)
       - jmpq PLT[0]              (5 bytes)
    3. Add R_X86_64_JUMP_SLOT relocation
    """
    var builder = new_got_plt_builder()
    var got_offset = 24  # Reserve first 3 entries for dynamic linker
    var plt_index = 1    # PLT[0] is special resolver stub

    # PLT[0]: Dynamic linker resolver (16 bytes)
    val plt0_stub = generate_plt0_stub()
    builder.plt_stubs["__plt0"] = plt0_stub

    for symbol in extern_symbols:
        # Allocate GOT entry
        builder.got_entries[symbol] = got_offset

        # Generate PLT stub for this symbol
        val stub = generate_plt_stub_x86_64(plt_index, got_offset)
        builder.plt_stubs[symbol] = stub

        # Add relocation for dynamic linker
        val reloc = ElfReloc(
            offset: got_offset,
            reloc_type: ElfRelocType.X86_64_JumpSlot,  # NEW enum value
            symbol_index: find_symbol_index(symbol),
            addend: 0
        )
        builder.dynamic_relocs.push(reloc)

        got_offset = got_offset + 8   # 8 bytes per entry
        plt_index = plt_index + 1

    builder

fn generate_plt0_stub() -> [i64]:
    """PLT[0]: Dynamic linker resolver stub.

    Assembly equivalent:
        pushq GOT[1](%rip)      # Push link_map pointer
        jmpq *GOT[2](%rip)      # Jump to resolver function
        nop
    """
    [
        0xff, 0x35, 0x00, 0x00, 0x00, 0x00,  # pushq GOT[1](%rip)
        0xff, 0x25, 0x00, 0x00, 0x00, 0x00,  # jmpq *GOT[2](%rip)
        0x90, 0x90, 0x90, 0x90               # nop padding (4 bytes)
    ]

fn generate_plt_stub_x86_64(index: i64, got_offset: i64) -> [i64]:
    """Generate PLT stub for a single symbol.

    Assembly equivalent:
        jmpq *GOT[offset](%rip)   # Jump to resolved address
        pushq $index              # Push symbol index
        jmpq PLT[0]               # Jump to resolver

    Size: 16 bytes
    """
    # Calculate RIP-relative offset to GOT entry
    # RIP points to next instruction, so offset = got_offset - (current_plt_offset + 6)
    val plt_offset = 16 + (index * 16)  # PLT[0] is 16 bytes, then 16 per stub
    val rip_offset = got_offset - (plt_offset + 6)

    # Encode jmpq *GOT[offset](%rip)
    var stub: [i64] = [0xff, 0x25]  # jmpq *disp32(%rip)
    stub = stub + encode_i32_le(rip_offset)

    # Encode pushq $index
    stub = stub + [0x68]
    stub = stub + encode_i32_le(index)

    # Encode jmpq PLT[0] (relative to current position)
    val plt0_offset = -(plt_offset + 11)  # 11 = size of jmpq + pushq
    stub = stub + [0xe9]
    stub = stub + encode_i32_le(plt0_offset)

    stub

fn encode_i32_le(value: i64) -> [i64]:
    """Encode signed 32-bit integer as little-endian bytes."""
    val b0 = value % 256
    val b1 = (value / 256) % 256
    val b2 = (value / 65536) % 256
    val b3 = (value / 16777216) % 256
    [b0, b1, b2, b3]
```

#### Part C: Add New Relocation Types

**File:** `src/compiler/backend/native/elf_writer.spl` (lines 117-153)

```simple
enum ElfRelocType:
    # x86_64
    X86_64_None
    X86_64_64
    X86_64_PC32
    X86_64_PLT32
    X86_64_32S
    X86_64_JumpSlot      # NEW: R_X86_64_JUMP_SLOT (for PLT)
    X86_64_Glob_Dat      # NEW: R_X86_64_GLOB_DAT (for GOT data)
    X86_64_GotPcRel      # NEW: R_X86_64_GOTPCREL (GOT-relative)
    # ... existing AArch64/RISC-V types ...

impl ElfRelocType:
    fn to_elf_value() -> i64:
        match self:
            # ... existing cases ...
            case X86_64_JumpSlot: 7     # R_X86_64_JUMP_SLOT
            case X86_64_Glob_Dat: 6     # R_X86_64_GLOB_DAT
            case X86_64_GotPcRel: 9     # R_X86_64_GOTPCREL
```

#### Part D: Integrate GOT/PLT into ELF Emission

**File:** `src/compiler/backend/native/elf_writer.spl` (modify write_elf64, ~456-753)

```simple
fn write_elf64(writer: ElfWriter) -> [i64]:
    # ... existing symbol table building ...

    # NEW: Collect extern symbols
    var extern_syms: [text] = []
    for sym in writer.symbols:
        if sym.section_index == SHN_UNDEF and sym.sym_bind == ElfSymbolBind.Global:
            extern_syms.push(sym.name)

    # NEW: Build GOT/PLT
    var got_plt = build_got_plt(extern_syms)
    var has_got_plt = extern_syms.len() > 0

    # NEW: Generate .got.plt section
    var got_plt_data: [i64] = []
    if has_got_plt:
        # GOT[0]: address of _DYNAMIC (set by linker)
        got_plt_data = got_plt_data + [0, 0, 0, 0, 0, 0, 0, 0]
        # GOT[1]: link_map pointer (set by linker)
        got_plt_data = got_plt_data + [0, 0, 0, 0, 0, 0, 0, 0]
        # GOT[2]: dl_runtime_resolve address (set by linker)
        got_plt_data = got_plt_data + [0, 0, 0, 0, 0, 0, 0, 0]
        # GOT[3..N]: Per-symbol entries (initialized to PLT stub by linker)
        for sym in extern_syms:
            got_plt_data = got_plt_data + [0, 0, 0, 0, 0, 0, 0, 0]

    # NEW: Generate .plt section
    var plt_data: [i64] = []
    if has_got_plt:
        for (name, stub) in got_plt.plt_stubs.items():
            plt_data = plt_data + stub

    # ... existing section offset calculation ...

    # NEW: Add .got.plt section header
    if has_got_plt:
        val got_plt_shndx = next_shndx
        next_shndx = next_shndx + 1
        val got_plt_name_off = strtab_get_offset(shstrtab, ".got.plt")
        buf = write_shdr(buf, got_plt_name_off, SHT_PROGBITS,
                        SHF_ALLOC + SHF_WRITE,
                        0, got_plt_offset, got_plt_data.len(), 0, 0, 8, 8)

    # NEW: Add .plt section header
    if has_got_plt:
        val plt_shndx = next_shndx
        next_shndx = next_shndx + 1
        val plt_name_off = strtab_get_offset(shstrtab, ".plt")
        buf = write_shdr(buf, plt_name_off, SHT_PROGBITS,
                        SHF_ALLOC + SHF_EXECINSTR,
                        0, plt_offset, plt_data.len(), 0, 0, 16, 16)

    # NEW: Add .rela.plt section header
    if has_got_plt:
        val rela_plt_name_off = strtab_get_offset(shstrtab, ".rela.plt")
        buf = write_shdr(buf, rela_plt_name_off, SHT_RELA, SHF_INFO_LINK,
                        0, rela_plt_offset, rela_plt_size,
                        symtab_shndx, got_plt_shndx, 8, ELF64_RELA_SIZE)

    buf.bytes
```

#### Part E: Update Instruction Selection for GOT Access

**File:** `src/compiler/backend/native/isel_x86_64.spl` (add to MachInst enum)

```simple
enum MachInst:
    # ... existing variants ...
    LoadGot(reg: Register, symbol: text)      # NEW: Load from GOT
    CallPlt(symbol: text)                     # NEW: Call via PLT

fn isel_call_extern(func_name: text) -> MachInst:
    """Generate call to external function via PLT.

    Instead of direct call, use PLT stub:
        call func@PLT
    """
    MachInst.CallPlt(symbol: func_name)

fn isel_global_load(symbol: text) -> MachInst:
    """Load global variable via GOT.

    PIE-safe access pattern:
        mov rax, [rip + symbol@GOTPCREL]
    """
    MachInst.LoadGot(reg: RAX, symbol: symbol)
```

#### Part F: Encode GOT/PLT Instructions

**File:** `src/compiler/backend/native/encode_x86_64.spl` (add encoders)

```simple
fn encode_call_plt(inst: MachInst) -> ([i64], [Reloc]):
    """Encode call to PLT stub.

    Assembly: call symbol@PLT
    Opcode: e8 00 00 00 00 (relative call with R_X86_64_PLT32 relocation)
    """
    val code = [0xe8, 0x00, 0x00, 0x00, 0x00]  # call rel32
    val reloc = Reloc(
        offset: 1,  # After opcode byte
        reloc_type: ElfRelocType.X86_64_PLT32,
        symbol: inst.symbol,
        addend: -4  # Adjust for instruction size
    )
    (code, [reloc])

fn encode_load_got(inst: MachInst) -> ([i64], [Reloc]):
    """Encode GOT-relative load.

    Assembly: mov rax, [rip + symbol@GOTPCREL]
    Opcode: 48 8b 05 00 00 00 00 (REX.W mov r/m64)
    """
    val code = [0x48, 0x8b, 0x05, 0x00, 0x00, 0x00, 0x00]
    val reloc = Reloc(
        offset: 3,  # After opcode bytes
        reloc_type: ElfRelocType.X86_64_GotPcRel,
        symbol: inst.symbol,
        addend: -4
    )
    (code, [reloc])
```

### Testing

**File:** `test/integration/native_link_spec.spl` (add to existing file)

```simple
describe "Phase 2.2: GOT/PLT Generation":
    it "generates GOT entries for extern symbols":
        val extern_syms = ["printf", "malloc"]
        val builder = build_got_plt(extern_syms)

        expect(builder.got_entries.len()).to_equal(2)
        expect(builder.got_entries.contains_key("printf")).to_equal(true)
        expect(builder.got_entries.contains_key("malloc")).to_equal(true)

    it "generates PLT stubs with correct size":
        val extern_syms = ["printf"]
        val builder = build_got_plt(extern_syms)

        # PLT[0] + one stub = 32 bytes total
        expect(builder.plt_stubs.len()).to_equal(2)  # __plt0 + printf
        val printf_stub = builder.plt_stubs["printf"]
        expect(printf_stub.len()).to_equal(16)  # Standard PLT stub size

    it "calls libc printf successfully":
        val source = """
        extern fn printf(fmt: text) -> i64

        fn main():
            printf("Hello from native backend!\\n")
        """

        val mir = parse_and_lower(source)
        val elf_bytes = compile_native(mir, CodegenTarget.X86_64)

        val obj_path = "/tmp/test_printf.o"
        write_elf_bytes_to_file(obj_path, elf_bytes)

        # Link with libc
        var config = NativeLinkConfig__default()
        config.libraries = ["c"]
        val result = link_to_native([obj_path], "/tmp/test_printf", config)

        expect(result.is_ok()).to_equal(true)

        # Execute and verify output
        val output = shell_output("/tmp/test_printf")
        expect(output).to_contain("Hello from native backend!")

        # Cleanup
        file_delete(obj_path)
        file_delete("/tmp/test_printf")
```

**Success Criteria:**
- ✅ Generates .got.plt, .plt, .rela.plt sections
- ✅ PLT stubs are 16 bytes (standard x86_64 size)
- ✅ Linked binary calls libc functions correctly
- ✅ Dynamic linker resolves symbols at runtime

---

## Sub-Phase 2.3: PIC/PIE Support (2-3 days)

### Goal

**PIC** (Position-Independent Code): Code that works at any memory address
**PIE** (Position-Independent Executable): Enables ASLR (Address Space Layout Randomization) security

Modern Linux systems require PIE for security. Without it, executables fail to run with:
```
bash: ./program: cannot execute binary file: Exec format error
```

### Current Limitation

File: `src/compiler/backend/native/isel_x86_64.spl` generates non-PIC code:

```simple
# Absolute addressing (NOT position-independent):
fn isel_load_global(symbol: text) -> MachInst:
    # mov rax, [symbol]  <- WRONG: absolute address
    MachInst.LoadAbs(reg: RAX, symbol: symbol)
```

### Implementation

#### Part A: GOT-Relative Loads

**File:** `src/compiler/backend/native/isel_x86_64.spl` (modify existing functions)

```simple
fn isel_load_global(symbol: text) -> MachInst:
    """Load global variable using GOT-relative addressing.

    Non-PIC (wrong):
        mov rax, [symbol]          # Absolute address

    PIC (correct):
        mov rax, [rip + symbol@GOTPCREL]  # GOT-relative
    """
    MachInst.LoadGot(reg: RAX, symbol: symbol)  # Already added in 2.2

fn isel_store_global(symbol: text, value_reg: Register) -> MachInst:
    """Store to global variable via GOT.

    Two-step process:
    1. Load address from GOT into temp register
    2. Store value through pointer
    """
    # Step 1: lea rax, [rip + symbol@GOTPCREL]
    # Step 2: mov [rax], value_reg
    MachInst.StoreGot(symbol: symbol, value_reg: value_reg)
```

#### Part B: Function Calls via PLT

Already implemented in 2.2 (CallPlt instruction).

#### Part C: Update Linker Flags

**File:** `src/compiler/linker/linker_wrapper.spl` (lines 82-94, modify link_to_native)

```simple
fn link_to_native(object_files: [text], output: text, config: NativeLinkConfig) -> Result:
    # ... existing code ...

    # Enable PIE by default (security best practice)
    if config.pie:
        args.push("-pie")
        args.push("--dynamic-linker")  # Require dynamic linker for PIE
        val dyld = find_dynamic_linker()
        if dyld != "":
            args.push(dyld)
        else:
            return Err("PIE requires dynamic linker, but none found")
```

#### Part D: CRT File Selection

**File:** `src/compiler/linker/mold.spl` (lines 138-180, modify mold_find_crt_files)

```simple
fn mold_find_crt_files(pie: bool, verbose: bool) -> MoldCrtFiles:
    """Discover C Runtime (CRT) files for linking.

    PIE vs non-PIE use different CRT files:
    - Non-PIE: crt1.o, crtbegin.o, crtend.o
    - PIE:     Scrt1.o, crtbeginS.o, crtendS.o
    """
    var crt1_name = if pie: "Scrt1.o" else: "crt1.o"
    var crtbegin_name = if pie: "crtbeginS.o" else: "crtbegin.o"
    var crtend_name = if pie: "crtendS.o" else: "crtend.o"

    val crt1 = mold_cc_print_file(crt1_name)
    val crti = mold_cc_print_file("crti.o")
    val crtn = mold_cc_print_file("crtn.o")
    val crtbegin = mold_cc_print_file(crtbegin_name)
    val crtend = mold_cc_print_file(crtend_name)

    # ... rest of function ...
```

### Testing

**File:** `test/integration/native_link_spec.spl` (add section)

```simple
describe "Phase 2.3: PIC/PIE Support":
    it "produces PIE executables":
        val source = """
        fn main():
            print "PIE executable"
        """

        val obj = compile_source_to_object(source)

        var config = NativeLinkConfig__default()
        config.pie = true
        link_to_native([obj], "/tmp/test_pie", config)

        # Verify PIE flag in ELF header
        val elf_type = read_elf_type("/tmp/test_pie")
        expect(elf_type).to_equal(3)  # ET_DYN (PIE executables are type 3)

        file_delete("/tmp/test_pie")

    it "runs with ASLR enabled":
        val binary = compile_and_link_pie("fn main(): pass")

        # Run multiple times and collect load addresses
        var addresses: [i64] = []
        for i in 0..5:
            val addr = get_process_load_address(binary)
            addresses.push(addr)

        # ASLR should randomize base address
        expect(addresses.all_different()).to_equal(true)

    it "accesses globals via GOT":
        val source = """
        var global_counter = 42

        fn main():
            print "{global_counter}"
        """

        val mir = parse_and_lower(source)
        val mach = isel_module(mir)

        # Verify GOT-relative load instruction
        val load_inst = find_instruction(mach, "global_counter")
        expect(load_inst.is_load_got()).to_equal(true)

fn read_elf_type(path: text) -> i64:
    """Read e_type field from ELF header (bytes 16-17)."""
    val bytes = file_read_bytes(path)
    bytes[16] + (bytes[17] * 256)

fn get_process_load_address(binary_path: text) -> i64:
    """Extract base address from /proc/self/maps after launching process."""
    # Launch process in background
    # Read /proc/{pid}/maps
    # Parse first address
    # Return address as i64
    # (Implementation details omitted for brevity)
    0x555555554000  # Example ASLR address
```

**Success Criteria:**
- ✅ Executables have ET_DYN type (PIE)
- ✅ `readelf -h` shows PIE flags
- ✅ ASLR works (different base addresses on each run)
- ✅ All global accesses use GOT-relative addressing

---

## Sub-Phase 2.4: Multi-Object Linking (2-3 days)

### Goal

Link multiple .o files with cross-module function calls and symbol resolution.

### Current Limitation

Driver only handles single-module compilation. No cross-module symbol resolution.

### Implementation

#### Part A: Symbol Table Builder

**File:** `src/compiler/linker/object_resolver.spl` (new file, ~200 lines)

```simple
# Object File Symbol Resolution
#
# Resolves symbols across multiple object files before linking.
# Detects duplicate definitions and undefined references.

struct ObjectFile:
    path: text
    symbols: [SymbolDef]
    undefined_refs: [text]

struct SymbolDef:
    name: text
    binding: SymbolBinding  # Local or Global
    section: text           # .text, .data, .rodata, .bss
    offset: i64
    size: i64

enum SymbolBinding:
    Local
    Global

struct ResolvedLinkage:
    """Result of symbol resolution across object files."""
    symbol_table: Dict<text, SymbolDef>
    undefined_symbols: [text]
    duplicate_symbols: [text]
    success: bool

fn resolve_symbols(objects: [ObjectFile]) -> ResolvedLinkage:
    """Build global symbol table and check for errors.

    Algorithm:
    1. Collect all global symbols from all objects
    2. Detect duplicates (multiple definitions)
    3. Find undefined references (no definition)
    4. Return unified symbol table
    """
    var symbol_table: Dict<text, SymbolDef> = {}
    var undefined: [text] = []
    var duplicates: [text] = []

    # Phase 1: Build global symbol table
    for obj in objects:
        for sym in obj.symbols:
            if sym.binding == SymbolBinding.Global:
                if symbol_table.contains_key(sym.name):
                    # Duplicate definition!
                    duplicates.push(sym.name)
                else:
                    symbol_table[sym.name] = sym

    # Phase 2: Check for undefined references
    for obj in objects:
        for ref in obj.undefined_refs:
            if not symbol_table.contains_key(ref):
                # Undefined symbol!
                undefined.push(ref)

    val success = (duplicates.len() == 0 and undefined.len() == 0)

    ResolvedLinkage(
        symbol_table: symbol_table,
        undefined_symbols: undefined,
        duplicate_symbols: duplicates,
        success: success
    )

fn parse_object_symbols(elf_bytes: [i64]) -> ObjectFile:
    """Extract symbols from ELF object file.

    Parses:
    - .symtab section (symbol table)
    - .strtab section (string table)
    - Symbol bindings (local/global)
    - Section assignments
    """
    var symbols: [SymbolDef] = []
    var undefined: [text] = []

    # Parse ELF sections
    # Extract symbol table entries
    # Build SymbolDef structs
    # (Detailed ELF parsing omitted for brevity)

    ObjectFile(
        path: "",
        symbols: symbols,
        undefined_refs: undefined
    )

export ObjectFile, SymbolDef, SymbolBinding, ResolvedLinkage
export resolve_symbols, parse_object_symbols
```

#### Part B: Multi-Module Compilation

**File:** `src/compiler/driver.spl` (modify compile_to_native, line 497)

```simple
me compile_to_native(output: text) -> CompileResult:
    val log = self.ctx.logger
    val backend_name = self.ctx.options.backend
    val is_release = self.ctx.options.release

    log.debug("AOT native: compiling {self.ctx.mir_modules.keys().len()} modules")

    # Compile all modules to object files
    var object_files: [text] = []
    var object_data: [ObjectFile] = []

    for name in self.ctx.mir_modules.keys():
        log.trace("compiling module: {name}")
        val mir_module = self.ctx.mir_modules[name]
        val compiled = compile_module_with_backend(backend_name, mir_module, is_release)

        if compiled.is_err():
            val err = compiled.unwrap_err()
            return CompileResult.CodegenError("AOT compile error in {name}: {err.to_text()}")

        val module = compiled.unwrap()
        if module.object_code.?:
            val obj_path = "{output}.{name}.o"
            write_elf_bytes_to_file(obj_path, module.object_code.unwrap())
            object_files.push(obj_path)

            # Parse symbols for resolution
            val obj_info = parse_object_symbols(module.object_code.unwrap())
            object_data.push(obj_info)

    # NEW: Symbol resolution across all modules
    val linkage = resolve_symbols(object_data)
    if not linkage.success:
        # Report errors
        for dup in linkage.duplicate_symbols:
            log.error("Duplicate symbol: {dup}")
        for undef in linkage.undefined_symbols:
            log.error("Undefined symbol: {undef}")
        return CompileResult.CodegenError("Symbol resolution failed")

    log.debug("Symbol resolution: {linkage.symbol_table.keys().len()} symbols")

    # Link all objects
    var link_config = NativeLinkConfig__default()
    link_config.debug = self.ctx.options.debug_info
    link_config.verbose = self.ctx.options.verbose

    match link_to_native(object_files, output, link_config):
        case Ok(_):
            log.info("Native executable: {output}")
            CompileResult.Success(output)
        case Err(e):
            CompileResult.CodegenError("Linking failed: {e}")
```

### Testing

**File:** `test/integration/native_link_spec.spl` (add section)

```simple
describe "Phase 2.4: Multi-Object Linking":
    it "links two modules with cross calls":
        # Module 1: Library
        val lib_source = """
        fn add(a: i64, b: i64) -> i64:
            a + b
        """

        # Module 2: Main
        val main_source = """
        extern fn add(a: i64, b: i64) -> i64

        fn main():
            val result = add(10, 20)
            print "{result}"
        """

        # Compile separately
        val lib_obj = compile_source_to_object(lib_source, "lib")
        val main_obj = compile_source_to_object(main_source, "main")

        # Link together
        val result = link_to_native([lib_obj, main_obj], "/tmp/test_multi",
                                    NativeLinkConfig__default())

        expect(result.is_ok()).to_equal(true)

        # Run and verify
        val output = shell_output("/tmp/test_multi")
        expect(output.trim()).to_equal("30")

        # Cleanup
        file_delete(lib_obj)
        file_delete(main_obj)
        file_delete("/tmp/test_multi")

    it "detects duplicate symbol definitions":
        # Both modules define 'foo'
        val mod1 = compile_source_to_object("fn foo(): pass", "mod1")
        val mod2 = compile_source_to_object("fn foo(): pass", "mod2")

        val obj1 = parse_object_symbols(read_elf_bytes(mod1))
        val obj2 = parse_object_symbols(read_elf_bytes(mod2))

        val linkage = resolve_symbols([obj1, obj2])

        expect(linkage.success).to_equal(false)
        expect(linkage.duplicate_symbols).to_contain("foo")

    it "detects undefined symbols":
        val source = """
        extern fn missing_function() -> i64

        fn main():
            val x = missing_function()
        """

        val obj = compile_source_to_object(source, "main")
        val obj_info = parse_object_symbols(read_elf_bytes(obj))

        val linkage = resolve_symbols([obj_info])

        expect(linkage.success).to_equal(false)
        expect(linkage.undefined_symbols).to_contain("missing_function")
```

**Success Criteria:**
- ✅ Links 2+ object files successfully
- ✅ Cross-module function calls work
- ✅ Detects duplicate symbols with clear errors
- ✅ Detects undefined symbols with clear errors

---

## Sub-Phase 2.5: Testing & Validation (2-3 days)

### Goal

Comprehensive test coverage and benchmark validation for Phase 2.

### Test Categories

#### A. Functional Tests

**File:** `test/integration/native_link_spec.spl` (complete file)

Already added sections:
- 2.1: Direct ELF Linking
- 2.2: GOT/PLT Generation
- 2.3: PIC/PIE Support
- 2.4: Multi-Object Linking

Additional tests:

```simple
describe "Phase 2.5: Edge Cases":
    it "handles empty main function":
        val result = compile_and_link("fn main(): pass")
        expect(result.is_ok()).to_equal(true)

    it "handles large number of extern symbols":
        var source = "extern fn func0() -> i64\n"
        for i in 1..100:
            source = source + "extern fn func{i}() -> i64\n"
        source = source + "fn main(): pass"

        val obj = compile_source_to_object(source, "many_externs")
        val obj_info = parse_object_symbols(read_elf_bytes(obj))

        expect(obj_info.undefined_refs.len()).to_equal(100)

    it "preserves debug symbols when requested":
        var config = NativeLinkConfig__default()
        config.debug = true

        val obj = compile_source_to_object("fn main(): pass", "debug_test")
        val result = link_to_native([obj], "/tmp/debug_test", config)

        # Verify debug sections exist
        val has_debug = check_elf_has_debug_info("/tmp/debug_test")
        expect(has_debug).to_equal(true)

fn check_elf_has_debug_info(path: text) -> bool:
    """Check if ELF file has .debug_* sections."""
    val output = shell_output("readelf -S {path}")
    output.contains(".debug_info") or output.contains(".debug_line")
```

#### B. Performance Benchmarks

**File:** `benchmark/native_startup_spec.spl` (new file, ~150 lines)

```simple
# Native Backend Startup Performance Benchmarks
#
# Validates that Phase 2 achieves the 32KB startup optimization goal.

use std.spec
use std.time.{now_ns}
use app.io.{shell_output}

describe "Native Startup Benchmarks":
    context "code size":
        it "startup code fits in 32KB (8 pages)":
            val binary = compile_minimal_executable()

            # Parse .text section size
            val text_size = get_elf_section_size(binary, ".text")

            # Should fit in 8 * 4KB pages
            expect(text_size).to_be_less_than(32768)

        it "PLT overhead is reasonable":
            # Compile with 10 libc calls
            val source = """
            extern fn printf(fmt: text) -> i64

            fn main():
                for i in 0..10:
                    printf("Line {i}\\n")
            """

            val binary = compile_and_link_pie(source)
            val plt_size = get_elf_section_size(binary, ".plt")

            # PLT[0] = 16 bytes, each stub = 16 bytes
            # Expected: 16 + (10 * 16) = 176 bytes
            expect(plt_size).to_equal(176)

    context "runtime performance":
        it "startup time under 10ms":
            val binary = compile_minimal_executable()

            var times: [i64] = []
            for i in 0..10:
                val start = now_ns()
                shell_output(binary)
                val elapsed = now_ns() - start
                times.push(elapsed)

            val avg_ns = times.sum() / times.len()
            val avg_ms = avg_ns / 1_000_000

            expect(avg_ms).to_be_less_than(10)

        it "linking time under 100ms":
            val objects = generate_10_object_files()

            val start = now_ns()
            link_to_native(objects, "/tmp/bench_link", NativeLinkConfig__default())
            val elapsed_ns = now_ns() - start

            val elapsed_ms = elapsed_ns / 1_000_000
            expect(elapsed_ms).to_be_less_than(100)

fn get_elf_section_size(binary: text, section_name: text) -> i64:
    """Get size of ELF section in bytes using readelf."""
    val output = shell_output("readelf -S {binary} | grep {section_name}")
    # Parse size from readelf output
    # Format: [Nr] Name  Type  Addr  Off  Size  ...
    parse_size_from_readelf(output)

fn compile_minimal_executable() -> text:
    """Compile smallest possible executable."""
    val source = "fn main(): pass"
    val obj = compile_source_to_object(source, "minimal")
    val binary = "/tmp/minimal_exec"
    link_to_native([obj], binary, NativeLinkConfig__default())
    binary
```

#### C. Integration Tests

**File:** `test/integration/native_backend_e2e_spec.spl` (update existing)

```simple
describe "Phase 2 Complete - End-to-End":
    it "compiles stdlib math module":
        # Test complex real-world code
        val source = file_read("src/lib/math.spl")
        val obj = compile_source_to_object(source, "math")

        expect(file_exists(obj)).to_equal(true)

        # Should have multiple symbols (sin, cos, sqrt, etc.)
        val obj_info = parse_object_symbols(read_elf_bytes(obj))
        expect(obj_info.symbols.len()).to_be_greater_than(10)

    it "links with pthread library":
        val source = """
        extern fn pthread_create(thread: i64, attr: i64, fn: i64, arg: i64) -> i64

        fn thread_func(arg: i64) -> i64:
            0

        fn main():
            pthread_create(0, 0, 0, 0)
        """

        var config = NativeLinkConfig__default()
        config.libraries = ["pthread"]

        val obj = compile_source_to_object(source, "pthread_test")
        val result = link_to_native([obj], "/tmp/pthread_test", config)

        expect(result.is_ok()).to_equal(true)

    it "produces stripped binary":
        var config = NativeLinkConfig__default()
        config.debug = false

        val obj = compile_source_to_object("fn main(): pass", "strip_test")
        link_to_native([obj], "/tmp/strip_test", config)

        # Check that debug sections are absent
        val has_debug = check_elf_has_debug_info("/tmp/strip_test")
        expect(has_debug).to_equal(false)
```

### Validation Checklist

**Run all tests:**

```bash
# Unit tests (object format, symbol resolution)
bin/simple test test/unit/compiler/backend/native_backend_spec.spl

# Integration tests (full pipeline)
bin/simple test test/integration/native_link_spec.spl
bin/simple test test/integration/native_backend_e2e_spec.spl

# Benchmarks (performance validation)
bin/simple test benchmark/native_startup_spec.spl
```

**Manual verification:**

```bash
# Compile hello world
echo 'fn main(): print "Hello"' > /tmp/hello.spl
bin/simple compile /tmp/hello.spl -o /tmp/hello --backend=native

# Verify ELF structure
readelf -h /tmp/hello  # Should show ET_DYN (PIE)
readelf -S /tmp/hello  # Should have .got.plt, .plt sections
readelf -d /tmp/hello  # Should show dynamic dependencies

# Run it
/tmp/hello  # Should print "Hello"

# Check ASLR
for i in {1..5}; do
    gdb -batch -ex 'info proc mappings' /tmp/hello | head -1
done
# Should show different base addresses
```

**Success Criteria:**
- ✅ All integration tests pass (100%)
- ✅ Startup code < 32KB
- ✅ PLT overhead matches calculation
- ✅ Linking time < 100ms
- ✅ Runtime overhead < 5% vs GCC

---

## Key Files Reference

| File | Purpose | Lines | Changes |
|------|---------|-------|---------|
| `src/compiler/linker/linker_wrapper.spl` | Direct ELF writing | +50 | Sub-phase 2.1 |
| `src/compiler/driver.spl` | Skip assembler, multi-module | ~100 | Sub-phases 2.1, 2.4 |
| `src/compiler/linker/mold.spl` | ELF detection | ~50 | Sub-phase 2.1 |
| `src/compiler/backend/native/elf_writer.spl` | GOT/PLT generation | +300 | Sub-phase 2.2 |
| `src/compiler/backend/native/isel_x86_64.spl` | GOT-relative ISel | +100 | Sub-phases 2.2, 2.3 |
| `src/compiler/backend/native/encode_x86_64.spl` | GOT/PLT encoding | +80 | Sub-phases 2.2, 2.3 |
| `src/compiler/linker/object_resolver.spl` | Symbol resolution | +200 | Sub-phase 2.4 |
| `test/integration/native_link_spec.spl` | Integration tests | +300 | All sub-phases |
| `benchmark/native_startup_spec.spl` | Performance tests | +150 | Sub-phase 2.5 |

**Total:** ~1,330 lines

---

## Timeline

| Week | Sub-phases | Deliverables |
|------|-----------|--------------|
| 1 | 2.1, 2.2 start | Direct linking, GOT/PLT design |
| 2 | 2.2 complete, 2.3 | Full GOT/PLT, PIC support |
| 3 | 2.4, 2.5 | Multi-object, tests, validation |

---

## Success Metrics

### Functional Completeness

- ✅ Link static executables (no libc)
- ✅ Call libc functions (printf, malloc)
- ✅ Support PIE executables (ASLR)
- ✅ Link multiple .o files
- ✅ Cross-module function calls
- ✅ Detect symbol errors (duplicate, undefined)

### Performance Targets

- ✅ Startup code < 32KB (fits in 8 pages)
- ✅ Linking time < 100ms (10+ objects)
- ✅ Runtime overhead < 5% vs GCC

### Feature Completion

- ✅ Feature #101: 70% → 100% (Native Backend)
- ✅ Close tracking issue: "Phase 2 - Native Binary Linking"
- ✅ Update documentation: `doc/feature/feature.md`

---

## Common Issues & Solutions

### Issue 1: Linker Not Found

**Error:**
```
No linker found. Please install mold, lld, or ensure ld is in PATH.
```

**Solution:**
```bash
# Install mold (recommended)
sudo apt install mold

# Or install lld
sudo apt install lld

# Or use system ld (slower)
# Already installed on all Unix systems
```

### Issue 2: CRT Files Not Found

**Error:**
```
CRT files not found, falling back to cc
```

**Solution:**
```bash
# Install development files
sudo apt install build-essential

# Verify CRT files exist
cc -print-file-name=Scrt1.o
cc -print-file-name=crtbegin.o
```

### Issue 3: Undefined Symbol at Runtime

**Error:**
```
./program: symbol lookup error: ./program: undefined symbol: printf
```

**Diagnosis:**
- Missing library in link config
- GOT/PLT not generated correctly

**Solution:**
```bash
# Check which symbols are undefined
readelf -r program | grep JUMP_SLOT

# Verify dynamic dependencies
ldd program

# Add missing library to config.libraries
config.libraries = ["c"]  # For libc functions
```

### Issue 4: Segmentation Fault on Startup

**Error:**
```
Segmentation fault (core dumped)
```

**Diagnosis:**
- Non-PIE executable on PIE-enforced system
- Incorrect PLT stub encoding

**Solution:**
```bash
# Check if PIE is enabled
readelf -h program | grep Type
# Should show: Type: DYN (Position-Independent Executable file)

# Verify PLT section
readelf -S program | grep plt

# Re-link with PIE enabled
config.pie = true
```

---

## Next Steps After Phase 2

Once Phase 2 is complete (Feature #101 at 100%), the next priorities are:

### Phase 3: LLVM Backend Integration
- MIR → LLVM IR translation
- Use LLVM's optimizations
- Cross-compilation support

### Phase 4: Windows Support
- PE/COFF file format
- MSVC runtime integration
- Windows syscalls

### Phase 5: macOS Support
- Mach-O file format
- System framework linking
- Apple Silicon support

---

## References

### ELF Specification
- [ELF Format (PDF)](https://refspecs.linuxfoundation.org/elf/elf.pdf)
- [x86_64 ABI](https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf)
- [PLT/GOT Internals](https://www.technovelty.org/linux/plt-and-got-the-key-to-code-sharing-and-dynamic-libraries.html)

### Linker Documentation
- [mold Linker](https://github.com/rui314/mold)
- [LLD (LLVM Linker)](https://lld.llvm.org/)
- [GNU ld Manual](https://sourceware.org/binutils/docs/ld/)

### Position-Independent Code
- [PIE/PIC Overview](https://eli.thegreenplace.net/2011/11/03/position-independent-code-pic-in-shared-libraries)
- [ASLR (Wikipedia)](https://en.wikipedia.org/wiki/Address_space_layout_randomization)

### Simple Compiler Architecture
- `doc/architecture/unified_backend_architecture.md`
- `doc/guide/backend_shared_components_integration.md`
- `doc/design/backend_production_plan.md`

---

**Last Updated:** 2026-02-13
**Status:** Implementation guide complete, ready for development
**Estimated Completion:** 3 weeks from start date
