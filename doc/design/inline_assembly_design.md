# Inline Assembly Design for Simple Language

**Status:** Draft
**Date:** 2026-02-05
**Author:** Claude

---

## 1. Executive Summary

This document designs the `asm{}` block syntax for Simple, enabling inline assembly with proper platform specification. Key innovations:

1. **Platform specification at multiple levels** (file, module, attribute)
2. **Simple-style symbolic operands** (not GCC's cryptic constraint letters)
3. **Integration with Simple's type system**
4. **Compile-time architecture validation**

---

## 2. Research Summary

### Approaches Analyzed

| Language | Approach | Pros | Cons |
|----------|----------|------|------|
| **Rust** | Symbolic operands (`in`, `out`, `inout`) | Clear, type-safe | Verbose |
| **Zig** | GCC-compatible constraints | Portable | Cryptic syntax |
| **GCC** | Single-letter constraints | Compact | Poorly documented |
| **D** | Direct instructions | Simple | No register allocation |

### Key Insights

1. **GCC constraints are error-prone** - cryptic single letters, late error detection
2. **Rust's symbolic operands are clearest** - explicit intent, good error messages
3. **Platform specification should be explicit** - not implicit in constraints
4. **D's direct syntax is simplest** - but loses compiler optimization

---

## 3. Design Goals

1. **Explicit platform specification** - No guessing which architecture
2. **Simple-friendly syntax** - Match Simple's style, not C/Rust style
3. **Type safety** - Validate operand types at compile time
4. **Multi-level platform control** - File, module, or per-block
5. **Clear error messages** - Fail early with helpful diagnostics

---

## 4. Platform Specification Design

### Option A: File-Level Declaration (Recommended)

```simple
# At top of file, after imports
@platform("x86_64")

fn fast_multiply(a: i64, b: i64) -> i64:
    var result: i64 = 0
    asm:
        "imul {result}, {a}, {b}"
        out result
        in a, b
    result
```

**Pros:**
- Clear scope - entire file uses one platform
- Mirrors `@cfg` pattern
- Easy to enforce in tooling

**Cons:**
- One platform per file (use separate files for multi-platform)

### Option B: Module-Level Declaration

```simple
# In mod.spl or __init__.spl
@platform("x86_64")
module baremetal.x86
```

**Pros:**
- Applies to entire module tree
- Hierarchical (child modules inherit)

**Cons:**
- More complex inheritance rules
- Harder to track which platform applies

### Option C: Per-Block Attribute

```simple
fn fast_multiply(a: i64, b: i64) -> i64:
    var result: i64 = 0

    @platform("x86_64")
    asm:
        "imul {result}, {a}, {b}"
        out result
        in a, b

    result
```

**Pros:**
- Fine-grained control
- Multiple platforms in one file

**Cons:**
- Verbose for files with many asm blocks
- Easy to forget annotation

### Option D: Combined (Recommended Final Design)

```simple
# File-level default (optional)
@platform("x86_64")

fn example():
    # Uses file-level platform
    asm:
        "nop"

    # Override for specific block
    @platform("arm")
    asm:
        "nop"
```

**Inheritance rules:**
1. Block `@platform` overrides file-level
2. File `@platform` overrides module-level
3. Module `@platform` overrides parent module
4. No platform = compile error if asm block present

---

## 5. Supported Platforms

### Platform Identifiers

| Identifier | Architecture | Registers | Notes |
|------------|--------------|-----------|-------|
| `"x86"` | i386/i686 | eax, ebx, ecx, edx, esi, edi, ebp, esp | 32-bit |
| `"x86_64"` | AMD64 | rax, rbx, rcx, rdx, rsi, rdi, r8-r15 | 64-bit |
| `"arm"` | ARM Cortex-M | r0-r12, sp, lr, pc | Thumb-2 |
| `"arm64"` | AArch64 | x0-x30, sp | 64-bit ARM |
| `"riscv32"` | RISC-V 32 | x0-x31 (a0-a7, t0-t6, s0-s11) | 32-bit |
| `"riscv64"` | RISC-V 64 | x0-x31 | 64-bit |
| `"avr"` | ATmega | r0-r31 | 8-bit |
| `"msp430"` | MSP430 | r0-r15 | 16-bit |

### Platform Aliases

```simple
@platform("cortex-m4")    # Alias for "arm" with Cortex-M4 features
@platform("cortex-m0")    # Alias for "arm" with Cortex-M0 subset
@platform("atmega328p")   # Alias for "avr" with ATmega328P features
```

---

## 6. Assembly Block Syntax

### Basic Syntax

```simple
asm:
    "instruction template"
    [operand declarations]
    [options]
```

### Operand Types

| Type | Syntax | Meaning |
|------|--------|---------|
| **in** | `in var` | Input only (read) |
| **out** | `out var` | Output only (write) |
| **inout** | `inout var` | Read and write |
| **clobber** | `clobber reg` | Register modified but not used |

### Register Specification

```simple
# Compiler chooses register (recommended)
asm:
    "add {a}, {b}"
    inout a
    in b

# Explicit register (when needed)
asm:
    "syscall"
    in(rax) syscall_num
    in(rdi) arg1
    out(rax) result
    clobber rcx, r11
```

### Template Syntax

```simple
# Named placeholders (recommended)
asm:
    "mov {dest}, {src}"
    out dest
    in src

# With register size modifier
asm:
    "mov {dest:l}, {src:l}"    # Low byte (al, bl, etc.)
    out dest
    in src

# Multiple instructions
asm:
    """
    push {value}
    call {func}
    add rsp, 8
    mov {result}, rax
    """
    in value, func
    out result
    clobber rax, rcx, rdx, r8, r9, r10, r11
```

### Template Modifiers

| Modifier | x86_64 | arm64 | Description |
|----------|--------|-------|-------------|
| `:q` | rax | x0 | Full 64-bit register |
| `:d` | eax | w0 | 32-bit (dword) |
| `:w` | ax | - | 16-bit (word) |
| `:l` | al | - | Low 8-bit (byte) |
| `:h` | ah | - | High 8-bit (x86 only) |

---

## 7. Options

### Available Options

```simple
asm:
    "template"
    operands
    options: [pure, nomem, nostack, preserves_flags]
```

| Option | Meaning |
|--------|---------|
| `pure` | No side effects (can be optimized away if unused) |
| `nomem` | Does not access memory |
| `readonly` | Only reads memory (no writes) |
| `nostack` | Does not use stack |
| `preserves_flags` | Does not modify CPU flags |
| `volatile` | Cannot be optimized away (default for bare asm) |
| `att_syntax` | Use AT&T syntax (x86 only) |

### Clobber ABI Shortcut

```simple
asm:
    "call {func}"
    in func
    out(rax) result
    clobber_abi "C"    # Auto-clobbers caller-saved registers
```

---

## 8. Type Mapping

### Operand Types

| Simple Type | Valid Registers | Notes |
|-------------|-----------------|-------|
| `i8`, `u8` | Byte regs (al, r8b) | 8-bit |
| `i16`, `u16` | Word regs (ax, r8w) | 16-bit |
| `i32`, `u32` | Dword regs (eax, r8d) | 32-bit |
| `i64`, `u64` | Qword regs (rax, r8) | 64-bit |
| `f32` | xmm0-xmm15 | SSE |
| `f64` | xmm0-xmm15 | SSE |
| `ptr<T>` | Pointer regs | Address |
| `rawptr<T>` | Pointer regs | Raw address |

### Type Checking

```simple
fn example():
    val x: i32 = 42
    var y: i64 = 0

    # ERROR: Type mismatch - x is i32, but rax is 64-bit
    asm:
        "mov {y}, {x}"
        in(rax) x      # Compile error!
        out y

    # CORRECT: Use 32-bit register
    asm:
        "movsxd {y}, {x}"
        in(eax) x
        out y
```

---

## 9. Safety Model

### Unsafe Requirement

All `asm` blocks require `unsafe` context:

```simple
fn safe_function():
    # ERROR: asm requires unsafe
    asm:
        "nop"

unsafe fn unsafe_function():
    # OK: in unsafe function
    asm:
        "nop"

fn mixed_function():
    # OK: explicit unsafe block
    unsafe:
        asm:
            "nop"
```

### Memory Safety

```simple
# The compiler cannot verify memory safety in asm blocks
# Programmer is responsible for:
# - Valid memory addresses
# - No buffer overflows
# - Proper alignment
# - No data races
```

---

## 10. Conditional Assembly

### Platform-Conditional Blocks

```simple
@platform("x86_64")
fn fast_popcount(x: u64) -> i32:
    var result: i32 = 0
    unsafe:
        asm:
            "popcnt {result:d}, {x}"
            in x
            out result
    result

@platform("arm64")
fn fast_popcount(x: u64) -> i32:
    var result: i32 = 0
    unsafe:
        asm:
            "cnt v0.8b, v0.8b"
            "addv b0, v0.8b"
            "fmov {result:w}, s0"
            in(v0) x
            out result
    result

# Fallback for other platforms
fn fast_popcount(x: u64) -> i32:
    # Software implementation
    var n = x
    var count = 0
    while n > 0:
        count = count + (n & 1) as i32
        n = n >> 1
    count
```

### Feature Detection

```simple
@platform("x86_64")
@requires("avx2")
fn simd_add(a: [f32; 8], b: [f32; 8]) -> [f32; 8]:
    var result: [f32; 8] = [0.0; 8]
    unsafe:
        asm:
            "vmovups ymm0, [{a}]"
            "vmovups ymm1, [{b}]"
            "vaddps ymm0, ymm0, ymm1"
            "vmovups [{result}], ymm0"
            in a, b
            out result
            clobber ymm0, ymm1
    result
```

---

## 11. Examples

### Example 1: x86_64 Syscall

```simple
@platform("x86_64")

unsafe fn syscall3(num: i64, arg1: i64, arg2: i64, arg3: i64) -> i64:
    var result: i64 = 0
    asm:
        "syscall"
        in(rax) num
        in(rdi) arg1
        in(rsi) arg2
        in(rdx) arg3
        out(rax) result
        clobber rcx, r11
    result

unsafe fn sys_write(fd: i64, buf: ptr<u8>, len: i64) -> i64:
    syscall3(1, fd, buf as i64, len)
```

### Example 2: ARM Cortex-M Interrupt Control

```simple
@platform("arm")

unsafe fn disable_interrupts():
    asm:
        "cpsid i"
        options: [volatile, nomem]

unsafe fn enable_interrupts():
    asm:
        "cpsie i"
        options: [volatile, nomem]

unsafe fn with_interrupts_disabled<T>(f: fn() -> T) -> T:
    disable_interrupts()
    val result = f()
    enable_interrupts()
    result
```

### Example 3: RISC-V Atomic Compare-and-Swap

```simple
@platform("riscv64")

unsafe fn compare_and_swap(ptr: rawptr<i64>, expected: i64, desired: i64) -> bool:
    var success: i64 = 0
    asm:
        """
        lr.d.aq t0, ({ptr})
        bne t0, {expected}, 1f
        sc.d.rl {success}, {desired}, ({ptr})
        seqz {success}, {success}
        j 2f
        1: li {success}, 0
        2:
        """
        in ptr, expected, desired
        out success
        clobber t0
    success != 0
```

### Example 4: AVR GPIO

```simple
@platform("avr")

val PORTB: u8 = 0x25
val DDRB: u8 = 0x24

unsafe fn set_pin_output(pin: u8):
    asm:
        "sbi {ddr}, {pin}"
        in(io) ddr = DDRB
        in pin

unsafe fn set_pin_high(pin: u8):
    asm:
        "sbi {port}, {pin}"
        in(io) port = PORTB
        in pin

unsafe fn toggle_pin(pin: u8):
    asm:
        "in r16, {port}"
        "eor r16, {mask}"
        "out {port}, r16"
        in(io) port = PORTB
        in mask = (1 << pin)
        clobber r16
```

---

## 12. Error Messages

### Good Error Messages (Goal)

```
error[E0501]: platform not specified for assembly block
 --> src/foo.spl:15:5
   |
15 |     asm:
   |     ^^^ assembly block requires platform specification
   |
help: add @platform attribute to file or block
   |
 1 | @platform("x86_64")
   |
```

```
error[E0502]: register 'rax' not available on platform 'arm'
 --> src/foo.spl:20:9
   |
20 |         in(rax) value
   |            ^^^ 'rax' is x86_64 register
   |
help: use ARM register instead
   |
20 |         in(r0) value
   |
```

```
error[E0503]: type mismatch in assembly operand
 --> src/foo.spl:25:9
   |
25 |         in(eax) value    # value is i64
   |            ^^^ 'eax' is 32-bit, but 'value' is i64
   |
help: use 64-bit register or cast value
   |
25 |         in(rax) value
   |
25 |         in(eax) value as i32
   |
```

---

## 13. Implementation Plan

### Phase 1: Parser Support (16h)

1. Add `@platform` attribute parsing
2. Add `asm:` block parsing
3. Parse operand declarations (`in`, `out`, `inout`, `clobber`)
4. Parse options list

### Phase 2: Semantic Analysis (24h)

1. Validate platform specification
2. Validate register names for platform
3. Type-check operands against registers
4. Verify unsafe context

### Phase 3: Code Generation (32h)

1. Generate platform-specific assembly
2. Handle register allocation for non-explicit registers
3. Emit clobber information
4. Integration with existing codegen

### Phase 4: Platform Backends (40h)

1. x86_64 backend (16h)
2. ARM Cortex-M backend (12h)
3. RISC-V backend (8h)
4. AVR backend (4h)

### Phase 5: Testing & Documentation (16h)

1. Unit tests for each platform
2. Integration tests with QEMU
3. Documentation and examples
4. Error message polish

**Total Estimated:** 128 hours (16 days)

---

## 14. Comparison with Original x86/semihost.spl

### Before (Parse Error)

```simple
@cfg("target_arch", "x86")
export arch_semi_host_call

@inline
fn outb(port: u16, value: u8):
    asm volatile(
        "outb {value}, {port}",
        value = in(reg_byte) value,
        port = in(reg) port
    )
```

### After (New Design)

```simple
@platform("x86_64")

fn outb(port: i32, value: i32):
    unsafe:
        asm:
            "out dx, al"
            in(dx) port
            in(al) value
            options: [volatile, nomem]

fn arch_semi_host_call(op: i32, arg0: i32, arg1: i32) -> i32:
    # Implementation using asm blocks
    ...
```

---

## 15. Target-Qualified Assembly (`asm match`)

**Full spec:** [`doc/feature/usage/target_qualified_asm.md`](../../feature/usage/target_qualified_asm.md)

Plain `asm` blocks (Sections 6-11) work for single-platform code where the target is set by
`@platform` or the build configuration. For **multi-platform** code that must dispatch to
different assembly per architecture/OS/ABI/backend, use `asm match`.

### Key constraints

- Target-qualified asm **only** works with `asm match:` or `asm assert [...]`
- Standalone `asm[spec]{ ... }` is **not supported** — always use `asm match`
- Each `case [spec]` qualifier uses the existing type system:
  `[TargetArch, TargetOS, ABI, BackendKind version_constraint]`
- Non-exhaustive `asm match` (no `_` catch-all) emits a compiler **warning**
- `_` catch-all should use `compile_error("message")` or provide a fallback implementation

### Quick example

```simple
fn memory_fence():
    asm match:
        case [x86_64]:
            "mfence"
        case [aarch64]:
            "dmb ish"
        case [riscv64]:
            "fence rw, rw"
        case _:
            compile_error("memory_fence: unsupported arch")
```

### Version constraints

Backend version requirements use `>=`, `==`, `<`, or `~=` (recommended/proper version):

```simple
asm match:
    case [x86_64, _, _, llvm >= 15]:
        "vmovaps ymm0, [{0}]"
    case _:
        compile_error("requires llvm 15+")
```

`~=` is a soft constraint: compiles on any version but emits a **note** if the version differs.

### Compile-time assert

```simple
fn kernel_main():
    asm assert [x86_64, linux, gnu, llvm >= 15]
    # Compile error if target doesn't match
    asm:
        "cli"
```

---

## 16. Open Questions

1. **Should `asm` require explicit `unsafe`?**
   - Rust requires it, D requires `@trusted`
   - Recommendation: Yes, require `unsafe` context

2. **Should we support AT&T syntax?**
   - GCC default, Rust option
   - Recommendation: Intel default, `att_syntax` option

3. **How to handle register allocation for mixed explicit/implicit?**
   - Rust allows mixing, compiler avoids conflicts
   - Recommendation: Same as Rust

4. **Should we support naked functions?**
   - Useful for interrupt handlers, entry points
   - Recommendation: Add `@naked` attribute for Phase 2

---

## 17. References

- [Rust Inline Assembly RFC](https://rust-lang.github.io/rfcs/2873-inline-asm.html)
- [Zig Assembly Documentation](https://ziglang.org/documentation/master/)
- [GCC Extended Asm](https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html)
- [D Inline Assembler](https://dlang.org/spec/iasm.html)
- [ARM Architecture Reference Manual](https://developer.arm.com/documentation)
- [Intel x86-64 Manual](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
- [RISC-V Specification](https://riscv.org/specifications/)
