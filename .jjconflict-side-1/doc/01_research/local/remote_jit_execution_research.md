# Remote JIT Execution Research

**Date:** 2026-02-05
**Status:** Research Complete
**Author:** Claude

## 1. Executive Summary

This document researches the feasibility of remote JIT execution using external debuggers (GDB/TRACE32) as memory writers. The system compiles Simple code to native machine code on the host, uploads it to a target device via debug protocol, and executes using hardware breakpoint sharing.

**Key Finding:** The architecture is feasible with a single hardware breakpoint shared via software multiplexing.

---

## 2. Target Architectures

### 2.1 ARM32 (ARMv7-M / Cortex-M)

**Architecture Overview:**
- 32-bit RISC architecture
- Thumb-2 instruction set (16/32-bit mixed)
- Little-endian (configurable)
- 16 general-purpose registers (R0-R15)

**Register Set:**
| Register | Purpose | Calling Convention (AAPCS) |
|----------|---------|---------------------------|
| R0-R3 | Arguments/Return | Caller-saved |
| R4-R11 | Local variables | Callee-saved |
| R12 (IP) | Intra-procedure scratch | Caller-saved |
| R13 (SP) | Stack pointer | - |
| R14 (LR) | Link register | Return address |
| R15 (PC) | Program counter | - |
| CPSR | Status register | Flags (N, Z, C, V) |

**Memory Map (Cortex-M typical):**
```
0x00000000 - 0x1FFFFFFF  Code (Flash)
0x20000000 - 0x3FFFFFFF  SRAM
0x40000000 - 0x5FFFFFFF  Peripherals
0xE0000000 - 0xFFFFFFFF  System (NVIC, Debug)
```

**Debug Hardware (CoreSight):**
- **FPB (Flash Patch and Breakpoint):** 6-8 instruction comparators
- **DWT (Data Watchpoint and Trace):** 4 data comparators
- **ITM (Instrumentation Trace Macrocell):** Printf-style tracing
- **TPIU (Trace Port Interface Unit):** Trace output

**FPB Registers:**
```
FP_CTRL  (0xE0002000): Control register
FP_REMAP (0xE0002004): Remap table address
FP_COMP0 (0xE0002008): Comparator 0
FP_COMP1 (0xE000200C): Comparator 1
...
FP_COMP7 (0xE0002024): Comparator 7

FP_COMPn encoding:
  Bit 0:     Enable
  Bit 1:     REPLACE (0=breakpoint, 1=remap)
  Bits 2-28: COMP (address bits [28:2])
  Bits 30-31: REPLACE code
```

**DWT Registers (Watchpoints):**
```
DWT_CTRL     (0xE0001000): Control
DWT_COMP0    (0xE0001020): Comparator 0 value
DWT_MASK0    (0xE0001024): Comparator 0 mask
DWT_FUNCTION0(0xE0001028): Comparator 0 function

DWT_FUNCTIONn encoding:
  Bits 0-3: FUNCTION
    0000 = Disabled
    0100 = PC value match (instruction)
    0101 = Data address read
    0110 = Data address write
    0111 = Data address read/write
```

---

### 2.2 RISC-V 32-bit (RV32IMAC)

**Architecture Overview:**
- 32-bit RISC architecture
- Modular ISA (I=Integer, M=Multiply, A=Atomic, C=Compressed)
- Little-endian
- 32 general-purpose registers (x0-x31)

**Register Set:**
| Register | ABI Name | Purpose | Calling Convention |
|----------|----------|---------|-------------------|
| x0 | zero | Hardwired zero | - |
| x1 | ra | Return address | Caller-saved |
| x2 | sp | Stack pointer | Callee-saved |
| x3 | gp | Global pointer | - |
| x4 | tp | Thread pointer | - |
| x5-x7 | t0-t2 | Temporaries | Caller-saved |
| x8 | s0/fp | Saved/Frame pointer | Callee-saved |
| x9 | s1 | Saved register | Callee-saved |
| x10-x11 | a0-a1 | Arguments/Return | Caller-saved |
| x12-x17 | a2-a7 | Arguments | Caller-saved |
| x18-x27 | s2-s11 | Saved registers | Callee-saved |
| x28-x31 | t3-t6 | Temporaries | Caller-saved |

**Memory Map (QEMU virt typical):**
```
0x00001000 - 0x00011FFF  Boot ROM
0x02000000 - 0x0200FFFF  CLINT (Core Local Interruptor)
0x0C000000 - 0x0FFFFFFF  PLIC (Platform-Level Interrupt Controller)
0x10000000 - 0x10000FFF  UART
0x80000000 - 0xFFFFFFFF  RAM (configurable)
```

**Debug Hardware (RISC-V Debug Spec 0.13):**
- **Trigger Module:** Up to 16 triggers (implementation-dependent)
- **Debug Module:** External debug support
- **Program Buffer:** Execute arbitrary instructions

**Trigger CSRs:**
```
tselect (0x7A0):  Trigger select
tdata1  (0x7A1):  Trigger data 1 (type + config)
tdata2  (0x7A2):  Trigger data 2 (address/data)
tdata3  (0x7A3):  Trigger data 3 (extra config)

tdata1 (mcontrol) encoding for address match:
  Bits 0-5:   DATA (trigger-specific)
  Bit 6:      DMODE (debug mode only)
  Bits 7-11:  TYPE (2 = address/data match)
  Bit 12:     CHAIN
  Bits 13-14: MATCH (0=equal, 1=napot, 2=>=, 3=<)
  Bit 15:     M (match in M-mode)
  Bit 16:     S (match in S-mode)
  Bit 17:     U (match in U-mode)
  Bit 18:     EXECUTE
  Bit 19:     STORE
  Bit 20:     LOAD
```

**QEMU RISC-V Debug Support:**
- QEMU implements RISC-V debug spec 0.13
- Supports up to 4 hardware breakpoints
- GDB stub built-in (`-s -S` flags)
- Memory-mapped debug interface

---

## 3. Debug Interfaces

### 3.1 JTAG (Joint Test Action Group)

**Physical Interface:**
```
Pin   Signal   Direction   Purpose
─────────────────────────────────────
1     TCK      Host→Target Test Clock
2     TMS      Host→Target Test Mode Select
3     TDI      Host→Target Test Data In
4     TDO      Target→Host Test Data Out
5     nTRST    Host→Target Test Reset (optional)
6     nSRST    Host→Target System Reset (optional)
```

**TAP State Machine:**
```
                    ┌───────────────┐
                    │  Test-Logic-  │
            ┌───────│    Reset      │───────┐
            │       └───────────────┘       │
            │ TMS=0          │ TMS=1        │
            ▼                ▼              │
     ┌──────────────┐  ┌──────────────┐    │
     │  Run-Test/   │  │   Select-    │    │
     │    Idle      │  │   DR-Scan    │    │
     └──────────────┘  └──────────────┘    │
            │                │              │
           ...              ...            ...
```

**Debug Access Port (DAP):**
- **DP (Debug Port):** JTAG-to-DAP bridge
- **AP (Access Port):** Target memory access
- **MEM-AP:** Memory-mapped access to target

**ARM CoreSight DAP:**
```
DPACC: Debug Port Access
  CTRL/STAT (0x04): Control/Status
  SELECT    (0x08): AP select
  RDBUFF    (0x0C): Read buffer

APACC: Access Port Access
  CSW  (0x00): Control/Status Word
  TAR  (0x04): Transfer Address
  DRW  (0x0C): Data Read/Write
```

---

### 3.2 SWD (Serial Wire Debug)

**Physical Interface (2-wire):**
```
Pin   Signal   Direction   Purpose
─────────────────────────────────────
1     SWCLK    Host→Target Serial Wire Clock
2     SWDIO    Bidirectional Serial Wire Data
3     nRESET   Host→Target System Reset (optional)
```

**Advantages over JTAG:**
- Fewer pins (2 vs 4-5)
- Same DAP access capability
- Faster for single-target debugging

**Protocol:**
```
Packet format: [Start][APnDP][RnW][A2][A3][Parity][Stop][Park][Turnaround]
                 1      1     1    1   1    1      1     1       1-2

Response: [ACK/NACK/WAIT][Data(32)][Parity]
              3            32        1
```

---

### 3.3 GDB Remote Serial Protocol (RSP)

**Transport:**
- TCP socket (most common)
- Serial port
- USB (via gdbserver)

**Packet Format:**
```
$<command>#<checksum>
+  (ACK)
-  (NACK, retransmit)

Checksum = sum of ASCII values mod 256
```

**Essential Commands:**
| Command | Description | Example |
|---------|-------------|---------|
| `?` | Query halt reason | `$?#3f` → `S05` (SIGTRAP) |
| `g` | Read all registers | `$g#67` → hex values |
| `G` | Write all registers | `$G<hex>#XX` |
| `p n` | Read register n | `$p0#a0` → register 0 |
| `P n=v` | Write register n | `$P0=12345678#XX` |
| `m addr,len` | Read memory | `$m80000000,4#XX` |
| `M addr,len:data` | Write memory | `$M80000000,4:12345678#XX` |
| `c [addr]` | Continue | `$c#63` |
| `s [addr]` | Single step | `$s#73` |
| `Z type,addr,kind` | Insert breakpoint | `$Z1,80000000,4#XX` |
| `z type,addr,kind` | Remove breakpoint | `$z1,80000000,4#XX` |

**Breakpoint Types (Z/z commands):**
| Type | Description | Hardware Support |
|------|-------------|------------------|
| 0 | Software breakpoint | No (uses EBREAK/BKPT) |
| 1 | Hardware breakpoint | Yes (instruction) |
| 2 | Write watchpoint | Yes (data) |
| 3 | Read watchpoint | Yes (data) |
| 4 | Access watchpoint | Yes (data) |

**Extended Commands:**
| Command | Description |
|---------|-------------|
| `qSupported` | Query supported features |
| `qXfer:memory-map:read` | Get memory map |
| `vCont` | Extended continue/step |
| `qRcmd,cmd` | Execute monitor command |

---

### 3.4 TRACE32 API

**Connection Methods:**
1. **Remote Control Interface (RCL):** TCP/IP API
2. **Practice Script:** Built-in scripting language
3. **Python API:** `lauterbach.trace32.rcl` module

**Python API Example:**
```python
import lauterbach.trace32.rcl as t32

# Connect
t32.Init("NODE=localhost PORT=20000 PACKLEN=1024")

# Memory operations
t32.Cmd("Data.Set 0x80000000 %Long 0x12345678")
value = t32.Var("Data.Long(0x80000000)")

# Breakpoints
t32.Cmd("Break.Set 0x80000000 /Hard /Program")
t32.Cmd("Break.Set 0x80000000 /Hard /Write")

# Execution
t32.Cmd("Go")
t32.Cmd("Break")

# State query
state = t32.GetState()
pc = t32.Var("Register(PC)")

# Disconnect
t32.Exit()
```

**Practice Script Commands:**
```
; Memory operations
Data.Set <addr> %Byte <value>
Data.Set <addr> %Word <value>
Data.Set <addr> %Long <value>
Data.dump <start>--<end>

; Register operations
Register.Set PC <value>
Register.Set SP <value>
Print Register(PC)

; Breakpoints
Break.Set <addr> /Program         ; Software breakpoint
Break.Set <addr> /Program /Hard   ; Hardware breakpoint
Break.Set <addr> /Read /Hard      ; Read watchpoint
Break.Set <addr> /Write /Hard     ; Write watchpoint
Break.Delete <addr>
Break.List

; Execution
Go
Go.direct                         ; No breakpoint check
Step
Step.Over
Break                             ; Halt
System.Down
System.Up

; Memory loading
Data.LOAD.Binary <file> <addr>
Data.LOAD.Elf <file>
```

---

## 4. Hardware Breakpoint Resources

### 4.1 ARM32 (Cortex-M)

| Resource | Count | Type | Notes |
|----------|-------|------|-------|
| FPB Comparators | 6-8 | Instruction | Can also remap flash |
| DWT Comparators | 4 | Data (watchpoint) | Read/Write/Access |

**Total:** 10-12 hardware debug resources

### 4.2 RISC-V32

| Resource | Count | Type | Notes |
|----------|-------|------|-------|
| Triggers | 2-16 | Configurable | Implementation-dependent |

**QEMU Default:** 4 triggers (all configurable as instruction or data)

### 4.3 Comparison

| Feature | ARM32 | RISC-V32 | Notes |
|---------|-------|----------|-------|
| Instruction BP | 6-8 | 2-4 | HW breakpoints |
| Data BP | 4 | 2-4 | Watchpoints |
| Total | 10-12 | 4-8 | - |
| Flash Remap | Yes (FPB) | No | ARM-specific |
| Chained Triggers | No | Yes | RISC-V advanced |
| Data Value Match | Limited | Yes | RISC-V feature |

---

## 5. Software Breakpoint Multiplexing

### 5.1 The Problem

Hardware breakpoints are scarce:
- ARM32: 6-8 instruction comparators
- RISC-V32: 2-4 triggers (often less in budget chips)

For remote JIT execution, we need:
- Multiple breakpoints for debugging
- Only 1-2 HW breakpoints available
- Software breakpoints require code modification (problematic on flash)

### 5.2 The Solution: HW Breakpoint Sharing

**Concept:** Use a single hardware breakpoint as a "dispatcher" that multiplexes multiple software breakpoint addresses.

```
┌─────────────────────────────────────────────────────┐
│  Host: Breakpoint Manager                           │
│  ──────────────────────                             │
│  Software BP table:                                 │
│    [0] 0x80000100 (enabled)                        │
│    [1] 0x80000200 (enabled)                        │
│    [2] 0x80000300 (disabled)                       │
│    [3] 0x80000400 (enabled)                        │
│                                                     │
│  Current HW BP:                                     │
│    points to: 0x80000100 (first enabled)           │
└─────────────────────┬───────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────┐
│  Target: Single HW Breakpoint                       │
│  ────────────────────────────                       │
│  DR0 / FPB_COMP0 / tdata2 = 0x80000100             │
│                                                     │
│  Execution hits 0x80000100:                        │
│    1. Target halts (HW BP triggered)               │
│    2. Host notified via GDB/TRACE32                │
│    3. Host checks: Is PC in SW BP table?           │
│       - YES: Report breakpoint to user             │
│       - NO: Spurious, continue execution           │
│    4. Host sets HW BP to next enabled SW BP        │
│    5. Host continues target execution              │
└─────────────────────────────────────────────────────┘
```

### 5.3 Algorithm: Round-Robin BP Sharing

```
State:
  sw_breakpoints: [(addr, enabled, hit_count)]
  hw_bp_index: current index in sw_breakpoints
  hw_bp_addr: current hardware breakpoint address

On target halt:
  pc = read_register(PC)

  if pc in sw_breakpoints and sw_breakpoints[pc].enabled:
    # Real breakpoint hit
    sw_breakpoints[pc].hit_count += 1
    notify_user("Breakpoint at {pc}")
    wait_for_user_continue()

  # Advance to next breakpoint (round-robin)
  hw_bp_index = (hw_bp_index + 1) % len(sw_breakpoints)
  while not sw_breakpoints[hw_bp_index].enabled:
    hw_bp_index = (hw_bp_index + 1) % len(sw_breakpoints)

  hw_bp_addr = sw_breakpoints[hw_bp_index].addr
  set_hardware_breakpoint(0, hw_bp_addr)
  continue_execution()
```

### 5.4 Optimization: Predictive BP Placement

Instead of round-robin, predict which breakpoint will be hit next:

```
State:
  execution_history: [addr]  # Recent PC values
  bp_hit_counts: {addr: count}

predict_next_breakpoint():
  # Option 1: Most frequently hit
  return max(sw_breakpoints, key=lambda bp: bp_hit_counts[bp.addr])

  # Option 2: Closest to current PC (linear code assumption)
  pc = read_register(PC)
  return min(sw_breakpoints, key=lambda bp: abs(bp.addr - pc))

  # Option 3: Call graph analysis (if available)
  # Use control flow graph to predict next BP
```

### 5.5 Single-Step Emulation

When user requests single-step but HW single-step is limited:

```
single_step_via_breakpoint():
  pc = read_register(PC)
  next_pc = disassemble_and_predict_next(pc)

  # Handle branches
  if is_branch_instruction(pc):
    # Set BP at both targets
    taken_addr = get_branch_target(pc)
    not_taken_addr = pc + instruction_size(pc)

    # Use 2 HW BPs if available, else:
    # Set BP at taken, execute, check if PC changed
    set_hardware_breakpoint(0, taken_addr)
    if hw_bp_count >= 2:
      set_hardware_breakpoint(1, not_taken_addr)

  else:
    # Linear: just set BP at next instruction
    set_hardware_breakpoint(0, next_pc)

  continue_execution()
  wait_for_halt()
  clear_hardware_breakpoints()
```

---

## 6. QEMU RISC-V32 Setup

### 6.1 QEMU Machine Configuration

```bash
# Install QEMU
apt-get install qemu-system-riscv32

# Run with GDB stub
qemu-system-riscv32 \
  -machine virt \
  -cpu rv32 \
  -m 128M \
  -nographic \
  -bios none \
  -kernel program.elf \
  -s -S  # -s: GDB on port 1234, -S: halt at start

# Or specify GDB port
qemu-system-riscv32 \
  -machine virt \
  -cpu rv32 \
  -m 128M \
  -nographic \
  -gdb tcp::3333 \
  -S
```

### 6.2 Memory Map (QEMU virt)

```
Address Range          Size      Description
──────────────────────────────────────────────
0x00001000-0x00011FFF  64 KB     Boot ROM
0x02000000-0x0200FFFF  64 KB     CLINT
0x0C000000-0x0FFFFFFF  64 MB     PLIC
0x10000000-0x10000FFF  4 KB      UART (NS16550)
0x10001000-0x10001FFF  4 KB      VirtIO
0x80000000-0x87FFFFFF  128 MB    RAM (default)
```

### 6.3 Minimal Bare-Metal Program

```asm
# start.S - RISC-V32 entry point
.section .text.start
.global _start

_start:
    # Set up stack
    la sp, _stack_top

    # Clear BSS
    la t0, _bss_start
    la t1, _bss_end
clear_bss:
    bge t0, t1, call_main
    sw zero, 0(t0)
    addi t0, t0, 4
    j clear_bss

call_main:
    # Call main
    call main

    # Halt on return
halt:
    wfi
    j halt

.section .bss
.align 4
_stack:
    .space 4096
_stack_top:
```

**Linker Script:**
```ld
/* link.ld */
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

SECTIONS {
    .text : {
        *(.text.start)
        *(.text*)
    } > RAM

    .rodata : {
        *(.rodata*)
    } > RAM

    .data : {
        *(.data*)
    } > RAM

    .bss : {
        _bss_start = .;
        *(.bss*)
        *(COMMON)
        _bss_end = .;
    } > RAM
}
```

### 6.4 GDB Connection Test

```bash
# Terminal 1: Start QEMU
qemu-system-riscv32 -machine virt -cpu rv32 -m 128M \
  -nographic -bios none -kernel program.elf -s -S

# Terminal 2: Connect GDB
riscv32-unknown-elf-gdb program.elf
(gdb) target remote :1234
(gdb) info registers
(gdb) x/10i 0x80000000
(gdb) hbreak *0x80000000
(gdb) continue
```

---

## 7. Code Generation Requirements

### 7.1 ARM32 Code Generation

**Instruction Encoding (Thumb-2):**
```
ADD Rd, Rn, Rm:     0x4400 | (Rm << 3) | Rd  (16-bit Thumb)
ADD.W Rd, Rn, Rm:   0xEB00 0x0000 | ...      (32-bit Thumb-2)

MOV Rd, #imm8:      0x2000 | (Rd << 8) | imm8

BL offset:          0xF000 | (offset_high)
                    0xD000 | (offset_low)

BKPT #imm:          0xBE00 | imm8  (Software breakpoint)
```

**Cranelift ARM32 Support:**
- Cranelift has `aarch32` backend (experimental)
- Thumb-2 support limited
- May need custom code generator

### 7.2 RISC-V32 Code Generation

**Instruction Encoding (RV32I):**
```
ADD rd, rs1, rs2:   0x33 | (rd << 7) | (rs1 << 15) | (rs2 << 20)
ADDI rd, rs1, imm:  0x13 | (rd << 7) | (rs1 << 15) | (imm << 20)
LW rd, imm(rs1):    0x03 | (rd << 7) | (rs1 << 15) | (imm << 20) | (0x2 << 12)
SW rs2, imm(rs1):   0x23 | (imm[4:0] << 7) | (rs1 << 15) | (rs2 << 20) | (imm[11:5] << 25) | (0x2 << 12)
JAL rd, offset:     0x6F | (rd << 7) | (offset encoding)
JALR rd, rs1, imm:  0x67 | (rd << 7) | (rs1 << 15) | (imm << 20)
BEQ rs1, rs2, off:  0x63 | ... | (0x0 << 12)
EBREAK:             0x00100073  (Software breakpoint / debugger trap)
```

**Cranelift RISC-V32 Support:**
- Cranelift has `riscv32` backend
- Good support for RV32IMAC
- Can generate position-independent code

### 7.3 Position-Independent Code (PIC)

For uploaded code, PIC is essential:

```
# Non-PIC (absolute addressing) - BROKEN for upload
lui a0, %hi(data)
addi a0, a0, %lo(data)

# PIC (PC-relative) - WORKS for upload
auipc a0, %pcrel_hi(data)
addi a0, a0, %pcrel_lo(data)
```

**Cranelift PIC flag:**
```rust
let mut builder = settings::builder();
builder.set("is_pic", "true").unwrap();
```

---

## 8. Performance Considerations

### 8.1 Communication Latency

| Operation | GDB (TCP) | TRACE32 (TCP) | TRACE32 (USB) |
|-----------|-----------|---------------|---------------|
| Read 4 bytes | ~1ms | ~0.5ms | ~0.1ms |
| Write 4 bytes | ~1ms | ~0.5ms | ~0.1ms |
| Read 1KB | ~5ms | ~2ms | ~0.5ms |
| Write 1KB | ~5ms | ~2ms | ~0.5ms |
| Set breakpoint | ~2ms | ~1ms | ~0.2ms |
| Continue | ~1ms | ~0.5ms | ~0.1ms |

### 8.2 BP Sharing Overhead

With N software breakpoints and 1 hardware breakpoint:
- Worst case: N halts to hit the right BP
- Average case: N/2 halts (random access)
- Best case: 1 halt (predictive placement)

**Mitigation:**
- Use prediction algorithm
- Batch BP updates
- Use 2 HW BPs if available (reduces overhead by 50%)

---

## 9. Security Considerations

### 9.1 Code Upload Risks

- **Malicious code injection:** Only upload from trusted sources
- **Memory corruption:** Validate upload addresses
- **Privilege escalation:** Use debug authentication if available

### 9.2 Debug Authentication

**ARM CoreSight:**
- Debug Authentication (DBGAUTH) signals
- Secure debug enable
- Non-invasive debug permissions

**RISC-V:**
- Debug Module authentication
- `dmcontrol.authbusy` and `dmcontrol.authenticated`
- Implementation-dependent security features

---

## 10. References

### Standards
1. ARM Debug Interface Architecture Specification ADIv5
2. ARM CoreSight Architecture Specification
3. RISC-V Debug Specification v0.13
4. IEEE 1149.1 (JTAG) Standard

### Documentation
5. GDB Remote Serial Protocol: https://sourceware.org/gdb/onlinedocs/gdb/Remote-Protocol.html
6. TRACE32 PowerView Manual: Lauterbach documentation
7. QEMU RISC-V Documentation: https://www.qemu.org/docs/master/system/riscv/virt.html

### Code References
8. OpenOCD source code (JTAG/SWD implementation)
9. QEMU RISC-V debug implementation (target/riscv/debug.c)
10. Cranelift codegen (cranelift-codegen crate)
