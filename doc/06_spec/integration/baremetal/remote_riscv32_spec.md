# Remote Riscv32 Specification

> Tests covering Remote Debug Core Types, RISC-V 32 Target, Feature Registry, GDB MI Parser, Feature Rank Constants, FeatureId, QEMU Integration, DebugConfig class methods, HaltReason enum methods, DebugError additional variants, GdbVariable class methods, FeatureHandler class methods, FeatureRegistry impl methods.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 85 | 85 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Riscv32 Specification

## Scenarios

### Remote Debug Core Types

#### Architecture enum

<details>
<summary>Advanced: converts to string</summary>

#### converts to string _(slow)_

- converts to string
   - Expected: Architecture.RiscV32.to_string() equals `riscv32`
   - Expected: Architecture.Arm32.to_string() equals `arm32`
   - Expected: Architecture.X86_64.to_string() equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("converts to string")
expect(Architecture.RiscV32.to_string()).to_equal("riscv32")
expect(Architecture.Arm32.to_string()).to_equal("arm32")
expect(Architecture.X86_64.to_string()).to_equal("x86_64")
```

</details>


</details>

#### Endianness enum

<details>
<summary>Advanced: converts to string</summary>

#### converts to string _(slow)_

- converts to string
   - Expected: Endianness.Little.to_string() equals `little`
   - Expected: Endianness.Big.to_string() equals `big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("converts to string")
expect(Endianness.Little.to_string()).to_equal("little")
expect(Endianness.Big.to_string()).to_equal("big")
```

</details>


</details>

#### DebugConfig

<details>
<summary>Advanced: creates default GDB config</summary>

#### creates default GDB config _(slow)_

- creates default GDB config
   - Expected: config.host equals `localhost`
   - Expected: config.port equals `1234`
   - Expected: config.program equals `test.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates default GDB config")
val config = DebugConfig.default_gdb("test.elf")
expect(config.host).to_equal("localhost")
expect(config.port).to_equal(1234)
expect(config.program).to_equal("test.elf")
```

</details>


</details>

<details>
<summary>Advanced: creates Trace32 config</summary>

#### creates Trace32 config _(slow)_

- creates Trace32 config
   - Expected: config.host equals `192.168.1.10`
   - Expected: config.port equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates Trace32 config")
val config = DebugConfig.for_trace32("192.168.1.10", 20000)
expect(config.host).to_equal("192.168.1.10")
expect(config.port).to_equal(20000)
```

</details>


</details>

#### DebugError

<details>
<summary>Advanced: formats error messages</summary>

#### formats error messages _(slow)_

- formats error messages
   - Expected: err.to_string() equals `connection failed: refused`
   - Expected: err2.to_string() equals `timeout`
   - Expected: err3.to_string() equals `breakpoint slots full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats error messages")
val err = DebugError.ConnectionFailed(msg: "refused")
expect(err.to_string()).to_equal("connection failed: refused")

val err2 = DebugError.Timeout
expect(err2.to_string()).to_equal("timeout")

val err3 = DebugError.BreakpointFull
expect(err3.to_string()).to_equal("breakpoint slots full")
```

</details>


</details>

### RISC-V 32 Target

#### identification

<details>
<summary>Advanced: reports correct name and architecture</summary>

#### reports correct name and architecture _(slow)_

- reports correct name and architecture
   - Expected: target.name() equals `RISC-V32 (RV32IMAC)`
   - Expected: arch.to_string() equals `riscv32`
   - Expected: endian.to_string() equals `little`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports correct name and architecture")
val target = RiscV32Target.create()
expect(target.name()).to_equal("RISC-V32 (RV32IMAC)")
# BUG-RT workaround: split chained method calls on enum return values
val arch = target.arch()
expect(arch.to_string()).to_equal("riscv32")
val endian = target.endianness()
expect(endian.to_string()).to_equal("little")
```

</details>


</details>

#### registers

<details>
<summary>Advanced: has 33 registers (x0-x31 + PC)</summary>

#### has 33 registers (x0-x31 + PC) _(slow)_

- has 33 registers (x0-x31 + PC)
   - Expected: target.register_count() equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has 33 registers (x0-x31 + PC)")
val target = RiscV32Target.create()
expect(target.register_count()).to_equal(33)
```

</details>


</details>

<details>
<summary>Advanced: maps ABI names correctly</summary>

#### maps ABI names correctly _(slow)_

- maps ABI names correctly
   - Expected: target.register_name(0) equals `zero`
   - Expected: target.register_name(1) equals `ra`
   - Expected: target.register_name(2) equals `sp`
   - Expected: target.register_name(8) equals `s0`
   - Expected: target.register_name(10) equals `a0`
   - Expected: target.register_name(32) equals `pc`
   - Expected: target.register_name(99) equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps ABI names correctly")
val target = RiscV32Target.create()
expect(target.register_name(0)).to_equal("zero")
expect(target.register_name(1)).to_equal("ra")
expect(target.register_name(2)).to_equal("sp")
expect(target.register_name(8)).to_equal("s0")
expect(target.register_name(10)).to_equal("a0")
expect(target.register_name(32)).to_equal("pc")
expect(target.register_name(99)).to_equal("unknown")
```

</details>


</details>

<details>
<summary>Advanced: reverse-maps names to indices</summary>

#### reverse-maps names to indices _(slow)_

- reverse-maps names to indices
   - Expected: target.register_index("zero") equals `0`
   - Expected: target.register_index("sp") equals `2`
   - Expected: target.register_index("a0") equals `10`
   - Expected: target.register_index("pc") equals `32`
   - Expected: target.register_index("nonexistent") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reverse-maps names to indices")
val target = RiscV32Target.create()
expect(target.register_index("zero")).to_equal(0)
expect(target.register_index("sp")).to_equal(2)
expect(target.register_index("a0")).to_equal(10)
expect(target.register_index("pc")).to_equal(32)
expect(target.register_index("nonexistent")).to_equal(-1)
```

</details>


</details>

<details>
<summary>Advanced: reports 4-byte register size</summary>

#### reports 4-byte register size _(slow)_

- reports 4-byte register size
   - Expected: target.register_size(0) equals `4`
   - Expected: target.register_size(32) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports 4-byte register size")
val target = RiscV32Target.create()
expect(target.register_size(0)).to_equal(4)
expect(target.register_size(32)).to_equal(4)
```

</details>


</details>

#### calling convention

<details>
<summary>Advanced: defines argument registers a0-a7</summary>

#### defines argument registers a0-a7 _(slow)_

- defines argument registers a0-a7
   - Expected: arg_regs.len() equals `8`
   - Expected: arg_regs[0] equals `10)  # a0 = x10`
   - Expected: arg_regs[7] equals `17)  # a7 = x17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines argument registers a0-a7")
val target = RiscV32Target.create()
val arg_regs = target.arg_registers()
expect(arg_regs.len()).to_equal(8)
expect(arg_regs[0]).to_equal(10)  # a0 = x10
expect(arg_regs[7]).to_equal(17)  # a7 = x17
```

</details>


</details>

<details>
<summary>Advanced: defines callee-saved registers s0-s11</summary>

#### defines callee-saved registers s0-s11 _(slow)_

- defines callee-saved registers s0-s11
   - Expected: saved.len() equals `12`
   - Expected: saved[0] equals `8)   # s0 = x8`
   - Expected: saved[1] equals `9)   # s1 = x9`
   - Expected: saved[2] equals `18)  # s2 = x18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines callee-saved registers s0-s11")
val target = RiscV32Target.create()
val saved = target.callee_saved_registers()
expect(saved.len()).to_equal(12)
expect(saved[0]).to_equal(8)   # s0 = x8
expect(saved[1]).to_equal(9)   # s1 = x9
expect(saved[2]).to_equal(18)  # s2 = x18
```

</details>


</details>

#### special registers

<details>
<summary>Advanced: identifies PC, SP, FP correctly</summary>

#### identifies PC, SP, FP correctly _(slow)_

- identifies PC, SP, FP correctly
   - Expected: target.pc_register_index() equals `32`
   - Expected: target.sp_register_index() equals `2`
   - Expected: target.fp_register_index() equals `8`
   - Expected: target.return_register_index() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("identifies PC, SP, FP correctly")
val target = RiscV32Target.create()
expect(target.pc_register_index()).to_equal(32)
expect(target.sp_register_index()).to_equal(2)
expect(target.fp_register_index()).to_equal(8)
expect(target.return_register_index()).to_equal(10)
```

</details>


</details>

#### debug hardware

<details>
<summary>Advanced: reports hardware breakpoint capabilities</summary>

#### reports hardware breakpoint capabilities _(slow)_

- reports hardware breakpoint capabilities
   - Expected: target.hw_breakpoint_count() equals `4`
   - Expected: target.hw_watchpoint_count() equals `4`
   - Expected: target.supports_single_step() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports hardware breakpoint capabilities")
val target = RiscV32Target.create()
expect(target.hw_breakpoint_count()).to_equal(4)
expect(target.hw_watchpoint_count()).to_equal(4)
expect(target.supports_single_step()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: defines EBREAK instruction</summary>

#### defines EBREAK instruction _(slow)_

- defines EBREAK instruction
   - Expected: ebreak.len() equals `4`
   - Expected: ebreak[0] equals `0x73`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines EBREAK instruction")
val target = RiscV32Target.create()
val ebreak = target.breakpoint_instruction()
expect(ebreak.len()).to_equal(4)
expect(ebreak[0]).to_equal(0x73)
```

</details>


</details>

#### QEMU memory map

<details>
<summary>Advanced: defines virt machine addresses</summary>

#### defines virt machine addresses _(slow)_

- defines virt machine addresses
   - Expected: target.qemu_virt_ram_base() equals `0x80000000`
   - Expected: target.qemu_virt_uart_base() equals `0x10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines virt machine addresses")
val target = RiscV32Target.create()
expect(target.qemu_virt_ram_base()).to_equal(0x80000000)
expect(target.qemu_virt_uart_base()).to_equal(0x10000000)
```

</details>


</details>

### Feature Registry

#### handler registration

<details>
<summary>Advanced: registers a single handler</summary>

#### registers a single handler _(slow)_

- registers a single handler
   - Expected: registry.is_supported(FeatureId.Halt) is true
   - Expected: registry.is_supported(FeatureId.Resume) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("registers a single handler")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb",
    \args: Ok("halted"),
    "GDB halt"
))
expect(registry.is_supported(FeatureId.Halt)).to_equal(true)
expect(registry.is_supported(FeatureId.Resume)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: stores handlers sorted by rank</summary>

#### stores handlers sorted by rank _(slow)_

- stores handlers sorted by rank
   - Expected: all.len() equals `3`
   - Expected: all[0].rank equals `0`
   - Expected: all[1].rank equals `1`
   - Expected: all[2].rank equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores handlers sorted by rank")
var registry = FeatureRegistry.empty()
# Register rank 4 first
registry.register(FeatureHandler.of(
    FeatureId.ReadLocals, 4, "emulation",
    \args: Ok("emulated"),
    "Emulated"
))
# Register rank 0 second
registry.register(FeatureHandler.of(
    FeatureId.ReadLocals, 0, "gdb",
    \args: Ok("gdb_locals"),
    "GDB"
))
# Register rank 1
registry.register(FeatureHandler.of(
    FeatureId.ReadLocals, 1, "trace32-gdb",
    \args: Ok("t32_locals"),
    "T32 bridge"
))

val all = registry.all_handlers(FeatureId.ReadLocals)
expect(all.len()).to_equal(3)
expect(all[0].rank).to_equal(0)
expect(all[1].rank).to_equal(1)
expect(all[2].rank).to_equal(4)
```

</details>


</details>

#### best handler selection

<details>
<summary>Advanced: picks lowest rank handler</summary>

#### picks lowest rank handler _(slow)_

- picks lowest rank handler
   - Expected: best.rank equals `0`
   - Expected: best.backend_name equals `gdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("picks lowest rank handler")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.ReadLocals, 0, "gdb",
    \args: Ok("gdb_locals"),
    "GDB"
))
registry.register(FeatureHandler.of(
    FeatureId.ReadLocals, 4, "emulation",
    \args: Ok("emulated"),
    "Emulated"
))

val best = registry.best_handler(FeatureId.ReadLocals).unwrap()
expect(best.rank).to_equal(0)
expect(best.backend_name).to_equal("gdb")
```

</details>


</details>

<details>
<summary>Advanced: falls back to emulation when native unavailable</summary>

#### falls back to emulation when native unavailable _(slow)_

- falls back to emulation when native unavailable
   - Expected: best.rank equals `3`
   - Expected: best.backend_name equals `emulation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("falls back to emulation when native unavailable")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.FlashProgram, 3, "emulation",
    \args: Ok("emulated_flash"),
    "OpenOCD flash"
))

val best = registry.best_handler(FeatureId.FlashProgram).unwrap()
expect(best.rank).to_equal(3)
expect(best.backend_name).to_equal("emulation")
```

</details>


</details>

<details>
<summary>Advanced: returns error for unsupported feature</summary>

#### returns error for unsupported feature _(slow)_

- returns error for unsupported feature
   - Expected: result.err == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns error for unsupported feature")
val registry = FeatureRegistry.empty()
val result = registry.best_handler(FeatureId.TraceCapture)
expect(result.err == nil).to_equal(false)
```

</details>


</details>

#### feature execution

<details>
<summary>Advanced: executes best handler</summary>

#### executes best handler _(slow)_

- executes best handler
   - Expected: result.unwrap() equals `halted_via_gdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes best handler")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb",
    \args: Ok("halted_via_gdb"),
    "GDB halt"
))

val result = registry.execute(FeatureId.Halt, [])
expect(result.unwrap()).to_equal("halted_via_gdb")
```

</details>


</details>

#### feature discovery

<details>
<summary>Advanced: lists supported features</summary>

#### lists supported features _(slow)_

- lists supported features
   - Expected: supported.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists supported features")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb", \args: Ok("ok"), "halt"
))
registry.register(FeatureHandler.of(
    FeatureId.Resume, 0, "gdb", \args: Ok("ok"), "resume"
))
registry.register(FeatureHandler.of(
    FeatureId.ReadLocals, 0, "gdb", \args: Ok("ok"), "locals"
))

val supported = registry.supported_features()
expect(supported.len()).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: counts total handlers</summary>

#### counts total handlers _(slow)_

- counts total handlers
   - Expected: registry.handler_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("counts total handlers")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb", \args: Ok("ok"), "halt"
))
registry.register(FeatureHandler.of(
    FeatureId.Halt, 1, "t32", \args: Ok("ok"), "halt"
))
registry.register(FeatureHandler.of(
    FeatureId.Resume, 0, "gdb", \args: Ok("ok"), "resume"
))

expect(registry.handler_count()).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: generates capabilities report</summary>

#### generates capabilities report _(slow)_

- generates capabilities report
   - Expected: report contains `Halt`
   - Expected: report contains `gdb`
   - Expected: report contains `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates capabilities report")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb", \args: Ok("ok"), "GDB halt cmd"
))

val report = registry.capabilities_report()
expect(report.contains("Halt")).to_equal(true)
expect(report.contains("gdb")).to_equal(true)
expect(report.contains("native")).to_equal(true)
```

</details>


</details>

### GDB MI Parser

#### result records

<details>
<summary>Advanced: parses done result</summary>

#### parses done result _(slow)_

- parses done result
   - Expected: token equals `42`
   - Expected: cls equals `done`
   - Expected: data.get("value") ?? "" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses done result")
val record = GdbMiParser.parse_line("42^done,value=\"hello\"")
match record:
    GdbMiRecord.Result(token, cls, data):
        expect(token).to_equal(42)
        expect(cls).to_equal("done")
        expect(data.get("value") ?? "").to_equal("hello")
    _:
        fail("expected Result record")
```

</details>


</details>

<details>
<summary>Advanced: parses error result</summary>

#### parses error result _(slow)_

- parses error result
   - Expected: record.is_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses error result")
val record = GdbMiParser.parse_line("5^error,msg=\"unknown command\"")
expect(record.is_error()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses result without token</summary>

#### parses result without token _(slow)_

- parses result without token
   - Expected: cls equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses result without token")
val record = GdbMiParser.parse_line("^done")
match record:
    GdbMiRecord.Result(token, cls, data):
        expect(cls).to_equal("done")
    _:
        fail("expected Result record")
```

</details>


</details>

#### async records

<details>
<summary>Advanced: parses stopped event</summary>

#### parses stopped event _(slow)_

- parses stopped event
   - Expected: record.is_stopped() is true
   - Expected: cls equals `stopped`
   - Expected: data.get("reason") ?? "" equals `breakpoint-hit`
   - Expected: data.get("bkptno") ?? "" equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses stopped event")
val record = GdbMiParser.parse_line("*stopped,reason=\"breakpoint-hit\",bkptno=\"1\"")
expect(record.is_stopped()).to_equal(true)
match record:
    GdbMiRecord.Async(cls, data):
        expect(cls).to_equal("stopped")
        expect(data.get("reason") ?? "").to_equal("breakpoint-hit")
        expect(data.get("bkptno") ?? "").to_equal("1")
    _:
        fail("expected Async record")
```

</details>


</details>

<details>
<summary>Advanced: parses thread-created notification</summary>

#### parses thread-created notification _(slow)_

- parses thread-created notification
   - Expected: cls equals `thread-created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses thread-created notification")
val record = GdbMiParser.parse_line("=thread-created,id=\"1\"")
match record:
    GdbMiRecord.Async(cls, data):
        expect(cls).to_equal("thread-created")
    _:
        fail("expected Async record")
```

</details>


</details>

#### stream records

<details>
<summary>Advanced: parses console output</summary>

#### parses console output _(slow)_

- parses console output
   - Expected: kind equals `console`
   - Expected: content contains `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses console output")
val record = GdbMiParser.parse_line("~\"Hello World\\n\"")
match record:
    GdbMiRecord.Stream(kind, content):
        expect(kind).to_equal("console")
        expect(content.contains("Hello World")).to_equal(true)
    _:
        fail("expected Stream record")
```

</details>


</details>

<details>
<summary>Advanced: parses log output</summary>

#### parses log output _(slow)_

- parses log output
   - Expected: kind equals `log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses log output")
val record = GdbMiParser.parse_line("&\"info\\n\"")
match record:
    GdbMiRecord.Stream(kind, content):
        expect(kind).to_equal("log")
    _:
        fail("expected Stream record")
```

</details>


</details>

#### prompt

<details>
<summary>Advanced: parses GDB prompt</summary>

#### parses GDB prompt _(slow)_

- parses GDB prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses GDB prompt")
val record = GdbMiParser.parse_line("(gdb)")
match record:
    GdbMiRecord.Prompt:
        pass  # correct
    _:
        fail("expected Prompt")
```

</details>


</details>

#### key-value parsing

<details>
<summary>Advanced: parses simple key-value pairs</summary>

#### parses simple key-value pairs _(slow)_

- parses simple key-value pairs
   - Expected: data.get("name") ?? "" equals `x`
   - Expected: data.get("value") ?? "" equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple key-value pairs")
val data = GdbMiParser.parse_key_values("name=\"x\",value=\"42\"")
expect(data.get("name") ?? "").to_equal("x")
expect(data.get("value") ?? "").to_equal("42")
```

</details>


</details>

<details>
<summary>Advanced: parses nested braces</summary>

#### parses nested braces _(slow)_

- parses nested braces
   - Expected: bkpt contains `number`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses nested braces")
val data = GdbMiParser.parse_key_values("bkpt={number=\"1\",type=\"breakpoint\"}")
val bkpt = data.get("bkpt") ?? ""
expect(bkpt.contains("number")).to_equal(true)
```

</details>


</details>

#### tuple list parsing

<details>
<summary>Advanced: parses list of tuples</summary>

#### parses list of tuples _(slow)_

- parses list of tuples
   - Expected: tuples.len() equals `2`
   - Expected: tuples[0].get("name") ?? "" equals `x`
   - Expected: tuples[0].get("value") ?? "" equals `42`
   - Expected: tuples[1].get("name") ?? "" equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses list of tuples")
val tuples = GdbMiParser.parse_tuple_list("[{name=\"x\",value=\"42\"},{name=\"y\",value=\"10\"}]")
expect(tuples.len()).to_equal(2)
expect(tuples[0].get("name") ?? "").to_equal("x")
expect(tuples[0].get("value") ?? "").to_equal("42")
expect(tuples[1].get("name") ?? "").to_equal("y")
```

</details>


</details>

<details>
<summary>Advanced: handles empty list</summary>

#### handles empty list _(slow)_

- handles empty list
   - Expected: tuples.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty list")
val tuples = GdbMiParser.parse_tuple_list("[]")
expect(tuples.len()).to_equal(0)
```

</details>


</details>

#### hex parsing

<details>
<summary>Advanced: parses hex values</summary>

#### parses hex values _(slow)_

- parses hex values
   - Expected: parse_hex_value("0x2a") equals `42`
   - Expected: parse_hex_value("0xFF") equals `255`
   - Expected: parse_hex_value("0x80000000") equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses hex values")
use app.debug.remote.protocol.gdb_mi_parser.parse_hex_value
expect(parse_hex_value("0x2a")).to_equal(42)
expect(parse_hex_value("0xFF")).to_equal(255)
expect(parse_hex_value("0x80000000")).to_equal(0x80000000)
```

</details>


</details>

<details>
<summary>Advanced: parses hex bytes</summary>

#### parses hex bytes _(slow)_

- parses hex bytes
   - Expected: parse_hex_byte("2a") equals `42`
   - Expected: parse_hex_byte("ff") equals `255`
   - Expected: parse_hex_byte("00") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses hex bytes")
use app.debug.remote.protocol.gdb_mi_parser.parse_hex_byte
expect(parse_hex_byte("2a")).to_equal(42)
expect(parse_hex_byte("ff")).to_equal(255)
expect(parse_hex_byte("00")).to_equal(0)
```

</details>


</details>

### Feature Rank Constants

<details>
<summary>Advanced: defines correct rank ordering</summary>

#### defines correct rank ordering _(slow)_

- defines correct rank ordering
   - Expected: FeatureRank.NATIVE() equals `0`
   - Expected: FeatureRank.BRIDGE() equals `1`
   - Expected: FeatureRank.SECONDARY() equals `2`
   - Expected: FeatureRank.EXTERNAL() equals `3`
   - Expected: FeatureRank.EMULATED() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines correct rank ordering")
expect(FeatureRank.NATIVE()).to_equal(0)
expect(FeatureRank.BRIDGE()).to_equal(1)
expect(FeatureRank.SECONDARY()).to_equal(2)
expect(FeatureRank.EXTERNAL()).to_equal(3)
expect(FeatureRank.EMULATED()).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: native is always preferred over bridge</summary>

#### native is always preferred over bridge _(slow)_

- native is always preferred over bridge
   - Expected: FeatureRank.NATIVE() < FeatureRank.BRIDGE() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("native is always preferred over bridge")
expect(FeatureRank.NATIVE() < FeatureRank.BRIDGE()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: bridge is preferred over emulated</summary>

#### bridge is preferred over emulated _(slow)_

- bridge is preferred over emulated
   - Expected: FeatureRank.BRIDGE() < FeatureRank.EMULATED() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bridge is preferred over emulated")
expect(FeatureRank.BRIDGE() < FeatureRank.EMULATED()).to_equal(true)
```

</details>


</details>

### FeatureId

<details>
<summary>Advanced: covers execution control features</summary>

#### covers execution control features _(slow)_

- covers execution control features
   - Expected: FeatureId.Halt.to_string() equals `Halt`
   - Expected: FeatureId.Resume.to_string() equals `Resume`
   - Expected: FeatureId.SingleStep.to_string() equals `SingleStep`
   - Expected: FeatureId.StepOver.to_string() equals `StepOver`
   - Expected: FeatureId.Reset.to_string() equals `Reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("covers execution control features")
expect(FeatureId.Halt.to_string()).to_equal("Halt")
expect(FeatureId.Resume.to_string()).to_equal("Resume")
expect(FeatureId.SingleStep.to_string()).to_equal("SingleStep")
expect(FeatureId.StepOver.to_string()).to_equal("StepOver")
expect(FeatureId.Reset.to_string()).to_equal("Reset")
```

</details>


</details>

<details>
<summary>Advanced: covers memory features</summary>

#### covers memory features _(slow)_

- covers memory features
   - Expected: FeatureId.ReadMemory.to_string() equals `ReadMemory`
   - Expected: FeatureId.WriteMemory.to_string() equals `WriteMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("covers memory features")
expect(FeatureId.ReadMemory.to_string()).to_equal("ReadMemory")
expect(FeatureId.WriteMemory.to_string()).to_equal("WriteMemory")
```

</details>


</details>

<details>
<summary>Advanced: covers register features</summary>

#### covers register features _(slow)_

- covers register features
   - Expected: FeatureId.ReadRegister.to_string() equals `ReadRegister`
   - Expected: FeatureId.WriteRegister.to_string() equals `WriteRegister`
   - Expected: FeatureId.ReadAllRegisters.to_string() equals `ReadAllRegisters`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("covers register features")
expect(FeatureId.ReadRegister.to_string()).to_equal("ReadRegister")
expect(FeatureId.WriteRegister.to_string()).to_equal("WriteRegister")
expect(FeatureId.ReadAllRegisters.to_string()).to_equal("ReadAllRegisters")
```

</details>


</details>

<details>
<summary>Advanced: covers inspection features</summary>

#### covers inspection features _(slow)_

- covers inspection features
   - Expected: FeatureId.ReadLocals.to_string() equals `ReadLocals`
   - Expected: FeatureId.ReadGlobals.to_string() equals `ReadGlobals`
   - Expected: FeatureId.ReadArguments.to_string() equals `ReadArguments`
   - Expected: FeatureId.EvaluateExpression.to_string() equals `EvaluateExpression`
   - Expected: FeatureId.ReadStackTrace.to_string() equals `ReadStackTrace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("covers inspection features")
expect(FeatureId.ReadLocals.to_string()).to_equal("ReadLocals")
expect(FeatureId.ReadGlobals.to_string()).to_equal("ReadGlobals")
expect(FeatureId.ReadArguments.to_string()).to_equal("ReadArguments")
expect(FeatureId.EvaluateExpression.to_string()).to_equal("EvaluateExpression")
expect(FeatureId.ReadStackTrace.to_string()).to_equal("ReadStackTrace")
```

</details>


</details>

<details>
<summary>Advanced: covers Trace32-unique features</summary>

#### covers Trace32-unique features _(slow)_

- covers Trace32-unique features
   - Expected: FeatureId.FlashProgram.to_string() equals `FlashProgram`
   - Expected: FeatureId.TraceCapture.to_string() equals `TraceCapture`
   - Expected: FeatureId.CoverageCollect.to_string() equals `CoverageCollect`
   - Expected: FeatureId.ProfileSample.to_string() equals `ProfileSample`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("covers Trace32-unique features")
expect(FeatureId.FlashProgram.to_string()).to_equal("FlashProgram")
expect(FeatureId.TraceCapture.to_string()).to_equal("TraceCapture")
expect(FeatureId.CoverageCollect.to_string()).to_equal("CoverageCollect")
expect(FeatureId.ProfileSample.to_string()).to_equal("ProfileSample")
```

</details>


</details>

<details>
<summary>Advanced: supports equality comparison</summary>

#### supports equality comparison _(slow)_

- supports equality comparison
   - Expected: FeatureId.Halt.eq(FeatureId.Halt) is true
   - Expected: FeatureId.Halt.eq(FeatureId.Resume) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports equality comparison")
expect(FeatureId.Halt.eq(FeatureId.Halt)).to_equal(true)
expect(FeatureId.Halt.eq(FeatureId.Resume)).to_equal(false)
```

</details>


</details>

### QEMU Integration

<details>
<summary>Advanced: connects GDB to QEMU and reads registers</summary>

#### connects GDB to QEMU and reads registers _(slow)_

- connects GDB to QEMU and reads registers
   - Expected: regs.keys().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects GDB to QEMU and reads registers")
# BUG-RT: skip() doesn't halt execution and return doesn't work in itlambdas.
# Guard entire test body with availability check.
if is_rv32_qemu_available() and is_rv32_gdb_available() and is_rv32_gcc_available():
    # Build test binary
    val elf_path = "/tmp/simple_test_rv32.elf"
    val build_result = build_rv32_test("test/remote/fixtures/hello_rv32.s", elf_path)
    match build_result:
        Ok(_):
            # Start QEMU
            val qemu_result = QemuRunner.start(elf_path, 11234)
            match qemu_result:
                Ok(qemu):
                    # Connect GDB
                    val config = DebugConfig(
                        host: "localhost",
                        port: 11234,
                        target: Architecture.RiscV32,
                        program: elf_path,
                        options: {}
                    )
                    val backend_result = RemoteRiscV32Backend.gdb_only(config)
                    match backend_result:
                        Ok(backend):
                            # Read all registers
                            val regs_result = backend.read_all_registers()
                            match regs_result:
                                Ok(regs):
                                    expect(regs.keys().len() > 0).to_equal(true)
                                Err(e):
                                    pass  # Skip on error
                            # Cleanup
                            backend.detach()
                        Err(_):
                            pass
                    qemu.stop()
                Err(_):
                    pass
        Err(_):
            pass
else:
    pending("required tools not available (QEMU/GDB/GCC)")
```

</details>


</details>

<details>
<summary>Advanced: sets breakpoint and inspects locals</summary>

#### sets breakpoint and inspects locals _(slow)_

- sets breakpoint and inspects locals
   - Expected: frames.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets breakpoint and inspects locals")
if is_rv32_qemu_available() and is_rv32_gdb_available() and is_rv32_gcc_available():
    val build_result = build_rv32_test("test/remote/fixtures/hello_rv32.s", "/tmp/simple_test_rv32_bp.elf")
    match build_result:
        Ok(elf_path):
            val qemu_result = QemuRunner.start(elf_path, 11235)
            match qemu_result:
                Ok(qemu):
                    val config = DebugConfig(
                        host: "localhost",
                        port: 11235,
                        target: Architecture.RiscV32,
                        program: elf_path,
                        options: {}
                    )
                    val backend_result = RemoteRiscV32Backend.gdb_only(config)
                    match backend_result:
                        Ok(backend):
                            # Set breakpoint and run
                            val bp_result = backend.set_breakpoint_at_addr(0x80000010)
                            backend.run()
                            val trace = backend.stack_trace()
                            match trace:
                                Ok(frames):
                                    expect(frames.len() > 0).to_equal(true)
                                Err(_):
                                    pass
                            backend.detach()
                        Err(_):
                            pass
                    qemu.stop()
                Err(_):
                    pass
        Err(_):
            pass
else:
    pending("required tools not available")
```

</details>


</details>

<details>
<summary>Advanced: verifies feature registry with real GDB</summary>

#### verifies feature registry with real GDB _(slow)_

- verifies feature registry with real GDB
   - Expected: backend.supports(FeatureId.Halt) is true
   - Expected: backend.supports(FeatureId.Resume) is true
   - Expected: backend.supports(FeatureId.ReadLocals) is true
   - Expected: report contains `Halt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifies feature registry with real GDB")
if is_rv32_qemu_available() and is_rv32_gdb_available() and is_rv32_gcc_available():
    val build_result = build_rv32_test("test/remote/fixtures/hello_rv32.s", "/tmp/simple_test_rv32_feat.elf")
    match build_result:
        Ok(elf_path):
            val qemu_result = QemuRunner.start(elf_path, 11236)
            match qemu_result:
                Ok(qemu):
                    val config = DebugConfig(
                        host: "localhost",
                        port: 11236,
                        target: Architecture.RiscV32,
                        program: elf_path,
                        options: {}
                    )
                    val backend_result = RemoteRiscV32Backend.gdb_only(config)
                    match backend_result:
                        Ok(backend):
                            backend.add_emulation()
                            expect(backend.supports(FeatureId.Halt)).to_equal(true)
                            expect(backend.supports(FeatureId.Resume)).to_equal(true)
                            expect(backend.supports(FeatureId.ReadLocals)).to_equal(true)
                            val report = backend.capabilities()
                            expect(report.contains("Halt")).to_equal(true)
                            backend.detach()
                        Err(_):
                            pass
                    qemu.stop()
                Err(_):
                    pass
        Err(_):
            pass
else:
    pending("required tools not available")
```

</details>


</details>

### DebugConfig class methods

#### default_gdb constructor

<details>
<summary>Advanced: sets localhost and port 1234</summary>

#### sets localhost and port 1234 _(slow)_

- sets localhost and port 1234
   - Expected: cfg.host equals `localhost`
   - Expected: cfg.port equals `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets localhost and port 1234")
val cfg = DebugConfig.default_gdb("firmware.elf")
expect(cfg.host).to_equal("localhost")
expect(cfg.port).to_equal(1234)
```

</details>


</details>

<details>
<summary>Advanced: stores the program path</summary>

#### stores the program path _(slow)_

- stores the program path
   - Expected: cfg.program equals `my_app.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores the program path")
val cfg = DebugConfig.default_gdb("my_app.elf")
expect(cfg.program).to_equal("my_app.elf")
```

</details>


</details>

<details>
<summary>Advanced: defaults to RiscV32 architecture</summary>

#### defaults to RiscV32 architecture _(slow)_

- defaults to RiscV32 architecture
   - Expected: arch.to_string() equals `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defaults to RiscV32 architecture")
val cfg = DebugConfig.default_gdb("fw.elf")
val arch = cfg.target
expect(arch.to_string()).to_equal("riscv32")
```

</details>


</details>

#### for_trace32 constructor

<details>
<summary>Advanced: stores the given host and port</summary>

#### stores the given host and port _(slow)_

- stores the given host and port
   - Expected: cfg.host equals `10.0.0.5`
   - Expected: cfg.port equals `20001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores the given host and port")
val cfg = DebugConfig.for_trace32("10.0.0.5", 20001)
expect(cfg.host).to_equal("10.0.0.5")
expect(cfg.port).to_equal(20001)
```

</details>


</details>

<details>
<summary>Advanced: sets backend option to trace32</summary>

#### sets backend option to trace32 _(slow)_

- sets backend option to trace32
   - Expected: backend equals `trace32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets backend option to trace32")
val cfg = DebugConfig.for_trace32("10.0.0.5", 20001)
val backend = cfg.options.get("backend") ?? ""
expect(backend).to_equal("trace32")
```

</details>


</details>

#### for_trace32_gdb constructor

<details>
<summary>Advanced: sets backend option to trace32-gdb</summary>

#### sets backend option to trace32-gdb _(slow)_

- sets backend option to trace32-gdb
   - Expected: backend equals `trace32-gdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets backend option to trace32-gdb")
val cfg = DebugConfig.for_trace32_gdb("192.168.1.1", 3333)
val backend = cfg.options.get("backend") ?? ""
expect(backend).to_equal("trace32-gdb")
```

</details>


</details>

<details>
<summary>Advanced: stores host and port correctly</summary>

#### stores host and port correctly _(slow)_

- stores host and port correctly
   - Expected: cfg.host equals `192.168.1.1`
   - Expected: cfg.port equals `3333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores host and port correctly")
val cfg = DebugConfig.for_trace32_gdb("192.168.1.1", 3333)
expect(cfg.host).to_equal("192.168.1.1")
expect(cfg.port).to_equal(3333)
```

</details>


</details>

### HaltReason enum methods

<details>
<summary>Advanced: formats Breakpoint with address</summary>

#### formats Breakpoint with address _(slow)_

- formats Breakpoint with address
   - Expected: r.to_string() equals `breakpoint at 0x80000010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats Breakpoint with address")
val r = HaltReason.Breakpoint(addr: 0x80000010)
expect(r.to_string()).to_equal("breakpoint at 0x80000010")
```

</details>


</details>

<details>
<summary>Advanced: formats Watchpoint with address</summary>

#### formats Watchpoint with address _(slow)_

- formats Watchpoint with address
   - Expected: r.to_string() equals `watchpoint at 0x20001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats Watchpoint with address")
val r = HaltReason.Watchpoint(addr: 0x20001000)
expect(r.to_string()).to_equal("watchpoint at 0x20001000")
```

</details>


</details>

<details>
<summary>Advanced: formats SingleStep</summary>

#### formats SingleStep _(slow)_

- formats SingleStep
   - Expected: r.to_string() equals `single step`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats SingleStep")
val r = HaltReason.SingleStep
expect(r.to_string()).to_equal("single step")
```

</details>


</details>

<details>
<summary>Advanced: formats Halt</summary>

#### formats Halt _(slow)_

- formats Halt
   - Expected: r.to_string() equals `halt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats Halt")
val r = HaltReason.Halt
expect(r.to_string()).to_equal("halt")
```

</details>


</details>

<details>
<summary>Advanced: formats Exception with code</summary>

#### formats Exception with code _(slow)_

- formats Exception with code
   - Expected: r.to_string() equals `exception 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats Exception with code")
val r = HaltReason.Exception(code: 3)
expect(r.to_string()).to_equal("exception 3")
```

</details>


</details>

### DebugError additional variants

<details>
<summary>Advanced: formats TargetNotHalted</summary>

#### formats TargetNotHalted _(slow)_

- formats TargetNotHalted
   - Expected: e.to_string() equals `target not halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats TargetNotHalted")
val e = DebugError.TargetNotHalted
expect(e.to_string()).to_equal("target not halted")
```

</details>


</details>

<details>
<summary>Advanced: formats InvalidAddress</summary>

#### formats InvalidAddress _(slow)_

- formats InvalidAddress
   - Expected: e.to_string() equals `invalid address: 0xDEAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats InvalidAddress")
val e = DebugError.InvalidAddress(addr: 0xDEAD)
expect(e.to_string()).to_equal("invalid address: 0xDEAD")
```

</details>


</details>

<details>
<summary>Advanced: formats InvalidRegister</summary>

#### formats InvalidRegister _(slow)_

- formats InvalidRegister
   - Expected: e.to_string() equals `invalid register: 99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats InvalidRegister")
val e = DebugError.InvalidRegister(index: 99)
expect(e.to_string()).to_equal("invalid register: 99")
```

</details>


</details>

<details>
<summary>Advanced: formats ProtocolError</summary>

#### formats ProtocolError _(slow)_

- formats ProtocolError
   - Expected: e.to_string() equals `protocol error: unexpected EOF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats ProtocolError")
val e = DebugError.ProtocolError(msg: "unexpected EOF")
expect(e.to_string()).to_equal("protocol error: unexpected EOF")
```

</details>


</details>

<details>
<summary>Advanced: formats NotSupported</summary>

#### formats NotSupported _(slow)_

- formats NotSupported
   - Expected: e.to_string() equals `not supported: flash write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats NotSupported")
val e = DebugError.NotSupported(msg: "flash write")
expect(e.to_string()).to_equal("not supported: flash write")
```

</details>


</details>

### GdbVariable class methods

#### of constructor

<details>
<summary>Advanced: stores name value and type</summary>

#### stores name value and type _(slow)_

- stores name value and type
   - Expected: v.name equals `count`
   - Expected: v.value equals `42`
   - Expected: v.type_name equals `int`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores name value and type")
val v = GdbVariable.of("count", "42", "int")
expect(v.name).to_equal("count")
expect(v.value).to_equal("42")
expect(v.type_name).to_equal("int")
```

</details>


</details>

<details>
<summary>Advanced: defaults num_children to 0</summary>

#### defaults num_children to 0 _(slow)_

- defaults num_children to 0
   - Expected: v.num_children equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defaults num_children to 0")
val v = GdbVariable.of("x", "1", "i32")
expect(v.num_children).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: defaults has_more to false</summary>

#### defaults has_more to false _(slow)_

- defaults has_more to false
   - Expected: v.has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defaults has_more to false")
val v = GdbVariable.of("y", "0", "bool")
expect(v.has_more).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: handles pointer type name</summary>

#### handles pointer type name _(slow)_

- handles pointer type name
   - Expected: v.type_name equals `uint32_t *`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles pointer type name")
val v = GdbVariable.of("ptr", "0x80001000", "uint32_t *")
expect(v.type_name).to_equal("uint32_t *")
```

</details>


</details>

### FeatureHandler class methods

#### of constructor

<details>
<summary>Advanced: stores feat rank and backend_name</summary>

#### stores feat rank and backend_name _(slow)_

- stores feat rank and backend_name
   - Expected: h.rank equals `2`
   - Expected: h.backend_name equals `secondary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores feat rank and backend_name")
val h = FeatureHandler.of(
    FeatureId.Reset, 2, "secondary",
    \args: Ok("reset_ok"),
    "Secondary reset"
)
expect(h.rank).to_equal(2)
expect(h.backend_name).to_equal("secondary")
```

</details>


</details>

<details>
<summary>Advanced: stores description</summary>

#### stores description _(slow)_

- stores description
   - Expected: h.description equals `GDB halt command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores description")
val h = FeatureHandler.of(
    FeatureId.Halt, 0, "gdb",
    \args: Ok("halted"),
    "GDB halt command"
)
expect(h.description).to_equal("GDB halt command")
```

</details>


</details>

<details>
<summary>Advanced: handler_fn returns expected result</summary>

#### handler_fn returns expected result _(slow)_

- handler_fn returns expected result
   - Expected: result.unwrap() equals `resumed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handler_fn returns expected result")
val h = FeatureHandler.of(
    FeatureId.Resume, 0, "gdb",
    \args: Ok("resumed"),
    "GDB continue"
)
val callback = h.handler_fn
val result = callback([])
expect(result.unwrap()).to_equal("resumed")
```

</details>


</details>

<details>
<summary>Advanced: handler_fn can receive args</summary>

#### handler_fn can receive args _(slow)_

- handler_fn can receive args
   - Expected: result.unwrap() equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handler_fn can receive args")
val h = FeatureHandler.of(
    FeatureId.ReadMemory, 0, "gdb",
    \args: Ok(args[0]),
    "GDB read mem"
)
val callback = h.handler_fn
val result = callback(["0x80000000"])
expect(result.unwrap()).to_equal("0x80000000")
```

</details>


</details>

### FeatureRegistry impl methods

#### all_handlers on empty registry

<details>
<summary>Advanced: returns empty list for unknown feature</summary>

#### returns empty list for unknown feature _(slow)_

- returns empty list for unknown feature
   - Expected: handlers.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns empty list for unknown feature")
val registry = FeatureRegistry.empty()
val handlers = registry.all_handlers(FeatureId.TraceCapture)
expect(handlers.len()).to_equal(0)
```

</details>


</details>

#### is_supported after registration

<details>
<summary>Advanced: returns true after registering the feature</summary>

#### returns true after registering the feature _(slow)_

- returns true after registering the feature
   - Expected: registry.is_supported(FeatureId.SingleStep) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns true after registering the feature")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.SingleStep, 0, "gdb",
    \args: Ok("stepped"),
    "GDB single step"
))
expect(registry.is_supported(FeatureId.SingleStep)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns false for an unregistered feature</summary>

#### returns false for an unregistered feature _(slow)_

- returns false for an unregistered feature
   - Expected: registry.is_supported(FeatureId.SingleStep) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns false for an unregistered feature")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb",
    \args: Ok("halted"),
    "GDB halt"
))
expect(registry.is_supported(FeatureId.SingleStep)).to_equal(false)
```

</details>


</details>

#### execute propagates handler result

<details>
<summary>Advanced: returns Ok value from handler</summary>

#### returns Ok value from handler _(slow)_

- returns Ok value from handler
   - Expected: result.unwrap() equals `reset_done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns Ok value from handler")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Reset, 0, "gdb",
    \args: Ok("reset_done"),
    "GDB reset"
))
val result = registry.execute(FeatureId.Reset, [])
expect(result.unwrap()).to_equal("reset_done")
```

</details>


</details>

<details>
<summary>Advanced: returns Err when no handler registered</summary>

#### returns Err when no handler registered _(slow)_

- returns Err when no handler registered
   - Expected: result.err == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns Err when no handler registered")
val registry = FeatureRegistry.empty()
val result = registry.execute(FeatureId.FlashProgram, [])
expect(result.err == nil).to_equal(false)
```

</details>


</details>

#### handler_count across multiple features

<details>
<summary>Advanced: counts handlers across different features</summary>

#### counts handlers across different features _(slow)_

- counts handlers across different features
   - Expected: registry.handler_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("counts handlers across different features")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb", \args: Ok("ok"), "halt"
))
registry.register(FeatureHandler.of(
    FeatureId.Resume, 0, "gdb", \args: Ok("ok"), "resume"
))
registry.register(FeatureHandler.of(
    FeatureId.Reset, 0, "gdb", \args: Ok("ok"), "reset"
))
expect(registry.handler_count()).to_equal(3)
```

</details>


</details>

#### capabilities_report content

<details>
<summary>Advanced: includes all registered feature names</summary>

#### includes all registered feature names _(slow)_

- includes all registered feature names
   - Expected: report contains `ReadMemory`
   - Expected: report contains `WriteMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes all registered feature names")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.ReadMemory, 0, "gdb", \args: Ok("ok"), "Read mem"
))
registry.register(FeatureHandler.of(
    FeatureId.WriteMemory, 0, "gdb", \args: Ok("ok"), "Write mem"
))
val report = registry.capabilities_report()
expect(report.contains("ReadMemory")).to_equal(true)
expect(report.contains("WriteMemory")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: labels native rank handlers as native</summary>

#### labels native rank handlers as native _(slow)_

- labels native rank handlers as native
   - Expected: report contains `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("labels native rank handlers as native")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.Halt, 0, "gdb", \args: Ok("ok"), "GDB halt"
))
val report = registry.capabilities_report()
expect(report.contains("native")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: labels emulated rank handlers as emulated</summary>

#### labels emulated rank handlers as emulated _(slow)_

- labels emulated rank handlers as emulated
   - Expected: report contains `emulated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("labels emulated rank handlers as emulated")
var registry = FeatureRegistry.empty()
registry.register(FeatureHandler.of(
    FeatureId.TraceCapture, 4, "emulation",
    \args: Ok("ok"), "Emulated trace"
))
val report = registry.capabilities_report()
expect(report.contains("emulated")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/integration/baremetal/remote_riscv32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Remote Debug Core Types, RISC-V 32 Target, Feature Registry, GDB MI Parser, Feature Rank Constants, FeatureId, QEMU Integration, DebugConfig class methods, HaltReason enum methods, DebugError additional variants, GdbVariable class methods, FeatureHandler class methods, FeatureRegistry impl methods.
- Remote Debug Core Types
- RISC-V 32 Target
- Feature Registry
- GDB MI Parser
- Feature Rank Constants
- FeatureId
- QEMU Integration
- DebugConfig class methods
- HaltReason enum methods
- DebugError additional variants
- GdbVariable class methods
- FeatureHandler class methods
- FeatureRegistry impl methods

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 85 |
| Active scenarios | 85 |
| Slow scenarios | 85 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `628fcbce62802dd98d7ceff5172734132409243227813e6097dad27bbdfed29b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `628fcbce62802dd98d7ceff5172734132409243227813e6097dad27bbdfed29b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `628fcbce62802dd98d7ceff5172734132409243227813e6097dad27bbdfed29b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/baremetal/remote_riscv32_spec.spl
mirror: doc/06_spec/integration/baremetal/remote_riscv32_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/baremetal/remote_riscv32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/baremetal/remote_riscv32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/baremetal/remote_riscv32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 47 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/baremetal/remote_riscv32_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/baremetal/remote_riscv32_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/baremetal/remote_riscv32_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default GDB config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
