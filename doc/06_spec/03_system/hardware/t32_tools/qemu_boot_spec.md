# QEMU debug-boot helper specification

Source: `test/03_system/hardware/t32_tools/qemu_boot_spec.spl`.
Owner: `src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl`.
Requirement: REQ-SSPEC-SYSTEM. Phase 1 baseline executed five scenarios:
**4 passed, 1 failed** in 274ms. All formatter scenarios passed; the real hex
parser failed with `type mismatch: comparing string with integer`.
Evidence: `build/phase-one-ui-diagnostic/qemu_boot_spec/cycle-one.log` and
`build/phase-one-ui-diagnostic/hardware-helpers-inputs.json`.
The byte-access repair passed the focused hexadecimal scenario **1/1** in
477ms, exit 0. Evidence:
`build/phase-one-ui-diagnostic/qemu-hex-cycle-two_spec/cycle-two.log`, its run
receipts, `build/phase-one-ui-diagnostic/qemu-hex-repair-inputs.json`, and
`build/phase-one-ui-diagnostic/qemu-hex-repair.patch`.
This is four formatter passes at the baseline snapshot plus one parser pass at
the repaired snapshot; the complete five-scenario file was **not rerun**.
Docgen and self-hosted core/MCP checks remain unverified. The 80% annotation
is a target, not measured coverage.

1. Construct `DebugInfo.unavailable()` and require unavailable state, empty
   registers/trace, and the exact unavailable message from `format_debug_info`.
2. Format a populated `StackFrame`, checking frame number, hexadecimal address,
   symbol, file and source line in the complete output.
3. Format a frame with no source file; require the address and symbol without
   a fabricated file/line suffix.
4. Construct available crash information and format it; require the exact fault,
   single register, stack frame, section separators and final newline. Using
   one register avoids relying on dictionary iteration order.
5. Invoke the real `parse_hex_value_u64` on zero, numeric, alphabetic,
   uppercase-prefix/mixed-case, leading-zero, and unprefixed addresses.

Every value under test comes from production helpers. The removed legacy
constant tests, canonical source-text pins, and local hardcoded parser were
not behavioral evidence. No production fallback or local parser replaces the
real implementation if these checks fail.

## Confirmed parser defect and focused repair evidence

The baseline production hex parser called `clean.char_at(i)` then compared it to
numeric character codes 48–57, 97–102 and 65–70. The inspected Phase 1 producer
implementation (`src/compiler_rust/compiler/src/interpreter_method/string.rs`,
`char_at` branch) returns text. The executed failure confirms the mismatch.
The repair uses `byte_at(i)`, matching numeric ASCII digit ranges and the
byte-count loop bound. It preserves the permissive accumulator: an unrecognized
byte contributes a zero nibble; invalid input is not rejected, and overflow
has no explicit check. These behaviors are documented limitations, not newly
validated contracts. No GDB stubs or unrelated runtime code were changed.
Details: `doc/08_tracking/bug/qemu_debug_hex_char_at_type_mismatch_2026-10-11.md`.

The imported owner reaches `std.qemu.mod` and `std.qemu.boot_runner`, located
under `src/lib/nogc_async_mut_noalloc/qemu/`, and the process facade
`std.nogc_sync_mut.io.process_ops`. Its `GdbMiParser`/`GdbMiClient` currently
contain empty/hardcoded method bodies. These scenarios do not call those
methods and cannot prove GDB parsing, attach, remote commands or crash capture.
If dependency resolution or owner parsing blocks execution, preserve the error;
do not replace it with source inspection or local simulations.

## Remaining live scope

QEMU boot, real GDB transport, breakpoints, register acquisition and crash
extraction remain **unverified**. These in-memory formatter/parser contracts
are a focused part of the original debug-boot intent, not whole boot completion.
No binary/protocol capture is claimed.

Use an admitted producer appropriate to the requested bootstrap phase; ordinary
tooling uses the source-matched self-hosted CLI. Do not present source discovery
or a load-only check as executed examples. Then run
`simple spipe-docgen test/03_system/hardware/t32_tools/qemu_boot_spec.spl --output doc/06_spec --no-index` and require zero stubs.

<details>
<summary>Executable SSpec</summary>

```simple
"""
QEMU debug-boot helper contracts for debugger maintainers. These scenarios call
the actual debug-information formatter, stack-frame formatter, and hex parser.
They do not launch QEMU or attach GDB. Runtime and docgen are UNRUN; dependency
or owner failures must be recorded rather than replaced with source searches
or a local parser. Live boot, GDB transport and crash extraction remain open.
"""
# codex-system-test
# @tag:system
# @req REQ-SSPEC-SYSTEM
# @manual_section: qemu boot runner smoke
# @cover src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl 80%
# Coverage percentage is a target, not a measured result.
# Lifecycle: doc/01_research/domain/sspec_documentization_maintenance.md ; doc/03_plan/sspec_modernization_plan.md ; doc/04_architecture/sspec_documentization_maintenance.md ; doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md

use std.spec.{describe, it, expect, step}
use std.nogc_async_mut_noalloc.qemu.debug_boot_runner.{DebugInfo, StackFrame, format_debug_info, parse_hex_value_u64}

describe "QEMU debug boot runner portable smoke":
    it "should format unavailable debug information without fabricating a trace":
        step("Construct unavailable debug information")
        val info = DebugInfo.unavailable()
        expect(info.available).to_equal(false)
        expect(info.registers.len()).to_equal(0)
        expect(info.stack_trace.len()).to_equal(0)
        step("Format the unavailable result")
        expect(format_debug_info(info)).to_equal("Debug information not available")

    it "should format a source-backed stack frame with its numeric address":
        step("Format a real stack-frame value with source location")
        val frame = StackFrame(frame_num: 2, address: 4660, function: "kernel_main", file: "kernel.spl", line: 37)
        expect(frame.to_string()).to_equal("#2 0x1234 in kernel_main at kernel.spl:37")

    it "should omit the source location for a frame without a file":
        step("Format a stack frame without source information")
        val frame = StackFrame(frame_num: 0, address: 255, function: "reset_handler", file: "", line: 0)
        expect(frame.to_string()).to_equal("#0 0xff in reset_handler")

    it "should format fault registers and stack frames from supplied debug data":
        step("Build available crash information from concrete values")
        val frame = StackFrame(frame_num: 0, address: 4660, function: "kernel_main", file: "kernel.spl", line: 37)
        val info = DebugInfo.from_gdb({"pc": 4660}, [frame], 4660, "breakpoint")
        expect(info.available).to_equal(true)
        step("Inspect the formatted fault register and stack sections")
        val output = format_debug_info(info)
        expect(output).to_equal("Fault Address: 0x1234\nFault Reason: breakpoint\n\nRegisters:\n  pc: 0x1234\n\nStack Trace:\n  #0 0x1234 in kernel_main at kernel.spl:37\n")

    it "should parse numeric and alphabetic hexadecimal digits through the owner":
        step("Parse prefixed unprefixed and mixed-case hexadecimal addresses")
        expect(parse_hex_value_u64("0x0")).to_equal(0)
        expect(parse_hex_value_u64("0x1234")).to_equal(4660)
        expect(parse_hex_value_u64("ff")).to_equal(255)
        expect(parse_hex_value_u64("0XAbCd")).to_equal(43981)
        expect(parse_hex_value_u64("000f")).to_equal(15)
        expect(parse_hex_value_u64("7f00")).to_equal(32512)
```

</details>
