# Leak check owner imports

- Executable spec: `test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl`
- Source SHA-256: `a540fb3f52bf92b47ec0f664a45644b1fc587c5618c8b8c6ff987a6aa084ca9a`
- Manual status: hand-maintained source mirror; no test-run receipt is asserted.
- Scenarios: 4 active, 0 skipped, 0 pending.

## Scope

These scenarios inspect the checked-in leak-check owner and runner sources. They assert import and file-read contracts; they do not execute a leak-check run.

## Shared setup

The following imports and helpers are part of the executable spec. Each scenario below reproduces its source block exactly.

```simple
# Purpose and audience: executable specification evidence for the owning engineering team.
# @req REQ-SSPEC-COMPILER
# research: doc/01_research/domain/sspec_documentization_maintenance.md ; plan: doc/03_plan/sspec_modernization_plan.md ; architecture: doc/04_architecture/sspec_documentization_maintenance.md ; design: doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md




"""
# Leak Check Owner Imports Contract

The Stage4 closure must resolve leak-check runtime types and driver calls from
their concrete owner modules rather than through multi-hop facades; the runtime
observable of that contract is that the tracker operations and entry type,
imported from those owners, work end to end.
"""

use std.spec.step

extern fn rt_file_read_text(path: text) -> text?
```

## Scenarios

### 1. imports the interpreter call and result type from concrete owners

Pins the interpreter bridge and CompileResult imports to their concrete owners.

```simple
    it "imports the interpreter call and result type from concrete owners":
        # @req REQ-SSPEC-COMPILER
        step("imports the interpreter call and result type from concrete owners")
        val source = rt_file_read_text("src/compiler/90.tools/leak_check/main.spl") ?? ""
        expect(source).to_contain("use compiler.driver.driver_public_interpret_bridge.\{interpret_file\}")
        expect(source).to_contain("use compiler.common.driver_core_types.\{CompileResult\}")
        expect(source).to_not_contain("use compiler.driver.\{interpret_file, CompileResult\}")
```

### 2. imports MemLeakEntry directly while retaining adjacent tracker operations

Pins MemLeakEntry to the synchronous tracker type while keeping tracker operations separate.

```simple
    it "imports MemLeakEntry directly while retaining adjacent tracker operations":
        # @req REQ-SSPEC-COMPILER
        step("imports MemLeakEntry directly while retaining adjacent tracker operations")
        val source = rt_file_read_text("src/compiler/90.tools/leak_check/main.spl") ?? ""
        expect(source).to_contain("use std.nogc_sync_mut.mem_tracker.types.\{MemLeakEntry\}")
        expect(source).to_contain("mem_enable, mem_disable, mem_snapshot, mem_dump_leaks, parse_leak_dump")
        expect(source.contains("parse_leak_dump, MemLeakEntry")).to_equal(false)
```

### 3. routes runner file reads through the canonical runtime facade

Checks that four runner files use the canonical I/O facade and omit direct file externs.

```simple
    it "routes runner file reads through the canonical runtime facade":
        val growth = read_file_text("src/compiler/90.tools/leak_check/growth_runner.spl")
        val static_runner = read_file_text("src/compiler/90.tools/leak_check/static_runner.spl")
        val internal = read_file_text("src/compiler/90.tools/leak_check/internal_runner.spl")
        val external = read_file_text("src/compiler/90.tools/leak_check/external_runner.spl")

        expect(growth).to_contain(r"use std.io_runtime.{file_exists, read_file_text}")
        expect(static_runner).to_contain(r"use std.io_runtime.{file_exists, read_file_text}")
        expect(internal).to_contain(r"use std.io_runtime.{file_exists, read_file_text}")
        expect(external).to_contain(r"use std.io_runtime.{file_exists}")
        expect(growth.contains("extern fn rt_file_exists")).to_equal(false)
        expect(growth.contains("extern fn rt_file_read_text")).to_equal(false)
        expect(static_runner.contains("extern fn rt_file_exists")).to_equal(false)
        expect(static_runner.contains("extern fn rt_file_read_text")).to_equal(false)
        expect(internal.contains("extern fn rt_file_exists")).to_equal(false)
        expect(internal.contains("extern fn rt_file_read_text")).to_equal(false)
        expect(external.contains("extern fn rt_file_exists")).to_equal(false)
        expect(external.contains("extern fn rt_file_read_text")).to_equal(false)
```

### 4. preserves facade file-existence and text-read behavior

Checks the named runner fixture exists and its text can be read through the facade.

```simple
    it "preserves facade file-existence and text-read behavior":
        val path = "src/compiler/90.tools/leak_check/growth_runner.spl"
        expect(file_exists(path)).to_equal(true)
        expect(read_file_text(path)).to_contain("Leak Check - Growth Runner")
```

## Verification

Run `test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl` with the admitted Simple test runner and require an actual nonzero-execution `Results:` receipt. This manual records the source contract only; it does not claim that run has passed.
