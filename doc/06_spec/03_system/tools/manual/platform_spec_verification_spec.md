# Platform specification verification

Source: `test/03_system/tools/manual/platform_spec_verification_spec.spl`.
Requirement: REQ-SSPEC-SYSTEM.
Production owner: `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`,
imported through the existing `std.test_runner.test_runner_types` interface.

Status: **All seven scenarios have passing Phase1 seed diagnostic evidence
across two attempts**. The first full-file attempt passed six and failed the
composite scenario because its binding named `spec` resolved to the imported
module namespace. After renaming that binding to `platform_text`, the exact
extracted failing case passed 1/1 in 365 ms. The other six scenarios were
unchanged and were not rerun; this is evidence across two source snapshots,
not a seven-case pass from one full-file run. Native acceptance and SPipe docgen
validation remain pending. The 80% annotation is a target, not measured coverage.

Baseline: `build/phase-one-ui-diagnostic/platform_spec_verification_spec/cycle-one.log`.
Focused rerun: `build/phase-one-ui-diagnostic/platform-binding-cycle-two_spec/cycle-two.log`
and its receipts. `build/phase-one-ui-diagnostic/platform-daemon-cycle-two-inputs.json`
binds the canonical and selected spec inputs. This manual mirrors the source.

## Manual scenarios

1. **Construct a composite variant.** Parse
   `interpreter(remote(baremetal(riscv32)))` through the production helper.
   Require the composite tag, match its actual enum payload, and round-trip the
   complete specification.
2. **Construct a simple interpreter.** Parse `interpreter`. Require the
   Interpreter variant, simple classification, base runtime, canonical name,
   host architecture, and no remote/bare-metal/container layers.
3. **Extract a composite runtime.** Parse a padded
   `smf (container(x86_64))`. Require a trimmed runtime name, preserved inner
   payload spacing, composite classification, and x86_64 architecture.
4. **Inspect nested layers.** Parse the original remote bare-metal RISC-V
   specification and require the runtime, remote and bare-metal layers, RISC-V32
   architecture, and absence of a container layer.
5. **Normalize simple modes.** Parse padded mixed-case native, SMF, and compile
   names. Require the actual corresponding enum variants and canonical names.
6. **Distinguish container execution.** Parse `native(container(linux))`.
   Require the container layer, no remote/bare-metal layers, native runtime,
   and host fallback when no recognized architecture is supplied.
7. **Retain unsupported-input fallback.** Parse empty, whitespace-only, and
   unknown plain names. Require the existing Interpreter fallback, simple
   classification, canonical name, and host architecture.

There are no test-owned parsing helpers or indexed array accesses. Every
observation comes from the production mode parser or its inspection helpers.
The byte-identical legacy spec was removed after all four original topics
(composite variant, simple mode, runtime extraction, nested layers) were
subsumed by these behavioral scenarios.

## Error boundary and remaining work

The production API returns `TestExecutionMode`, not `Result`; its negative-input
contract for unknown plain names is fallback, not an error diagnostic.
Malformed nested syntax is not validated, and layer detection uses substring
matching. This spec neither codifies those false positives as correct behavior
nor claims grammar validation is complete.

Concrete tracked source issue:
`doc/08_tracking/bug/platform_spec_composite_validation_gap_2026-10-11.md`.
No product source was changed in this repair.

The separate producer binding collision and original 6/7 diagnostic are retained
in `doc/08_tracking/bug/platform_spec_pattern_binding_module_collision_2026-10-11.md`.
Renaming the local payload avoids that known producer defect; it does not fix
the compiler or demonstrate malformed platform grammar rejection.

A future admitted Phase1 seed run is diagnostic evidence only. Compiled/native
acceptance, target availability, remote execution, container execution and
bare-metal execution are separate obligations; parser results prove none of
those environments ran.

<details>
<summary>Executable SSpec</summary>

```simple
# Purpose and audience: production platform-spec helpers for test-runner maintainers.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/nogc_sync_mut/test_runner/test_runner_types.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# research: doc/01_research/domain/sspec_documentization_maintenance.md ; plan: doc/03_plan/sspec_modernization_plan.md ; architecture: doc/04_architecture/sspec_documentization_maintenance.md ; design: doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md
# bug: doc/08_tracking/bug/platform_spec_composite_validation_gap_2026-10-11.md
# producer bug: doc/08_tracking/bug/platform_spec_pattern_binding_module_collision_2026-10-11.md
# Host diagnostic scope: parse and inspect modes, not execute remote targets.

use std.spec.{describe, it, expect, step, fail}
use std.test_runner.test_runner_types.{
    TestExecutionMode,
    execution_mode_from_string,
    execution_mode_base_runtime,
    execution_mode_is_composite,
    execution_mode_has_layer,
    execution_mode_is_remote,
    execution_mode_is_baremetal,
    execution_mode_is_container,
    execution_mode_target_arch,
    execution_mode_to_string
}

describe "Platform specification production helpers":
    # @manual scenario evidence
    it "should construct a composite enum carrying the complete nested specification":
        step("Parse a nested remote bare-metal platform specification")
        val mode = execution_mode_from_string("interpreter(remote(baremetal(riscv32)))")
        expect(execution_mode_is_composite(mode)).to_equal(true)
        step("Inspect the composite variant payload")
        match mode:
            TestExecutionMode.Composite(platform_text):
                expect(platform_text).to_equal("interpreter(remote(baremetal(riscv32)))")
            _:
                fail("Expected a composite execution mode carrying the parsed specification")
        expect(execution_mode_to_string(mode)).to_equal("interpreter(remote(baremetal(riscv32)))")

    it "should construct the simple interpreter variant without composite layers":
        step("Parse a simple interpreter mode")
        val mode = execution_mode_from_string("interpreter")
        expect(mode).to_equal(TestExecutionMode.Interpreter)
        expect(execution_mode_is_composite(mode)).to_equal(false)
        expect(execution_mode_base_runtime(mode)).to_equal("interpreter")
        expect(execution_mode_to_string(mode)).to_equal("interpreter")
        expect(execution_mode_target_arch(mode)).to_equal("host")
        expect(execution_mode_is_remote(mode)).to_equal(false)
        expect(execution_mode_is_baremetal(mode)).to_equal(false)
        expect(execution_mode_is_container(mode)).to_equal(false)

    it "should extract the runtime while preserving nested payload text":
        step("Parse a whitespace-padded composite mode")
        val mode = execution_mode_from_string("  smf (container(x86_64))  ")
        expect(execution_mode_base_runtime(mode)).to_equal("smf")
        expect(execution_mode_is_composite(mode)).to_equal(true)
        expect(execution_mode_to_string(mode)).to_equal("smf (container(x86_64))")
        expect(execution_mode_target_arch(mode)).to_equal("x86_64")

    it "should detect the remote bare-metal layers and target architecture":
        step("Inspect the parsed remote bare-metal platform")
        val mode = execution_mode_from_string("interpreter(remote(baremetal(riscv32)))")
        expect(execution_mode_base_runtime(mode)).to_equal("interpreter")
        expect(execution_mode_has_layer(mode, "remote")).to_equal(true)
        expect(execution_mode_has_layer(mode, "baremetal")).to_equal(true)
        expect(execution_mode_is_remote(mode)).to_equal(true)
        expect(execution_mode_is_baremetal(mode)).to_equal(true)
        expect(execution_mode_is_container(mode)).to_equal(false)
        expect(execution_mode_target_arch(mode)).to_equal("riscv32")

    it "should normalize case and whitespace for all simple runtime modes":
        step("Parse normalized simple runtime names")
        val native_mode = execution_mode_from_string("  NaTiVe  ")
        expect(native_mode).to_equal(TestExecutionMode.Native)
        expect(execution_mode_base_runtime(native_mode)).to_equal("native")
        expect(execution_mode_to_string(native_mode)).to_equal("native")
        expect(execution_mode_is_composite(native_mode)).to_equal(false)
        val smf_mode = execution_mode_from_string(" SMF ")
        expect(smf_mode).to_equal(TestExecutionMode.Smf)
        expect(execution_mode_base_runtime(smf_mode)).to_equal("smf")
        val compile_mode = execution_mode_from_string(" COMPILE ")
        expect(compile_mode).to_equal(TestExecutionMode.Compile)
        expect(execution_mode_to_string(compile_mode)).to_equal("compile")

    it "should distinguish a container from remote and bare-metal layers":
        step("Parse a container platform without a recognized architecture")
        val mode = execution_mode_from_string("native(container(linux))")
        expect(execution_mode_is_container(mode)).to_equal(true)
        expect(execution_mode_is_remote(mode)).to_equal(false)
        expect(execution_mode_is_baremetal(mode)).to_equal(false)
        expect(execution_mode_has_layer(mode, "remote")).to_equal(false)
        expect(execution_mode_base_runtime(mode)).to_equal("native")
        expect(execution_mode_target_arch(mode)).to_equal("host")

    it "should retain interpreter fallback for empty and unknown plain modes":
        step("Parse empty whitespace-only and unknown plain runtime names")
        for mode_text in ["", "   ", "unknown-runtime"]:
            val mode = execution_mode_from_string(mode_text)
            expect(mode).to_equal(TestExecutionMode.Interpreter)
            expect(execution_mode_base_runtime(mode)).to_equal("interpreter")
            expect(execution_mode_is_composite(mode)).to_equal(false)
            expect(execution_mode_to_string(mode)).to_equal("interpreter")
            expect(execution_mode_target_arch(mode)).to_equal("host")
```

</details>
