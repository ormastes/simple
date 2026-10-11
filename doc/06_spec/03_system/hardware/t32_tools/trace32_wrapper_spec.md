# TRACE32 configuration and registry specification

Source: `test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl`.
Owners: `src/lib/nogc_sync_mut/debug/remote/types.spl` and
`src/lib/nogc_sync_mut/debug/remote/feature/features.spl`.
Requirement: REQ-SSPEC-SYSTEM. Phase 1 baseline executed **4/4 PASS** in 244ms.
Evidence: `build/phase-one-ui-diagnostic/trace32_wrapper_spec/cycle-one.log` and
`build/phase-one-ui-diagnostic/hardware-helpers-inputs.json`. This producer-bound
result is not native/release qualification; docgen remains unverified.
The 80% coverage annotations are targets, not measurements.

1. Create the native TRACE32 configuration through `DebugConfig.for_trace32`.
   Require preserved host/port, native backend selection, ARM32 and empty program.
2. Create the GDB bridge configuration through `for_trace32_gdb`; require its
   distinct backend token with the specified host/port and ARM32 architecture.
3. Convert actual trace/coverage feature enum values to names and numeric IDs,
   then resolve IDs 40 and 41 back to their names.
4. Read actual native/bridge ranks and require native priority to precede bridge.

The removed legacy file only asserted local constants. Native/bridge tokens
and architecture now come from production factories, and feature assertions
call production conversions. Its asserted 30,000ms timeout is **unverified**:
these configuration factories have no timeout field. This does not establish
wrapper timeout behavior, connection success, feature execution, or live probe
coverage. No protocol capture was produced by these in-memory checks.

The existing design references remain relevant context:
`doc/04_architecture/hardware/t32_terminal_power_remote.md` and
`doc/05_design/hardware/t32_terminal_power_remote.md`. Their remote terminal,
power and transport obligations are not closed by this registry/configuration
spec. A live TRACE32 probe or t32rem/GDB bridge remains separate evidence.

Use an admitted producer appropriate to the requested bootstrap phase; ordinary
tooling uses the source-matched self-hosted CLI. The Rust seed is not the normal
user command. Record actual executed examples separately from source discovery.
Then run `simple spipe-docgen test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl --output doc/06_spec --no-index` and require zero stubs.

<details>
<summary>Executable SSpec</summary>

```simple
"""
Hardware-free TRACE32 configuration and feature-registry checks for debugger
maintainers. Calls production config factories and feature conversions without
opening a probe, t32rem process, or GDB bridge. Live wrapper/protocol behavior
and timeout enforcement remain unverified. Runtime and docgen are UNRUN.
"""
# codex-system-test
# @tag:system
# @req REQ-SSPEC-SYSTEM
# @manual_section: trace32 wrapper portable smoke
# @cover src/lib/nogc_sync_mut/debug/remote/feature/features.spl 80%
# @cover src/lib/nogc_sync_mut/debug/remote/types.spl 80%
# Coverage percentages are targets, not measured results.
# research: doc/01_research/hardware/t32/trace32_remote_interfaces_2026-03-08.md ; plan: doc/03_plan/sspec_modernization_plan.md ; architecture: doc/04_architecture/hardware/t32_terminal_power_remote.md ; design: doc/05_design/hardware/t32_terminal_power_remote.md

use std.spec.{describe, it, expect, step}
use std.nogc_sync_mut.debug.remote.feature.features.{FeatureId, FeatureRank}
use std.nogc_sync_mut.debug.remote.types.{DebugConfig}

describe "Trace32 wrapper portable smoke":
    it "should preserve native connection parameters and ARM32 configuration":
        step("Create the native TRACE32 configuration")
        val config = DebugConfig.for_trace32("debug-host", 20000)
        expect(config.host).to_equal("debug-host")
        expect(config.port).to_equal(20000)
        expect(config.options["backend"]).to_equal("trace32")
        expect(config.target.to_string()).to_equal("arm32")
        expect(config.program).to_equal("")

    it "should select the GDB bridge without losing connection parameters":
        step("Create the TRACE32 GDB bridge configuration")
        val config = DebugConfig.for_trace32_gdb("bridge-host", 2345)
        expect(config.host).to_equal("bridge-host")
        expect(config.port).to_equal(2345)
        expect(config.options["backend"]).to_equal("trace32-gdb")
        expect(config.target.to_string()).to_equal("arm32")

    it "should round-trip trace capture and coverage feature identities":
        step("Read feature names and numeric registry identities")
        expect(FeatureId.TraceCapture.to_string()).to_equal("TraceCapture")
        expect(FeatureId.CoverageCollect.to_string()).to_equal("CoverageCollect")
        expect(FeatureId.TraceCapture.to_i32()).to_equal(40)
        expect(FeatureId.CoverageCollect.to_i32()).to_equal(41)
        step("Resolve numeric identities back to feature names")
        val trace = FeatureId.from_i32(40)
        val coverage = FeatureId.from_i32(41)
        expect(trace.to_string()).to_equal("TraceCapture")
        expect(coverage.to_string()).to_equal("CoverageCollect")

    it "should prioritize native handlers before bridge handlers":
        step("Inspect the registry's handler priority ranks")
        expect(FeatureRank.NATIVE()).to_equal(0)
        expect(FeatureRank.BRIDGE()).to_equal(1)
        expect(FeatureRank.NATIVE()).to_be_less_than(FeatureRank.BRIDGE())
```

</details>
