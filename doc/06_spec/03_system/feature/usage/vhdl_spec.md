# VHDL Process-Facade Toolchain Acceptance

> Operator manual mirrored from
> `test/03_system/feature/usage/vhdl_spec.spl`. It verifies the exact
> pure-Simple process-facade lane used by the GHDL/Yosys wrappers.

| Field | Value |
|---|---|
| Feature | `#VHDL-002` |
| Requirement | `REQ-VHDL-SFFI-001` |
| Evidence class | qualified host-tool execution |
| Executable scenarios | 3 |
| Runtime status, 2026-08-16 | `TEST_BLOCKED` — no admitted full CLI with `test`, `spipe-docgen`, and `sspec-maintain` is available |
| Manual status | manually synchronized; docgen must replace/confirm it when an admitted CLI is available |

## Purpose and audience

This manual is for compiler and hardware-tooling maintainers validating that
`std.nogc_async_mut.io.vhdl_sffi` reaches the canonical
`std.nogc_sync_mut.io.process_ops.process_run` owner. A green run proves that
successful and failing GHDL processes preserve exit status and captured output.
It does not prove generated RTL correctness, FPGA synthesis, or board behavior.

## Preconditions

1. Use an admitted pure-Simple full CLI. A Rust seed, bootstrap-only CLI, or
   unadmitted binary is not evidence.
2. Install `ghdl` and `yosys` on `PATH`.
3. Set `SIMPLE_VHDL_TEST=1`.

If qualification is absent, the tool-backed scenarios print `TEST_BLOCKED`,
fail the `ready` matcher, and return before invoking host tools. Missing
qualification can never become a passing skip.

## Operator workflow

```sh
SIMPLE_VHDL_TEST=1 SIMPLE_TIMEOUT_SECONDS=3600 \
  <admitted-simple> test test/03_system/feature/usage/vhdl_spec.spl

<admitted-simple> spipe-docgen \
  test/03_system/feature/usage/vhdl_spec.spl \
  --output doc/06_spec --no-index

<admitted-simple> sspec-maintain scan \
  test/03_system/feature/usage/vhdl_spec.spl
```

Accept only a nonzero scenario count, zero failures/drops, docgen `0 stubs`, a
current mirror, and no `SSDOC-*` blocker. Any missing command, unresolved
extern, timeout, signal exit, absent verdict, or host-tool failure is FAIL or
`TEST_BLOCKED`, never PASS.

## Scenario flow

### 1. Positive — analyze valid VHDL through the qualified facade

1. `step("Require the qualified VHDL toolchain environment")`
   - Require `test_env_require("SIMPLE_VHDL_TEST") == "ready"`.
2. `step("Demand truthful GHDL and Yosys availability probes")`
   - Require both availability wrappers to return `true`.
3. `step("Create an isolated GHDL work directory and valid VHDL source")`
   - Create `/tmp/ghdl_work`, write a minimal entity/architecture, then read it
     back byte-for-byte.
4. `step("Analyze the source and preserve the successful exit result")`
   - Require `success == true` and `exit_code == 0`.

### 2. Edge — preserve exact empty and populated streams

1. `step("Construct a zero-exit result with intentionally empty streams")`
   - Require success, code `0`, and exact empty stdout/stderr.
2. `step("Construct a nonzero result with output on both captured streams")`
   - Require failure, code `7`, exact stdout, and the stderr diagnostic.

This host-independent case keeps tuple-to-record mapping reviewable even before
the qualified tool environment is admitted.

### 3. Error — reject invalid VHDL with retained diagnostics

1. `step("Require the qualified VHDL toolchain environment")`.
2. `step("Write deliberately invalid VHDL without substituting a mock tool")`.
3. `step("Demand fail-closed status, nonzero exit, and retained diagnostics")`.
   - Require `success == false`, `exit_code > 0`, and combined captured output
     length greater than zero.

## Requirement traceability

| Requirement | Positive | Edge | Error | Coverage |
|---|---|---|---|---|
| `REQ-VHDL-SFFI-001` | qualified GHDL/Yosys probes and valid analysis | exact quiet/noisy result mapping | invalid VHDL, nonzero code, diagnostic | Prepared; execution `TEST_BLOCKED` |

## Evidence and provenance

- Executable source: `test/03_system/feature/usage/vhdl_spec.spl`
- Canonical owner: `src/lib/nogc_sync_mut/io/vhdl_sffi.spl`
- Process facade: `src/lib/nogc_sync_mut/io/process_ops.spl`
- Test plan: `doc/03_plan/sys_test/vhdl_process_facade.md`
- Lane state: `.spipe/vhdl-gen-backend/state.md`
- Runtime evidence: none accepted in this documentation-only follow-up; the
  previously admitted native implementation probe does not substitute for the
  new SSpec/docgen/maintainer run.

## Compatibility and limitations

- `/tmp/ghdl_work` is a hosted-test workspace, not a synthesis artifact.
- `yosys_available()` proves executable discovery only; the GHDL Yosys plugin
  synthesis path is outside `REQ-VHDL-SFFI-001`.
- The manual is intentionally marked manually synchronized until qualified
  docgen runs. Do not relabel `TEST_BLOCKED` as generated or passing evidence.

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-VHDL-SFFI-001
use std.spec.*
use std.common.test_env_gate.{test_env_require}
use std.nogc_sync_mut.io.dir_ops.{dir_create_all}
use std.nogc_async_mut.io.vhdl_sffi.{
    ghdl_available, yosys_available, ghdl_analyze,
    vhdl_tool_result, vhdl_write_file, vhdl_read_file, vhdl_file_exists
}

fn qualified_vhdl_environment_status() -> text:
    val status = test_env_require("SIMPLE_VHDL_TEST")
    if status != "ready":
        print("TEST_BLOCKED: set SIMPLE_VHDL_TEST=1 and provide admitted GHDL/Yosys tooling")
    status

describe "REQ-VHDL-SFFI-001: canonical captured process results":
    it "should analyze valid VHDL through the qualified process facade":
        step("Require the qualified VHDL toolchain environment")
        val environment_status = qualified_vhdl_environment_status()
        expect(environment_status).to_equal("ready")
        if environment_status != "ready": return
        step("Demand truthful GHDL and Yosys availability probes")
        expect(ghdl_available()).to_equal(true)
        expect(yosys_available()).to_equal(true)
        step("Create an isolated GHDL work directory and valid VHDL source")
        expect(dir_create_all("/tmp/ghdl_work")).to_equal(true)
        val path = "/tmp/simple_vhdl_process_facade_positive.vhd"
        val source = "entity process_facade_positive is end entity; architecture rtl of process_facade_positive is begin end architecture;"
        expect(vhdl_write_file(path, source)).to_equal(true)
        expect(vhdl_file_exists(path)).to_equal(true)
        expect(vhdl_read_file(path).unwrap()).to_equal(source)
        step("Analyze the source and preserve the successful exit result")
        val result = ghdl_analyze(path)
        expect(result.success).to_equal(true)
        expect(result.exit_code).to_equal(0)

    it "should preserve exact edge-case streams in VhdlToolResult":
        step("Construct a zero-exit result with intentionally empty streams")
        val quiet = vhdl_tool_result(0, "", "")
        expect(quiet.success).to_equal(true)
        expect(quiet.exit_code).to_equal(0)
        expect(quiet.stdout).to_equal("")
        expect(quiet.stderr).to_equal("")
        step("Construct a nonzero result with output on both captured streams")
        val noisy = vhdl_tool_result(7, "partial output", "analysis error")
        expect(noisy.success).to_equal(false)
        expect(noisy.exit_code).to_equal(7)
        expect(noisy.stdout).to_equal("partial output")
        expect(noisy.stderr).to_contain("analysis error")

    it "should reject invalid VHDL with a nonzero code and captured diagnostic":
        step("Require the qualified VHDL toolchain environment")
        val environment_status = qualified_vhdl_environment_status()
        expect(environment_status).to_equal("ready")
        if environment_status != "ready": return
        step("Write deliberately invalid VHDL without substituting a mock tool")
        expect(dir_create_all("/tmp/ghdl_work")).to_equal(true)
        val path = "/tmp/simple_vhdl_process_facade_error.vhd"
        expect(vhdl_write_file(path, "this is not valid VHDL at all;")).to_equal(true)
        step("Demand fail-closed status, nonzero exit, and retained diagnostics")
        val result = ghdl_analyze(path)
        expect(result.success).to_equal(false)
        expect(result.exit_code).to_be_greater_than(0)
        val diagnostic = result.stdout + result.stderr
        expect(diagnostic.len()).to_be_greater_than(0)
```

</details>
