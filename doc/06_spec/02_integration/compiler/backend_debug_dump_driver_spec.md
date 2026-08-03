# Backend Debug Dump Driver Integration

> Exercise the public native-build CLI boundary for the ten compiler artifact stages without treating a requested name, output path, or silent omission as evidence that a layer ran.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Debug Dump Driver Integration

Exercise the public native-build CLI boundary for the ten compiler artifact stages without treating a requested name, output path, or silent omission as evidence that a layer ran.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/02_requirements/feature/backend_layer_artifact_matrix.md |
| Plan | doc/03_plan/sys_test/backend_layer_artifact_matrix.md |
| Design | doc/05_design/backend_layer_artifact_matrix.md |
| Research | N/A |
| Source | `test/02_integration/compiler/backend_debug_dump_driver_spec.spl` |
| Updated | 2026-08-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercise the public native-build CLI boundary for the ten compiler artifact
stages without treating a requested name, output path, or silent omission as
evidence that a layer ran.

## Purpose

Keep the current unsupported state explicit while making the eventual six
shared-stage implementation prove real intermediate content. The test also
prevents `--debug-dump=all` from succeeding while silently omitting later
backend artifacts.

## Audience

Compiler, bootstrap, and release engineers use this specification when adding
or reviewing layered debug-artifact hooks.

## Preconditions

Run from the repository root with a full CLI capable of the integration test
runner. The fixture is intentionally small and local; no GPU, network, or
whole-compiler bootstrap is required.

## Examples

The shared request selects `source,ast,hir,monomorphized-hir,mir,optimized-mir`.
The full request adds `backend-ir,object,linked-binary,run-readback-receipt`.
The adjacent negative request uses `source,,mir` and must not start a partial
build.

## Claim boundaries

On the current public surface, `--debug-dump` is unsupported. That state is
accepted only as an exact configuration failure with no output and every cell
accounted as `FAIL`. Once the option is supported, Source through Optimized MIR
may pass only with real nonempty content-bearing artifacts. Backend IR, Object,
Linked Binary, and Run/Readback Receipt remain required failures until typed
validators and producer hooks exist; binary presence alone is `UNVALIDATED`,
never `PASS` or `SKIP`.

## Scenarios

### backend debug dump driver integration

#### accounts for Source through Optimized MIR without false artifact passes

- compile the layered backend fixture
   - Expected: dir_create_all(root) is true
   - Expected: file_write(source, fixture_source()) is true
   - Expected: result equals `0`
   - Expected: file_exists(output) is true
   - Expected: option_error equals `unknown option: --debug-dump={SHARED_STAGES}`
   - Expected: result equals `2`
   - Expected: file_exists(output) is false
- expect all statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compile the layered backend fixture")
val run_id = getpid()
val root = "build/backend_debug_dump_driver_{run_id}/shared"
val dump = "{root}/layers"
val output = "{root}/probe"
val source = "{root}/probe.spl"
expect(dir_create_all(root)).to_equal(true)
expect(file_write(source, fixture_source())).to_equal(true)
val args = native_build_args(source, output, dump, SHARED_STAGES)
val option_error = cli_native_build_option_error(args)
val result = cli_native_build(args)
val expected = expected_shared_status(option_error)

if option_error == "":
    expect(result).to_equal(0)
    expect(file_exists(output)).to_equal(true)
else:
    expect(option_error).to_equal("unknown option: --debug-dump={SHARED_STAGES}")
    expect(result).to_equal(2)
    expect(file_exists(output)).to_equal(false)
expect_all_statuses(shared_artifact_statuses(dump, run_id, "probe"), expected)
```

</details>

#### fails closed and accounts for four requested backend layers without hooks

- validate every emitted compiler layer
   - Expected: dir_create_all(root) is true
   - Expected: file_write(source, fixture_source()) is true
   - Expected: option_error equals ``
   - Expected: result == 0 is false
   - Expected: file_exists(output) is false
- expect all statuses
   - Expected: option_error equals `unknown option: --debug-dump={ALL_STAGES}`
   - Expected: result equals `2`
   - Expected: file_exists(output) is false
- expect all statuses
- expect all statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("validate every emitted compiler layer")
val run_id = getpid()
val root = "build/backend_debug_dump_driver_{run_id}/all"
val dump = "{root}/layers"
val output = "{root}/probe"
val source = "{root}/probe.spl"
expect(dir_create_all(root)).to_equal(true)
expect(file_write(source, fixture_source())).to_equal(true)
val shared_args = native_build_args(source, output, dump, SHARED_STAGES)
val shared_option_error = cli_native_build_option_error(shared_args)
val args = native_build_args(source, output, dump, ALL_STAGES)
val option_error = cli_native_build_option_error(args)
val result = cli_native_build(args)

if shared_option_error == "":
    expect(option_error).to_equal("")
    expect(result == 0).to_equal(false)
    expect(file_exists(output)).to_equal(false)
    expect_all_statuses(shared_artifact_statuses(dump, run_id, "probe"), "PASS")
else:
    expect(option_error).to_equal("unknown option: --debug-dump={ALL_STAGES}")
    expect(result).to_equal(2)
    expect(file_exists(output)).to_equal(false)
    expect_all_statuses(shared_artifact_statuses(dump, run_id, "probe"), "FAIL")

# Missing backend adapters are required failures, never PASS or SKIP.
expect_all_statuses(backend_artifact_statuses(dump, run_id, "probe"), "FAIL")
```

</details>

#### rejects an adjacent empty stage instead of starting a partial build

- select all compiler artifact stages
   - Expected: dir_create_all(root) is true
   - Expected: file_write(source, fixture_source()) is true
   - Expected: result == 0 is false
   - Expected: option_error equals `unknown option: --debug-dump={malformed}`
   - Expected: result equals `2`
   - Expected: file_exists(output) is false
- expect all statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("select all compiler artifact stages")
val run_id = getpid()
val root = "build/backend_debug_dump_driver_{run_id}/malformed"
val dump = "{root}/layers"
val output = "{root}/probe"
val source = "{root}/probe.spl"
expect(dir_create_all(root)).to_equal(true)
expect(file_write(source, fixture_source())).to_equal(true)
val malformed = "source,,mir"
val args = native_build_args(source, output, dump, malformed)
val option_error = cli_native_build_option_error(args)
val result = cli_native_build(args)

if option_error == "":
    expect(result == 0).to_equal(false)
else:
    expect(option_error).to_equal("unknown option: --debug-dump={malformed}")
    expect(result).to_equal(2)
expect(file_exists(output)).to_equal(false)
expect_all_statuses(shared_artifact_statuses(dump, run_id, "probe"), "FAIL")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/backend_layer_artifact_matrix.md`
- **Plan:** `doc/03_plan/sys_test/backend_layer_artifact_matrix.md`
- **Design:** `doc/05_design/backend_layer_artifact_matrix.md`


</details>
