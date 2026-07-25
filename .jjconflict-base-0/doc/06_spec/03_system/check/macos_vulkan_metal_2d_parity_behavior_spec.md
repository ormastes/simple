# macOS Vulkan/Metal 2D parity behavior

> Exercises the aggregate checker with deterministic local PPM captures and complete synthetic lane records. The positive case must accept byte-exact Vulkan/Metal evidence; the negative case changes one semantic accent field and must fail before pixel tolerance could hide the mismatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Vulkan/Metal 2D parity behavior

Exercises the aggregate checker with deterministic local PPM captures and complete synthetic lane records. The positive case must accept byte-exact Vulkan/Metal evidence; the negative case changes one semantic accent field and must fail before pixel tolerance could hide the mismatch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/engine2d_four_backend_capture.md |
| Plan | doc/03_plan/sys_test/engine2d_four_backend_capture.md |
| Design | doc/05_design/engine2d_four_backend_capture.md |
| Research | doc/01_research/local/engine2d_four_backend_capture.md |
| Source | `test/03_system/check/macos_vulkan_metal_2d_parity_behavior_spec.spl` |
| Updated | 2026-07-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the aggregate checker with deterministic local PPM captures and
complete synthetic lane records. The positive case must accept byte-exact
Vulkan/Metal evidence; the negative case changes one semantic accent field and
must fail before pixel tolerance could hide the mismatch.

**Requirements:** doc/02_requirements/feature/engine2d_four_backend_capture.md
**Plan:** doc/03_plan/sys_test/engine2d_four_backend_capture.md
**Design:** doc/05_design/engine2d_four_backend_capture.md
**Research:** doc/01_research/local/engine2d_four_backend_capture.md
**Architecture:** doc/04_architecture/engine2d_four_backend_capture.md

## Syntax

```sh
bin/simple test test/03_system/check/macos_vulkan_metal_2d_parity_behavior_spec.spl --mode=interpreter
```

## Expected Result

The exact fixture reports `pass_status=pass`. After semantic mutation the same
checker reports `fail_status=fail` with
`semantic-after-accent-mismatch`. Temporary artifacts are removed by the
fixture. This contract does not claim that either native backend ran.

## Scenarios

### macOS Vulkan and Metal 2D parity behavior

#### should pass exact evidence then fail one semantic mutation

- Construct two small exact lane captures
- Run the aggregate checker and require PASS
- Mutate one semantic field and require FAIL
   - Expected: code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct two small exact lane captures")
step("Run the aggregate checker and require PASS")
step("Mutate one semantic field and require FAIL")
val (stdout, stderr, code) = process_run("/bin/sh", [
    "scripts/check/fixtures/check-macos-vulkan-metal-2d-parity-contract.shs"
])
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("pass_status=pass")
expect(stdout).to_contain("fail_status=fail")
expect(stdout).to_contain("fail_reason=semantic-after-accent-mismatch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/engine2d_four_backend_capture.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_four_backend_capture.md`
- **Design:** `doc/05_design/engine2d_four_backend_capture.md`
- **Research:** `doc/01_research/local/engine2d_four_backend_capture.md`


</details>
