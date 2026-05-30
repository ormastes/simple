*Source: `test/integration/remote_jit/ch32v307_composite_runner_path_spec.spl`*  
*Last Updated: 2026-03-31*

---

# CH32V307 Composite Runner Path Regression

**Feature IDs:** #RJE-013  
**Category:** Integration  
**Difficulty:** 4/5  
**Status:** Implemented  
**Requirements:** N/A  
**Plan:** [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)  
**Design:** [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)  
**Research:** N/A

## Overview

Verifies that the CH32V307 composite runner no longer short-circuits through
the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))`
through the real adapter-backed execution flow.

This spec is intentionally host-aware:

- if `wlink` or the probe is unavailable, the runner must skip cleanly
- if hardware is available, the composite runner must take the real CH32 adapter path
- the result must not regress to the old `"not implemented"` message

This file is the authoritative regression for composite-runner wiring. The
direct `wlink` readiness and SDI-output probe remains covered separately by
`ch32v307_composite_runner_spec.spl`.

## Syntax

```simple
val result = run_test_file_jit_ch32v307(
    "test/fixtures/remote_jit/baremetal_lib_workload_main.spl",
    source,
    default_options()
)
```

## Examples

```simple
expect(result.error.contains("not implemented")).to_equal(false)
expect(result.skipped).to_equal(0)
```
