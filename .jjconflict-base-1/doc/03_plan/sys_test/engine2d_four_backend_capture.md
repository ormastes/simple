# Engine2D Four-Backend Capture System Test Plan

Related semantic/material test plan:
`doc/03_plan/sys_test/wm_glass_theme_host_simpleos.md`. Its architecture and
detail design are `doc/04_architecture/wm_glass_theme_host_simpleos.md` and
`doc/05_design/wm_glass_theme_host_simpleos.md`; their CPU material assertions
do not replace the backend evidence below.

| Requirement | Evidence |
|---|---|
| REQ-E2D4-001 | Same scene ID and dimensions in all five records |
| REQ-E2D4-002 | GPU device readback or SIMD execution counters |
| REQ-E2D4-003 | Exact six-event ordered target receipt |
| REQ-E2D4-004 | Durable capture path, SHA-256, bounds, revision |
| REQ-E2D4-005 | Pairwise and aggregate comparison report |
| REQ-E2D4-006 | Negative validation scenarios |

The pure contract spec runs first. Each live target then runs once. A failed
target may be fixed and rerun no more than twice. The final comparison consumes
only evidence created from the integrated revision.

The CPU-composited glass-material source/unit slice emits no capture record and
does not satisfy any row above. In particular it cannot stand in for SIMD
counters, Vulkan/Metal device readback, ordered target events, a host capture,
or x86/ARM QEMU evidence; those existing gates are unchanged.

The reviewed correction has no post-fix test run because the current session's
verification cycle cap is reached. Its bounded CPU blur/reduction and memory
guard are not a substitute for an integrated backend evidence run.
