# System test plan: container/GPU 8K80 completion

| Requirement | Scenario | Expected result |
|---|---|---|
| REQ-R8KC-001/002 | admitted native A4 direct execution | exact receipt passes |
| REQ-R8KC-003 | strict changing semantic Vulkan producer | device receipt passes |
| REQ-R8KC-007 | strict changing semantic visible-window producer | one-owner presentation receipt passes and explicitly excludes scanout capture |
| REQ-R8KC-007 | unavailable/suboptimal/fallback window presentation | producer blocks or fails closed |
| REQ-R8KC-004/005 | correlated A4+A5, no physical | `blocked-physical` |
| REQ-R8KC-004/006 | correlated A4+A5+A6/A8 | aggregate `pass` |
| REQ-R8KC-005 | missing/malformed/duplicate key | aggregate `failed` |
| REQ-R8KC-005 | source/workload/device mismatch | aggregate `failed` |
| REQ-R8KC-005 | seed/interpreter/stub/fallback/unknown | aggregate `failed` |
| NFR-R8KC-001 | p95 above 12.5 ms | aggregate `failed` |
| NFR-R8KC-006 | CUDA-only or headless claimed physical | aggregate `failed` |

The bounded parser/self-test runs without GPU hardware. The live scenario runs
only when container GPU admission succeeds and reports `blocked`, not skipped,
when its prerequisites are absent. Physical promotion remains TODO684/TODO685.
