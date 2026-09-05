# RT/HAL Provider Differential — Operator Manual

Executable: `test/03_system/runtime/rt_hal_provider_differential_spec.spl`  
Status: **not executed in this lane**; hand-maintained mirror.

## Workflow

1. **compare RT/HAL providers** — compiler-stage a sealed V3 plan, then execute
   one query through Pure Simple, C, and Rust adapters and require deterministic
   provider order and parity.
2. Execute an effect once through the Pure Simple owner; comparators consume replay mode and must match the effect trace.
3. Require `RTHAL-E-MISMATCH` for a divergent result and `RTHAL-W-UNSUPPORTED` for an absent required provider.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-008 | Pure provider occupies ordinal zero; foreign providers are comparators |
| REQ-009 | Query comparison, effect replay, mismatch/unsupported distinction |
| REQ-014 | Slot-based deterministic provider ordering |

## Admission boundary

The V2 public entry and direct V3 installation are deliberately rejected. The
scenario must use the compiler-owned staged V3 route, demonstrate that Plan A
reaches Ready, then demonstrate that same-rank Plan B with a different canonical
identity is rejected. This manual does not claim an executed foreign-provider
run until its executable receipt exists.
