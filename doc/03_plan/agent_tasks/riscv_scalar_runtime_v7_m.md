# V7 unified dynamic IM owner agent handoff

## Ownership

Merge owner: primary Codex. Final reviewer: normal/highest-capability model.
The product boundary is a V7-only `rv32im`/`rv64im` flattened pipeline with
one tag-2 dynamic M owner. V8 CSR is separate; this handoff neither changes
class 6/tag 3 nor permits IM+Zicsr profiles.

## Implemented shared contract

The implementation uses the `request_*`, `completion_*`, and
`provider_protocol_fault` ports of
`strict_riscv_scalar_runtime_m_provider`. It is a single flat tag-2 owner.
No V7-specific SPipe setup/checker helper suite was added; future test work
must bind to this actual interface rather than invent a parallel contract.
Sidecars must not make another tag-2 provider, modify V6/V8 sources, or mark
qualification complete.

## Lanes

| Lane | Owner | Boundary and acceptance |
| --- | --- | --- |
| Flat M owner | Primary | Implemented: one sequential tag-2 owner; all MUL/DIV/REM + RV64 W forms; full admission and held completion |
| Router/fault/pipeline/backend | Primary | Implemented: versioned V7 router/pipeline/backend with exactly one M fault input and strict deterministic VHDL renderer |
| Admission/oracle review | Codex Spark sidecar | Review existing div admission/normalizer/datapath against exact IM rows; report only, no source edits without merge-owner approval |
| Clocked vectors/manual | Primary | Provider-only GHDL scenario exists; full-pipeline GHDL and RV32 multiply vectors remain open |
| Final acceptance | Highest-capability reviewer | Audit found source topology but not qualified evidence; PASS remains prohibited |

## Non-negotiable review invariants

- No second tag-2 owner, no V6 multiply provider remaining in V7 closure, and
  no sequential divider child.
- Full metadata admission precedes capture; `row_matched` alone is insufficient.
- RV64 W divide/remainder uses 32-bit restoring state and one final sign extension.
- Zero-divisor and signed-overflow are results, not traps; malformed metadata is
  a sticky protocol fault with no completion.
- Completion is stable under backpressure, consumed once, and all retirement
  remains through the existing sole completion path.

## Qualification handoff

The merge owner runs the current two commands in the V7 system-test plan only
after an admitted self-hosted runtime is available. The final reviewer cannot
accept a PASS, release, or combined CSR profile before admitted structural and
full-pipeline clocked lanes (including the open RV32 multiply coverage) succeed.
