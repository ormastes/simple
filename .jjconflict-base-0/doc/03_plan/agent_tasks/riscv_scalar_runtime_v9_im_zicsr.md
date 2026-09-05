# V9 IM + Zicsr agent handoff

## Ownership and shared contract

Merge owner: primary Codex. Final reviewer: normal/highest-capability model.
V9 is the exact `rv32im_zicsr_zifencei`/`rv64im_zicsr_zifencei` product with
21 direct children, one tag-2 unified M owner, one tag-3 CSR owner, and a
12-source fail-closed gate. Shared test helper names are those in the V9 detail
design; all unimplemented helpers fail explicitly.

## Parallel lanes

| Lane | Suggested owner | Boundary | Acceptance |
| --- | --- | --- | --- |
| Canonical plan/router | Codex Spark sidecar | V9 profile/database/type/router only | exact profile receipt and M/CSR class/tag rejection matrix |
| Pipeline/fault/backend | Primary Codex | V9 21-child bindings, gate, VHDL renderer | unique drivers/closure, 12 named faults, deterministic VHDL |
| M/CSR integration review | Claude Haiku sidecar | review-only against V7/V8 provider ABIs | report tag isolation, service/commit and held-result hazards; no edits |
| Clocked/system scenarios | Primary Codex | V9 tests and manual only | real assertions for matrix; zero-stub generated manual |
| Final acceptance | Highest-capability reviewer | source, test, generated manual, qualification evidence | no V7/V8 wrapper/alias or bootstrap-evidence promotion |

The merge owner defines interfaces before sidecars start and resolves all
conflicts. Sidecars must not modify V7/V8 product files, duplicate a provider,
weaken canonical receipt checking, or mark a release PASS.

## Sequencing

1. Add canonical V9 profiles and exact decoder-plan acceptance.
2. Add V9 router, fault gate, flat 21-child pipeline, and strict backend.
3. Wire existing flat M and CSR owners once each; preserve their public ABI.
4. Add unit, full-pipeline clocked GHDL, system, and manual evidence.
5. Have the final reviewer audit all requirements before admitted-runtime
   qualification and formal/RVFI gates.

## Non-negotiable invariants

- No second tag-2/tag-3 owner; no V6 Zmmul owner and no V7/V8 wrapper child.
- Exact plan/profile/row/class/effect metadata precedes provider capture.
- M and CSR live state, ready/valid, faults, and service side effects are
  independent; retirement still has one global completion path.
- CSR commit is exactly once on legal held-result consumption; protocol faults
  have no completion/effect; policy traps are not protocol faults.
- Qualification remains blocked until admitted self-hosted, full-pipeline GHDL,
  formal/RVFI, and generated-manual evidence all pass.
