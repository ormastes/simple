<!-- codex-design -->
# Agent tasks: LLM Caret infrastructure access

## Shared contract (primary-owned)

The public types/functions, five tool names, seven `step("...")` strings, and
four test helper names are frozen in the architecture/detail design before any
implementation sidecar work.

## Lanes

| Lane | Owner | Scope | Merge rule |
|---|---|---|---|
| Research implementation audit | Kant (sidecar, complete) | Caret/ITF source truth | read-only findings reviewed by primary |
| Research document audit | Jason (sidecar, complete) | existing docs/evidence gaps | read-only findings reviewed by primary |
| Research provider audit | Russell (sidecar, complete) | official compatibility surfaces | primary checked conclusions/sources |
| Smaller-model guide draft | `gpt-5.4-mini` sidecar (complete) | initial operator/developer guide | primary corrected before acceptance |
| Compatibility implementation | Primary Codex | `infra_access.spl`, tool gate, focused tests | preserve unrelated dirty lanes |
| SPipe/manual/verification | Primary Codex | system spec, docgen, gates, PASS report | no release mutation |

No implementation sidecar lane is needed: the chosen thin capsule is one
coupled trust-boundary change and concurrent edits would increase merge risk.

## Merge and review ownership

- Merge owner: primary Codex session for this feature lane.
- Final reviewer: primary highest-capability Codex model after the smaller-model
  draft and research sidecars complete.
- Unrelated dirty files and active-session work are excluded from this lane.
