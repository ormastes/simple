# Bootstrap Phase 4 conflict-resolution manifest — 2026-08-16

Status: **RESOLVED / AWAITING INDEPENDENT REVIEW / NOT PUSHED**

## Authority

- Isolated worktree: `/mnt/data/worktrees/stage4-sync-guard-20260816`
- Fetched upstream: `origin/main` at
  `22c80fe63e1ba9581f7b5ef26c44b86f2cbede0a`
- WIP commit: `c228a3e5c879a516c2dba55661be0c91bccf7021`
- WIP parent / merge stage 1: `6a31a89ce15ee38440d20910b43057fa5dd26fee`
- Push lock: `/mnt/data/tmp/simple-main-restart12-push.lock` held throughout
  fetch, resolution, and commit preparation.
- Tracked-file guard: `114538` before cherry-pick; `114553` after resolution
  manifest publication. The count increased by 15 and did not trigger the
  reduction guard.

## Conflict blobs and resolutions

`absent` means the path has no blob in that side of the three-way merge.

| Path | Before / stage 1 | Upstream / stage 2 | WIP / stage 3 | Resolved |
|---|---|---|---|---|
| `doc/08_tracking/bug/bootstrap_flat_llvm_receiver_signature_corruption_2026-08-16.md` | `4d1dab3c4c52e50df2ac41554ed070a0f0d5c84e` | absent | `5781abf1b5d358061844b19788183e3c07da196e` | absent |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | `0a4dcedb753b9f080434bc4421851ba93299e922` | `affeea79b67ed62bf45c0ba5b54057939e111122` | `4af150cbdfed9bd1b406fec8d945e730e2c85273` | `f9883b992658a4c3742857d6652b89c58744a980` |
| `scripts/bootstrap/resume-stage3-from-admitted.sh` | `e5f74a6fe0b747394e4dd9300773bfe1e1f824d9` | `7d76eb25acbeff62a37e5bd971bd8ccc4c0afbfc` | `8b0cad2b956579e7f73d5f14655d2f8a51f93959` | `16c28551e146e8878428d881af2733ba7a1975ee` |
| `scripts/check/lib/bootstrap-stage3/manifest-verify.shs` | `71d188850268402ab10365a1cf663b2abdbeb1c3` | `52d8e8e14fad92cc6c5bc2879026d0235991b0d6` | `f803f584ea056c6acc5a92b74bbe201b46cb8897` | `fb37df8ac9c32e3be8a6d60a209f2ec910eee252` |
| `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` | `08aaa455ce1482fceaf2566b50fe8c28ae937097` | `8ebcb017ba21edb7a9b7a1736ad4290e3397c9ed` | `ac4f82c657a2955a2fcbeca47110338527b6d9f8` | `9966f9d0270d9842a8063ad140d26a0fbd04f058` |

### Rationale

- The obsolete receiver-signature bug document stays absent. Its final text
  falsified that hypothesis as the complete root cause; the active mixed-tail
  status is retained in the handoff and
  `bootstrap_flat_function_tail_local_payload_loss_2026-08-16.md`.
- `bootstrap-from-scratch.sh` keeps upstream planner-v2 authorization,
  stop-after-Stage-3, and admitted Stage-4 resume semantics. It integrates the
  WIP strategy supervisor and the complete Stage-2-only identity-bound
  admission path, including receiver evidence, receipt creation, cleanup, and
  mutually exclusive option checks. The merged path has no unset evidence
  variables.
- `resume-stage3-from-admitted.sh` requires the WIP Stage-2 admission and
  receiver receipts in addition to upstream's immutable inputs. Fresh
  source/Git/tool preflight snapshots use separate temporary paths and must
  match the admitted Stage-2 files before lock acquisition or build; admitted
  receipts are never overwritten.
- `manifest-verify.shs` preserves upstream Stage-3 streaming and allocator
  constraints. It also accepts the WIP's historical Stage-2 transcript shape
  only when its progress path is empty or equals the canonical output path;
  Stage 3 still requires the exact canonical path.
- `core_codegen.spl` preserves upstream's streaming driver contract:
  `register_bootstrap_signatures`, `emit_bootstrap_statics`, then per-function
  translation. It integrates the WIP scalar-table fallback scan without
  restoring the obsolete combined emitter. C3 call-destination handling is
  retained: Call payloads are decoded by discriminant, missing destinations
  fail closed before LLVM assembly, and `defined_locals` is recorded only
  after a call line reaches its output sink.

## Scoped checks

- `git diff --cached --check -- <five conflict paths>`: **PASS**
- `sh -n scripts/bootstrap/bootstrap-from-scratch.sh`: **PASS**
- `sh -n scripts/bootstrap/resume-stage3-from-admitted.sh`: **PASS**
- `sh -n scripts/check/lib/bootstrap-stage3/manifest-verify.shs`: **PASS**
- Reviewer amendment: affected-path `git diff --check` and
  `sh -n scripts/bootstrap/resume-stage3-from-admitted.sh`: **PASS**
- Unmerged paths after staging: `0`

Formal verification was intentionally not run. Independent resolution review
is required before any push.

## Explicitly deferred WIP recovery hardening

The resolved wrapper preserves upstream behavior for the following WIP intents,
which remain blocking follow-up work rather than silently claimed integration:

- allowlisted external output roots (the WIP authority helper is absent from
  the fetched upstream helper bundle),
- signal-race-safe lock-owner cleanup,
- one immutable archive directory per recovery attempt, and
- hash/evidence-bound retention of previous and failed candidates.

These deferrals do not weaken the mandatory authority precomparison above, but
they preclude claiming the full WIP resume-recovery hardening as complete.
