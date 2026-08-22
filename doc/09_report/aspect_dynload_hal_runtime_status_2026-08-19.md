# Aspect Dynload, Runtime, HAL, and Bootstrap Status

**Date:** 2026-08-19  
**Overall:** IMPLEMENTATION PARTIAL; END-TO-END EVIDENCE INCOMPLETE; RELEASE NOT READY
**Plan:** `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`

## Test status

| Evidence | Count | Meaning |
|---|---:|---|
| Focused startup/ExecIR run | 23 pass, 0 fail, 0 skip | Current focused evidence only |
| Environment-gated audit | 19 fail, 8 pass | Historical 2026-08-09 evidence; must be reconciled before calling it current |
| Stage-binary guard | 8 failed/crashed invocations of 12 | Retained historical evidence across four binaries |
| Raw skip lines | 216 | Static lines, not deduplicated executable tests |
| Raw pending lines | 93 | Static lines |
| `ignore_it` lines | 8 | Static lines |
| Ignore annotations | 4 | Static lines |
| Rust `#[ignore]` | 29 | Rust test-like annotations |
| Confirmed empty executable `it` bodies | 3 | Must be replaced or explicitly unavailable |

There is no honest current repo-wide failed/ignored-test total yet. The next
gate is a deduplicated manifest keyed by test path, case, compiler identity,
mode, platform, and receipt date.

## Rust and pure-Simple status

- Deployed `bin/simple` is still the Rust seed.
- A retained pure-Simple Stage 2 artifact exists but is stale; there is no
  admitted current Stage 3, Stage 4, or deploy receipt.
- The current Rust authority tree has no matching successful
  `simple-compiler` receipt; the next non-repeated gate is one focused offline
  `cargo check`, after ownership is stable.
- HAL implementation inventory contains 195 Simple files / 23,442 LOC, 20 C
  files / 14,924 LOC, 16 C headers / 1,665 LOC, and zero Rust HAL `.rs` files.

## Runtime boundary status

- Current anchored pure-Simple `rt_*` declarations: **4,277**
  (compiler 797; library 3,480).
- Current Rust-tree lexical `rt_*` tokens: **32,061**.
- The earlier 64,335 total was an unpinned historical dirty-tree lexical
  snapshot, not a unique-symbol or semantic-callsite count.
- A clean first alias-removal slice is ready across six env/file leaf files;
  process/time slices are also identified. `io_runtime.spl` is currently a
  no-go because delegating to its owners would create import cycles.

## HAL C migration and coverage

- C remains concentrated in Cosmos/OpenSSD (15 files / 9,052 LOC), RV64
  runtime shims (3 / 4,804), Cortex-M33 (1 / 1,044), and the RV32 wrapper.
- Cosmos FSBL is the first honest pure-Simple migration. Canonical libc/EABI
  exports stay C-owned until duplicate-symbol and weak `__aeabi_idiv0`
  semantics are proven.
- HAL branch coverage is **unknown**, not 100%. The retained 100% receipt has a
  zero-file/zero-branch denominator and is invalid evidence.
- The acceptance target is 100% of a nonzero host-executable branch manifest,
  plus separate physical-board contract evidence. Cosmos alone currently has
  an audited 884 C branch sites; that is not the total HAL denominator.

## Remaining feature groups

Seven main aspect/bootstrap groups remain: startup config cutover, loader policy
consumer, component resolver, CLI help/router cutover, aspect-pack admission,
typed facet compiler surface, and admitted x86_64 Stage 4 bootstrap/deploy.
HAL migration, parity, branch evidence, and runtime-boundary collapse proceed
as parallel supporting lanes.

## Repository and process cleanup

- Parallel review reached the 21-agent concurrency cap; broad findings received
  a highest-capability Sol review.
- Preserved useful missing heads as `rescue/agentrestore-35849c9` and
  `rescue/fix-dbl-87d5f016`; pruned their missing registrations.
- Removed only the failed seed checkout after confirming its commit remained on
  `codex/gate5r-dir-sync-b791`.
- Terminated stale/runaway audit process groups 291105, 343494, and 376108 with
  `TERM`; active main-agent and live build processes were preserved.
- Repaired shared Git configuration to the standard per-worktree layout and
  verified linked roots plus unchanged indexes.
- Bulk worktree/branch/JJ deletion is deferred: the attempted exact manifest did
  not converge, so no bulk delete list is authorized. Each candidate still
  needs current cleanliness, reachability, process-CWD, lock, patch-id/change-id,
  and JJ-root checks before removal or cherry-pick.

## Current verdict

**STATUS: WARN** — the 2026-08-22 implementation tranche now includes compiler
MC/DC manifests and probes, native report accounting, exact normal/alpha/beta
promotion gates, five-kind governed exclusions, static/dynamic aspect policy,
bounded environment adapters and replay cursors, critical-closure allocation
and assurance checks, and bounded provider configuration. Focused native
evidence measures the disarmed patchpoint at 3 ns/call versus a 2 ns baseline,
with zero allocation/map/dynload activity and 1,024 KiB peak RSS.

Release remains blocked on a source-current admitted Pure Simple compiler and
the canonical matched five-mode receipt. Static-off/static-on and armed-mode
NFR rows therefore remain unproven. The sealed provider protocol still carries
digests rather than normalized operation payloads, so tagged calls are not yet
wired end-to-end to real Pure/C/Rust I/O comparison or automatic environment
instruction extraction. Trusted live sandbox execution is also unavailable on
the current host. These are active gaps, not exclusions or PASS results.
