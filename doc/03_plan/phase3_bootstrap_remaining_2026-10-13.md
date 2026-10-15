# Phase 3 bootstrap and generics: remaining work

Updated 2026-10-13. Status: INCOMPLETE; shared candidate is not release-qualified.

## Scope and candidate

Finish robust Windows bootstrap based on Claude session
`75022ee3-ea0e-4bfe-bdb6-3d4b162cae8c`, qualify generic features and implementations,
logic and memory behavior, and formal verification, then land reviewed fixes on
the existing `release_phase3` branch. Phase 3 and native Hello World must pass
for release qualification. On 2026-10-13 the user explicitly requested landing
the current source changes before these gates pass. Landing source does not
constitute compiler admission, deployment qualification, or a passing bootstrap.

The candidate contains 35 individually applied source commits on base
`40f7ab097a1c1052b266ba4b7f2e9c39729c2510`; its last source commit is
`3b91f4c0abfe503b9cdebc32d62e52ec24bfb082`. The latest generic owner fix came
from `1ef1588fe26c9a9d645779cf5f89d6c3b6f683cb`. Subsequent commits may add
this plan. Preserve one-at-a-time application for remaining fixes.

## Evidence and limits

| Item | Actual evidence | Remaining limitation |
| --- | --- | --- |
| Diagnostic Stage 2 | 1,233 modules compiled; genuine sanity and receiver checks passed | Whole bootstrap exited 1 during postreceiver Windows long-path inspection; no new admission |
| Stage 2 binary | SHA-256 `a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994` | Compiler-only; full CLI and test runner remain unbuilt/unverified |
| Generic owner repair | Source review accepted initial composite and method binder paths; working/staged environment guards passed | Eleven unit tests and twelve native HIR scenarios are authored but unrun; concrete generic method execution and omitted-default application remain open |
| Continuation receipt hardening | Twelve bounded host component controls passed; native exit 0, Job empty, unchanged pins | Complete typed admission consumption and full resource-failure coverage remain unverified; production continuation is disabled |
| Formal checks | Earlier structural-model checks passed on unchanged inputs | Production captures, differential checks, negative controls and implementation refinement are incomplete; no universal generics proof |
| Long-path repair | Actual production owner compiled and reached deep-path controls | Four host attempts failed on setup/test-oracle issues; final junction control and corrected suite remain unrun |

Do not repeat unchanged passing checks or infer product correctness from authored
tests, static review, binary existence, structural CI, or a model-only proof.

## Ordered completion plan

1. Resolve the retry-limit decision. `AGENTS.md` limits a feature to three
   verify/fix cycles. One additional run was explicitly authorized and consumed.
   The prepared fifth host run requires a new exception; sharing this plan does
   not authorize it. Run only the corrected nine-case control suite under its
   five-minute, 2 GiB RSS, 512 MiB growth bounds if authorized.
2. Qualify and review the isolated Windows long-path enumeration repair.
   Preserve lexical paths, no-follow reparse checks, ownership checks and
   resource limits. Commit and apply this repair separately after its controls
   pass; do not sweep continuation files into the same commit.
3. Complete typed postreceiver admission integration. Preserve the original
   bootstrap failure and existing genuine passing receipts. Require canonical
   source/runtime/tool/build-argument verification and an actual closed bounded
   process receipt. Qualify the public typed receipt path, copied/renamed receipt
   refusals, legacy compatibility and resource failures before enabling it.
4. Review and test full-root resource accounting for the one canonical internal
   Rust bootstrap junction. Count its ordinary generation once and refuse every
   other unapproved reparse entry. Account for original source, caches, runtime
   and output; a small continuation directory must not hide whole-build growth.
5. Finalize the retained Stage 2 output through the canonical admission route
   without rebuilding its unchanged 1,233 modules or rerunning passing sanity
   and receiver checks. Do not manufacture receipts or rewrite identity stamps.
6. Freeze fresh source and tool inputs for the actual final candidate. Historical
   f34 qualification inputs are stale after later picks. Build Phase 3, a
   non-vacuous full CLI, and a phase-bound test runner with separate compatible
   caches and `SIMPLE_NO_STUB_FALLBACK=1`. Record real reuse and rebuilt counts.
7. Run generic unit and native tests against the actual producer: scalar,
   array/composite and nominal arguments; imported owner methods; declaration
   bounds/defaults; shadowing; aliases; trait/impl paths; physical linkage;
   persistence; explicit missing-dependency diagnostics; and actual concrete
   method calls. Complete omitted type-argument default application rather than
   treating default dependency projection as proof of application.
8. Verify serializer C0/Unicode byte fidelity, archive publication/refusal and
   corrupted-input controls. Investigate the earlier post-HIR memory growth
   with attributable evidence; do not claim provider instrumentation fixed it.
   Check logic, ownership, memory and applicable native diagnostic controls.
9. Bind formal production captures to the frozen source and run the planned
   differential and negative checks. Report exactly what the model proves and
   which production behaviors are covered; retain gaps as failures/open work.
10. Run required compiler/library/MCP/LSP checks, MCP stdio integration and native
    smoke, native Hello World build/run, and full CLI tests with a real `Results:`
    line. Audit environment facades and spec layout. Perform the final clean
    build only after focused repairs converge, preserving successful caches.
11. Require verification `STATUS: PASS` for all requested acceptance gates.
    Review the exact PR diff, fresh base and comments, resolve real failing
    checks and conflicts without discarding other sessions' work, then ready
    and merge subsequent qualification changes into `release_phase3`. The user
    separately authorized landing the current source checkpoint while these
    gates remain open. No direct protected-branch push.

## Restart instructions

Start a fresh scoped session; do not resume an oversized rollout. Read this plan
from the current `release_phase3` branch and use its current commit as the new
integration base. PR #3465 carries the source checkpoint and this plan.

1. Check the active worktree and sessions before editing. Keep the shared main
   worktree read-only and create an isolated `work/*` lane. Do not reset or clean
   retained diagnostic storage or another session's worktree.
2. Read the local acceptance ledger and composition mapping listed below, then
   inspect actual terminal receipts and input hashes. Four host attempts are
   terminal failures; no fifth attempt is live. The twelve passing typed-receipt
   component tests do not establish production continuation readiness.
3. Request the required explicit exception for the corrected fifth host run if
   it has not been authorized. Inspect `request-v5.pending.json`, verify every
   source/tool/collector pin and the fresh output paths, then execute that exact
   bounded request only when authorized. Do not blindly rerun an old launcher.
4. Review and apply the two isolated bootstrap repairs separately; they are not
   included automatically in the current landed source checkpoint. Check their
   compatibility against the latest release helpers before enabling production.
5. Follow the ordered completion plan above. Reuse compatible retained caches
   and genuine passing evidence; update authority for changed inputs rather than
   rewriting stamps. Keep stage/producer/entry cache writers separate.
6. Record fresh source revision, actual argv, tool hashes, exit codes, test totals,
   output hashes and resource measurements for each new acceptance gate. Stop
   when each gate passes; escalate concrete failures at the iteration limit.

Suggested restart task: "Read this plan and the retained acceptance ledger;
continue the unfinished Phase 3 bootstrap/generic/formal qualification from the
current release_phase3 source. Preserve caches and other sessions. Do not claim
PASS from the source landing or repeat unchanged green tests."

## Retained local artifacts and unshared repairs

These paths are host-local evidence, not artifacts available automatically to
someone cloning the draft PR:

- `C:/dev/simple/build/native_probe/release-phase3-acceptance-ledger-20261011.md`:
  chronological observations, source identities and unresolved gates.
- `C:/dev/simple/build/native_probe/gh-composition-40f7-20261012.json`:
  ordered source and applied commit mapping.
- `C:/dev/simple-bootstrap-storage/windows-diagnostic-parent-20261012`:
  immutable diagnostic source, retained compiler/runtime caches, binary and
  whole-bootstrap failure evidence.
- `C:/dev/simple-bootstrap-storage/bootstrap-longpath-host-controls-20261012`:
  four failed attempt receipts/logs and `request-v5.pending.json` (unexecuted).
- `C:/dev/simple-bootstrap-storage/postreceiver-typed-host-controls-20261012`:
  twelve passing component-control observations and bounded receipt.
- `C:/dev/simple-bootstrap-longpath-20261012`: uncommitted isolated long-path
  and typed-continuation repairs. These are NOT in the 35-pick candidate.

The existing shared `C:/dev/simple` worktree contains other sessions' changes.
Preserve them; this plan and candidate are authored in an isolated worktree.

## Measured state addendum — 2026-10-16 (macOS stage1→2 campaign lane)

Canonical local runs (llvm/dynload, full waiver atoms, 8 GiB RSS cap) on
release_phase3 a1d66e52 and fix branches; details and retained logs in
doc/08_tracking/bug/stage2_matrix_remaining_rows_sdnvalue_cli_imports_2026-10-15.md
(site-19).

ALWAYS GREEN on every run: stage1 seed build, stage2 native compile
(1348 modules), LINK, sanity probes, struct-receiver proof, all 8 `_cg`
module-compile rows.

Rows and their fixes (PR numbers against release_phase3):
- test_runner_build: two stage2 backend ICEs FIXED and campaign-verified
  (PR #3487: GEP index conversion; void-to-integer materialization).
  `SdnValue::Array` payload mismatch FIXED and campaign-verified
  (PR #3488: owner canonicalization + metadata-owner disambiguation).
  Remaining: B5b "multiple wildcard arms" in `SdnValue.is_null` —
  `case Null:` reaches MIR as Wildcard; bridge and MIR reclassification
  ruled out with receipts; diagnosis points at mono-archive body capture
  (ArchiveRequests) while the enum subject is unresolved through the
  `Dict<text, SdnValue>` payload seam. Owner: mono archive lane.
- compiler_cli_build: `Span` import FIXED (PR #3486). Remaining:
  fabricated-position `BackendKind` (owner-walk diagnosis needed) and
  missing `_pci_ecam_base` arm64/riscv64 helper (needs SimpleOS PCI
  driver owner; provider carries `PciHostConfig.ecam_base`).
- compiler_bootstrap_tests / interpreter_interpreter_tests /
  loader_interpreter_tests: cascades of the two build rows.

Operational notes for future runs: manual runs need the four
SIMPLE_MCDC_OFF_WAIVER_* atoms; rerun with --invalidate-cache=stage2 on
source change; admitted caches seal read-only (chmod u+w for local
cleanup); source-edit experiments drift build/scv — clear it afterwards;
the test campaign runs a sharded-frontend policy (see
verification_frontend_policy lines in row logs).
