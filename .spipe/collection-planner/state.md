# Item 3: typed collections and query optimizer

## Objective and selected scope

User requested further research, updated plan/design documents, concrete modern
SSpec acceptance tests, TDD implementation, and parallel isolated worktrees on
the release branch. The selected contract remains REQ-001–011 in
`doc/02_requirements/feature/collection_planner.md` and NFR-001–007 in
`doc/02_requirements/nfr/collection_planner.md`.

Status: **IN PROGRESS; verification is incomplete; no release admission.**

Latest continuation adds generic explicit-contract map/set, stable hashed
uniqueness, real interned-symbol/nested-option fixtures, bounded canonical-loop
provenance and four shared engine-oracle programs. Differential certification
now rejects nonzero exits, missing/wrong expected markers and any failed lane;
JIT still lacks an execution witness. Array-concat rewriting preserves original
MIR until canonical ownership, liveness and alias proofs exist. All new Simple
checks remain authored but unexecuted.

Canonical bootstrap attempt 1 stopped on an excluded symlink target; attempt 2
passed materialization but stopped on an excluded counterpart ABI header.
Attempt 3 followed an explicit prerequisite-existence preflight and terminated
at the RSS admission guard. Its source pin was `d53aed4ec74`; the later explicit
user resume and bounded recovery are recorded below. Original evidence remains
under Git worktree metadata `item3-bootstrap/attempt3`. Original
attempt-1 logs were removed by sparse-checkout behavior; its reconstructed
summary is explicitly not an original log. No prior native diagnostic is rerun.

## Session ownership (2026-10-03)

- Session: `01a0fedc-f802-7af2-ab5b-a5c6abe85984`, merge/review owner `/root`.
- Integration worktree: `C:/dev/simple-item3-dev-20261003`.
- Work branch: `work/item3-dev-20261003`; target: `release/1.0`.
- Refreshed base and expected target: `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c`.
- Research, specifications, and planner agents have separate sibling worktrees
  and `work/item3-{research,spec,planner}-20261003` branches. Their commits are
  integrated explicitly; unrelated items 1/5 and bootstrap work are preserved.
- Each worktree retains a local Git ownership receipt. No protected ref is
  updated directly, and no release tag or publication is authorized here.

## Evidence boundaries

The test plan owns CP-001-A through CP-011-C: 33 full-scope acceptance scenarios.
CP-GUARD scenarios separately exercise the real advisory selector and explain
API. A selector result does not prove extraction, lowering, generated artifact
execution, cross-engine semantic parity, or NFR compliance.

`C:/dev/simple/bin/simple.exe --version` reports a Rust bootstrap seed.
The inspected WSL snapshot `/root/simple-build/build/phase_snapshots/phase1_1790916939/simple`
also reports a Rust seed. Neither is used for normal test verification.
The Windows LLVM Stage 2 compiler under
`C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage2/x86_64-pc-windows-msvc/simple.exe`
identifies itself as `simple-bootstrap 1.0.0-rc.1`; its help exposes compilation
only, not `test`, `check`, or doc generation. Native attempts through it are
diagnostic, unadmitted evidence, not full runtime acceptance.

The native bound-regression build first rejected missing SCV compile-event
journal admission. Retrying once with the prescribed cold-inventory setting
timed out after 120 seconds without an executable. The test-first commit
`944e1fe7644` precedes source fix `8ab6c4d7bd1` in the planner lane, but neither
attempt establishes semantic RED or GREEN. The tracked diagnostic report is
`doc/09_report/collection_planner_bound_tdd_2026-10-03.md`.

The guard now rejects static size or admitted profile size exceeding a known
hard bound before attributes can authorize an alternative. Exact bounds and
unadmitted profiles retain their existing semantics. Independent source review
found no P0/P1; runtime correctness remains unverified. No full REQ is closed
by this focused guard.

The continuation adds seven synchronous typed-column acceptance subcases
(CP-001-A/B/C suffixes) with 40 real assertions and an authored companion.
It also fixes logical-plan negative fixtures that inadvertently supplied their
supposedly missing bindings, with positive controls and a companion manual.
Both changes received independent source review without P0/P1 findings.
They remain unexecuted; no complete REQ or cross-engine gate is closed.

Read-only diagnosis established that cold admission inventories all `src` and
`test` before entry closure; the earlier 120-second budget was shorter than its
300-second Git subprocess limit. `SIMPLE_CACHE_DIR` did not configure the native
cache; the report now records the actual default and supported `--cache-dir`
flag. The final bounded diagnostic is tracked in the same report and cannot
qualify as RED unless the before-fix executable reaches its intended assertion.
That final attempt timed out at 360 seconds before inventory publication,
without an executable. The owned process tree was terminated and the fixed
selector restored with its blob identity verified. All three diagnostic
attempts are exhausted; another identical retry is not the next step.
Admission profiling or a supplied admitted runner is required to unblock
execution. No semantic RED/GREEN or production-ready verification was obtained.

## Continued logic and tests at user direction

The user requested code logic and tests first despite the execution blocker.
The memory lane adds per-candidate memory admission to the real selector and
exposes the same supplied bounds in explanations. Unknown budget or candidate
bounds reject optimization; attributes and admitted profiles cannot bypass
them. Zero/exact limits and fitting alternative selection are covered by
test-first unit, profile-bridge and CP-GUARD-07–10 scenarios.

Selector lane: `work/item3-memory-20261003` in the existing planner worktree;
caller lane: `work/item3-memory-callers-20261003` in the existing spec worktree.
Both refreshed their local ownership receipts at base `40730ce2cd9`.
Selector tests `0131dfae5bf` precede implementation `69043e3fd64`; explanation
tests `db0b7694c29` precede renderer `0428efd8edb`. Independent review found a
fixture missing an explicit linear bound; it was corrected and re-reviewed.

Tests are authored, not executed. Supplied peak-extra-byte bounds do not
implement their compiler producer, actual lowering or measured NFR RSS gates.
The separate runtime-container CLI does not acquire memory admission through
this compiler-selector change. No runtime retry was made; the full objective
and release verification remain incomplete.

## Remaining work and stop conditions

### Continued implementation after the user's “go; do not stop”

Registry loading now has a closed SDN schema, source-bound snapshot validation,
module-scoped binding and a safe empty default configuration. The driver API
loads supplied source once per configuration and performs bounded validation;
at the shared pre-monomorphization boundary it checks actual declaration owner,
canonical typed ABI signature, receiver, arity and backend before publishing
analysis snapshots. Reconfiguration/failure clears old snapshots. Numeric
SymbolIds are not assumed globally unique. Default configuration does not
manufacture admitted standard-library metadata.

Module analysis connects the typed diagnostic collector with maximal unary
chain discovery, retaining source-located blockers and visiting nested argument
regions without duplicate chain suffix plans. It is analysis only: explicit-loop
normalization, proof production and emitted MIR replacement remain outstanding.

Both typed-column variants now offer checked mask/index/dtype/storage diagnostics
through their package facades. Dynamic adapters validate backing extents and
overflow before reads; legacy error behavior remains compatible. Dynamic
`array_uniq` now uses actual equality instead of display identity, with its
quadratic fallback explicitly tracked. `group_by_hashed` offers stable grouping
with explicit hash/equality callbacks and collision checks; equality-only
`group_by` remains available.

The SCV cold-create path now reuses its existing validated batch initializer.
Equivalence tests cover generations, flags and mixed/invalid fallback. This is
a source-level optimization, not a proven timeout root cause or measured speedup.
No exhausted diagnostic attempt was repeated and no admission was bypassed.

All new Simple tests are authored but unexecuted. Independent source reviews
have resolved identified issues; they do not replace runtime verification.

The user next requested continued coding. Query-CSE work uses isolated planner
and spec lanes `work/item3-query-cse-20261003` and
`work/item3-query-tests-20261003`, both based on `c92920d6806`.
Tests-first commits `a3861fefd52`, `aa45407a49a`, and parent `45fda607c84`
cover query ownership, framed constant identities, local/result redefinition,
consuming moves and effect barriers. The parent system slice is CP-MIR-01–05.
All remain unexecuted. Source commit `97ffa878e45` was integrated as
`623e56a178c` after the tests. Independent review found two follow-ups: retain
malformed-local rejection and reject string literal payload equality as general
runtime pointer identity. Test-first correction `d9efd1639dd` also adds a
supported scalar/local positive control. The unit and system additions total
25 scenarios, without claiming 25 passing checks.
Source follow-up `87d96188ab0` resolves both review findings. Three preexisting
hoisting fixtures were also corrected to assert preserved instructions and
terminators with zero hoist counters, matching the already-disabled production
hoisting implementation. Runtime tests and compiler/lib/MCP/LSP smoke gates
remain blocked; source review is not a substitute for those checks.

Runtime-looking names alone are not ownership evidence. The implementation
seam defaults to an empty admitted-read set; production admission is deferred
until authoritative MIR call origin/resolution exists. Its lost reuse opportunity
is recorded in `doc/08_tracking/bug/collection_query_cse_authority_performance_2026-10-03.md`.
This bounded repair does not implement the full loop/chain lowering pipeline.

1. Obtain an admitted self-hosted CLI and execute the test-first regressions;
   preserve actual RED and GREEN logs. A compiler failure is not a RED test.
2. Connect typed registry resolution, HIR extraction, proof construction,
   physical selection, MIR lowering, and generated artifact execution using the
   architecture/design contract. Retain exact original-region fallback.
3. Implement the remaining collection, generic-index, typed-column, diagnostics,
   profile, and explain requirements using the concrete system-test matrix.
4. Execute all retained semantic, backend, host and NFR gates. Generate the SSpec
   manual with the actual tool; authored documentation is not generated evidence.
5. Run the required compiler/lib/MCP/LSP and runtime/native smoke checks, review
   the exact owned diff and live PR comments, then land through a release-line PR.

Do not mark this objective complete because the documentation or selector guard
is ready. At most three fix/verify cycles are allowed per feature; do not repeat
already passing checks without changed code or new failure evidence.

## 2026-10-03 final bootstrap attempt and source checkpoint

Integrated source checkpoint `ad12ff62177` is pushed to draft PR #2285 targeting
`release/1.0`. Subsequent increments include explicit-contract generic map/set,
stable hashed uniqueness, opaque-source chain boundaries, retained canonical
loop provenance, literal source cardinality with consistency revalidation,
unsafe concat-rewrite rejection, and strict differential fixture admission.
Shared fixtures cover checked columns, closures/collections and generic indices.
All added Simple tests remain authored and unexecuted; manuals are not generated
execution evidence. Full REQ-001–011 and the release merge remain incomplete.

The third canonical Windows bootstrap attempt ended at 04:29:13 UTC before
stage-2 compilation. The stage-2 build wrapper returned 255; its log states:
`rss-guard: cap must be between 1 and 6835937 KiB (7000000000 bytes)`.
The launch requested 16777216 KiB. This is a resource-contract rejection, not
evidence of an Item 3 compiler or semantic failure. Producer artifacts and caches
are retained. No admitted self-hosted CLI/test runner was produced. No fourth
attempt is allowed in this session. A later scoped attempt must use a supported
cap and preserve the admitted producer generation; it must also distinguish
seed-delegated bootstrap tests from actual pure-Simple feature execution.

Evidence is retained outside sparse source worktrees at
`C:/dev/simple/.git/worktrees/simple-item3-spec-20261003/item3-bootstrap/attempt3`.
The pinned bootstrap source is `d53aed4ec74200a34ceb198a25de135e39bfe5e1`.
Do not use the Rust seed or a compile-only stage-2 artifact for normal tests.

The proposed typed indirect-call repair `d6d5b0a5fbf` stays isolated: independent
review found incompatible lifted-lambda producer signatures. Its tests and the
unimplemented scalar ORC contract are not integrated as completed implementation.
See the tracked typed-indirect ABI blocker for the exact producer/consumer gap.

## Explicit user resume: bounded recovery and ABI prerequisites

The user explicitly resumed implementation after the preceding blocked run.
The new recovery keeps one worker, a supported 5859375 KiB process-tree cap,
the admitted Rust producer generation, and seed test delegation disabled.
It permits three attempts; the earlier failed attempts remain terminal.

Recovery cycle 1 reused producer artifacts but failed Windows C admission:
MSYS reported status 125 despite creating an object. A tests-first repair uses
the existing native process adapter and clang-cl hyphen flags. Its real shell
regression failed before the repair and passed afterward, including malformed
input and missing-tool rejection. This is bootstrap evidence only.

Recovery cycle 2, pinned to `1d9824fe2d1`, passed C admission and preflight,
then rejected the old Stage 2 cache identity. The source identity changed for
the reviewed adapter repair; four tool version statuses changed from 125 to 0.
Runtime identity was unchanged. The cache contained one binding file and zero
usable entry objects. After preserving and hash-checking that file, cycle 3
uses canonical `--invalidate-cache=stage2` on the same output directory.
Rust, runtime and Cargo caches remain retained. Cycle 3 is the final attempt;
its fixed deadline is 2026-10-03 06:49:13 UTC, without extension.
Evidence: Git worktree metadata
`item3-bootstrap/recovery-20261003/cycle3` in the specification worktree.
No test-capable CLI or Simple semantic result is claimed at this checkpoint.

Reviewed implementation increments now include signed-zero binary decoding,
numeric join value oracles, captured-filter closure ABI and callback fixtures,
explicit LLVM link-option forwarding, target-owned standard libraries, and the
native output existence postcondition. Direct fixed extern signatures now
retain declared arity through MIR and LLVM, including zero-argument calls,
lifted lambdas and bootstrap initializers. An isolated raw owner declares 24
LLVM-C functions against inspected LLVM 23.1.1 headers and exports. It provides
no safe session, loaded-provider identity, or JIT invocation. Actual imported
owner calls still require verification; appended-source ABI tests alone do not
prove that boundary. All added Simple scenarios remain authored, unexecuted.

Full REQ-001–011, native/backend parity, measured NFRs, generated manuals,
production verification and the release-line merge remain incomplete.
