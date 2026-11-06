# HIR repair campaign — 2026-11-07

**STATUS: INCOMPLETE. Runtime qualification is NOT_RUN.**

This record preserves the scope and evidence for release PR [#7356](https://github.com/ormastes/simple/pull/7356).
It does not close every historical HIR report or authorize release publication.
The campaign began 2026-11-06 19:59:59 UTC with a requested deadline of
2026-11-07 07:59:59 UTC. Earlier saved broad work remains in draft PR #7265.

## Repair and qualification ledger

| Cause | Current result | Remaining evidence |
|---|---|---|
| Split symbol-table guard owner | Guard repaired and landed in #7351; nine invariants and negative fixtures passed | Existing language/runtime regressions remain separate |
| Historical status-3 publication contradiction | Removed controller identified; historical bug note corrected in #7351 | No blanket archive runtime closure |
| Inferred Any aliases and written annotation authority | Exact symbol provenance retained through ordinary, tuple and pattern bindings; module copies and codec updated | Actual diagnostics, codec round trips, generator reproducibility |
| Codec traversal/resource bounds | Current schema reconciled with bounded writer traversal; canonical availability remains closed | Generated-code reproducibility and native round trips |
| Strict HIR ownership preflight | Preflight before interpreter side effects; imported effect authority and traversal bounds checked in source | Real positive/negative interpreter and driver executions |
| Stale import/re-export specs | Current APIs used with owner identity and invalidation assertions preserved | Execute the repaired specs |
| Required type payloads | Prior production repair retained; new real-source producer regressions authored | Execute producer and supported legacy-codec tests; canonical unavailability is asserted separately |
| Focused HIR worker counts | Existing closure clamp reused after memory admission | Native launch counts; unknown closure publication remains open |
| Focused HIR fallback | Unconfirmed worker retirement returns failure before MIR/fallback | Actual lifecycle tests; underlying native termination/reap contract remains open |
| Native session retirement | Canonical owner rejects unconfirmed reap and signal failures; 40 native assertions passed on Darwin arm64 | HIR caller migration, descendant scope and other platforms remain unverified |
| Built-in trait-bound erasure | Live local/imported erasure identified; scope options prepared | User scope selection, implementation, active call/driver verification |
| Historical i64-to-void failure | Six narrow retained-IR native checks passed | Original full failure not reproduced or closed |

Independent source reviews and scoped environment/layout/whitespace guards
passed. Ten blocking push gates passed at checkpoint
`c5fa284d61912dc24d509fddc42a8be44f405b2e` on release base
`854904fdf5513af730b395e660d179cdd8b00821`. Advisory, full compiler/lib/MCP/LSP,
package and performance qualification are not implied by those checks.

## Runtime evidence and limits

The admitted bootstrap producer has SHA-256
`a90ecfaae83431c9404aa8b55c79c50b62b0264390b65faeac263f1ebf1431b4`.
It supports compilation/native building, not the full CLI's run/test/check
commands. Another bootstrap session invalidated its original output directory.
The candidate, runtime, receipts and frozen verifier were preserved independently
under `/private/tmp/release100-hir-campaign-20261107/preserved-a90`.

The first relocated receipt replay failed on a missing MIR-retention log.
Seven omitted companion logs were recovered with exact receipt-bound hashes;
the changed bundle then passed canonical metadata-only relocation verification.
No receipt was edited, absent log fabricated, or candidate executed during replay.
This is bootstrap admission, not full-CLI or new-source qualification.

The narrow i32/text retained-IR diagnostic executed six assertions successfully.
Its compiler's SMF packaging failed because the backend produced Mach-O where
SMF required ELF. The later diagnostic executable does not turn that compile
failure into success. Its linker evidence pinned `/usr/bin/ld`, a launcher,
not the dispatched toolchain linker; exact transitive tool identity is unproved.

A separate production annotation-helper probe has sixteen assertions:

1. Envelope 1 stopped before compiler launch because its frozen supervisor
   omitted `bootstrap-session-exec.c`. Source/tool/runtime integrity passed.
2. Envelope 2 included the exact missing dependency. It imported and lowered
   119 production modules, then exceeded the enforced 2 GiB process-tree cap
   (peak 2,116,080 KiB, exit 88). Postflight integrity passed and the supervised
   session was quiescent. Retained IR contains only token-module functions,
   not the harness entry point. **Zero assertions executed.**
3. The final envelope used the supported native-build/low-memory route and
   native MIR eviction, retaining LLVM diagnostics. Canonical capacity admission
   refused 11,855 MiB available against its unchanged 12,288 MiB requirement
   (exit 3). No objects or IR were produced; integrity and supervisor quiescence
   checks passed. The three-envelope budget is exhausted.

The final envelope used the supported `--low-memory` native route.
Removing `SIMPLE_KEEP_MIR` alone cannot help this SMF path: its only read controls
native-output eviction, which SMF bypasses. No unchanged retry is authorized.

Detailed local evidence is in `/private/tmp/release100-hir-provenance-probe`.
No resource limit was lowered or raised to manufacture a passing result.

## Native session-owner evidence

The focused runtime repair passed 40 assertions on macOS 26.5 arm64 with
Apple clang 17.0.0. Compile exit was zero (0.316 seconds); execution exit was
zero (4.725 seconds). Bounds were 30 seconds for compilation, 35 seconds
externally for execution, and independent 30/12-second parent/helper alarms.
The fixture executes the actual C owner with syscall-only fault injection and
a real TERM-ignoring session leader. It covers signal denial, unconfirmed reap,
wait error, repeated EINTR, post-reap sweep failure and clock failure.

Source hashes remained unchanged; independent review matched all 40 successful
assertions and artifact SHA-256
`8e186c1f14c1d02e3df891c393511c9f621dcdcc90432baa2fffd7645b5bc65e`
to `/private/tmp/ptree-retirement-20261107.receipt.sdn`. No test was rerun.
This does not establish descendant disappearance, HIR caller migration, or
Linux/FreeBSD runtime behavior. A bounded reachability audit could not prove
HIR-only session confinement: the worker uses the generic native-build entry,
inherits backend/tool configuration and can reach shell-based source loading.
No shared worker migration or new strict-retirement API was implemented.
The focused fallback barrier remains a mitigation, not full lifecycle closure.

## Continuation constraints

- Keep PR #7356 draft until required actual runtime checks pass. Source review
  and authored manuals are not substitute execution evidence.
- Preserve other sessions' work and active bootstrap directories. Revalidate
  exact candidate/source/runtime/tool identities before any new execution.
- Preserve the first failed replay and all three probe envelopes. At most three
  envelopes were allocated to this probe and are exhausted. Do not retry this
  probe without an explicit new budget. Never rerun unchanged green checks.
- The prior requalification and bounded-FS repair budgets remain exhausted.
  The earlier memory lane used four of six cycles. Do not reset these counts
  by moving worktrees or renaming a cause.
- Built-in trait semantics and a diagnostic reserve exception remain pending
  user decisions. Elapsed time is not approval.
- Full CLI construction is resource-blocked. Configured remote ARM64 runners
  were offline at discovery. An active independent bootstrap may produce a
  usable runtime later; do not assume its outputs are already admitted.
