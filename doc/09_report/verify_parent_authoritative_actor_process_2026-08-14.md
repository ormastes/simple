# Verification: parent-authoritative actor/process lane

## Scope

Changed actor admission/lifecycle, parent-owned process-result ingress, parent
application commit, piped child lifecycle, focused unit/system evidence, and
the canonical architecture, guide, expert knowledge, and plans.

## Results

- PASS: a full bootstrap admitted the pure-Simple Stage-2 binary at
  `build/bootstrap-restart12-current/stage2/x86_64-unknown-linux-gnu/simple`
  from current source and advanced to Stage 3. Its SHA-256 is
  `4c2d7d7328372175260d75ffd1ee2e475d9848a1d534c73ace7a9ef1eee0b68e`.
- PASS: the typed bootstrap receipt was emitted by the pure-Simple recovery
  planner and validated before the canonical full-bootstrap transaction.
- PASS by source inspection: the bootstrap core-C projection now carries the
  existing durable memory-snapshot open/record/close providers. Its focused
  projection test asserts the exact exported set and permits only the two
  explicitly native-all-owned heap counters unresolved. The test passed in the
  current terminal session, but no separate provenance-bound test log was
  retained, so this report does not promote it to retained executable evidence.
- PASS: the core C runtime capsule self-check passed all 33 checks after its
  coverage fixture gained the required string constructor.
- PASS: hosted Rust evidence passed checked actor invalid/heap/disconnected
  rejection, finite-capacity backpressure (2 tests), cooperative stop wakeup
  and single transition (1), hosted-symbol fallback (1), and common actor
  backpressure (1).
- PASS: Stage-2 execution proved mutation-after-offer process-frame isolation.
- PASS by static inspection: actor operations route through the scheduler
  owner; parent commit validates/applies/verifies before one publication;
  cancellation revokes retained frames; the focused specs have real assertions,
  five frozen system steps, and AC/REQ traceability.
- PASS: `git diff --check`, the working-tree direct-environment runtime guard,
  numbered-artifact guard, executable-spec layout guard, and focused
  placeholder/step-count scan.
- WARN: a resumed three-cycle Stage-3 pass on the rebased source first reached
  complete HIR and exposed an upstream-corrupted
  `defer_unsupported_marker` declaration. The declaration and focused
  regression were repaired. Cycle 2 was externally terminated under concurrent
  host memory pressure before a compiler verdict. Cycle 3, run after contention
  cleared, completed HIR for all 616 closure files and then reported fourteen
  remaining folded module constants without explicit types during MIR lowering.
  The cap forbids another diagnostic/build cycle in this session.
- PASS: the zero-module-constant recovery planner compiled with the retained
  Stage 2 when invoked through its documented `--entry`/`--source` interface;
  the resulting typed receipt authorized a replacement current-source Stage 2.
- WARN: the replacement Stage 2 began Stage 3 and parsed 200/617 files, then
  grew monotonically to 29,019,120 KiB RSS and was terminated with status 143
  before a compiler diagnostic or candidate. The retained progress receipt is
  `build/bootstrap-restart12-current/bootstrap-retry-progress.log`.
- WARN: the replacement Stage 2 supports only `compile` and `native-build`, not
  the Stage-4 `test`/SPipe commands. Its focused process-system native build
  reached link, then failed closed because the general core-C lane did not
  retain mutex/thread-sleep/piped-process providers. No stub fallback was used.
- WARN: the remaining Stage-2 system scenarios exposed aggregate/`Option`
  corruption: fragmented real-child delivery, atomic rollback, and cancellation
  did not produce valid executable verdicts. Assertions were retained.
- WARN: the deployed Stage-4 wrapper still exits 139 at its bounded test ABI
  probe. Consequently focused Simple tests, SPipe docgen/maintenance, and the
  compiler/lib/MCP/LSP Stage-4 gates are not admitted.
- REVIEW: the independent final audit's three source findings were resolved:
  real-child flows use owner-issued identity, issuance is monotonic under the
  sole parent mutex with zero/exhaustion rejected, and lock-failure receipts do
  not read canonical state. The reviewer still correctly withheld ACCEPT
  because the executable WARN gates above remain open.

The blockers are the Stage-3 RSS termination tracked in
`doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`
and the existing deployed-runtime failure tracked in
`doc/08_tracking/bug/native_selfhosted_run_segfault_startup_normalize_2026-07-24.md`.
No Rust seed result was substituted for Simple acceptance evidence.

STATUS: WARN

Integration reachability and post-rebase tree state are recorded after the
serialized push; they do not change `STATUS: WARN`.
