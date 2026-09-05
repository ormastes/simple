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
- UNRETAINED PASS: Stage-2 execution reported mutation-after-offer
  process-frame isolation, but this report has no exact retained command/log.
- UNRETAINED PASS: admitted Stage-2 focused process executables reported 8/8 inbox, 9/9
  owner, and 6/6 piped-session examples. This includes hostile/replay/budget
  ingress, copied retention, revoke/no-resurrection, deterministic drain,
  candidate apply/verify, mutation receipts, rollback, generation rejection,
  and close behavior. Exact shard commands and retained logs are absent, so
  these rows are historical session evidence rather than reproducible retained
  verification.
- PASS by static inspection: actor operations route through the scheduler
  owner; parent commit validates/applies/verifies before one publication;
  cancellation revokes retained frames; the focused specs have real assertions,
  five frozen system steps, and AC/REQ traceability.
- PASS: `git diff --check`; `direct-env-runtime-guard.shs --working`;
  `numbered-artifact-guard.shs --changed-from origin/main`; the executable-spec
  layout guard (`0` `.spl` files under `doc/06_spec`); SPipe dev-command wiring;
  and the focused placeholder/step-count scan (zero placeholders, 7 actor steps,
  11 process steps).
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
- PASS: the source-checkout runtime selector now rejects an incomplete staged
  Rust archive in favor of the complete core-C source capsule. The capsule
  passed 33 checks, linked the focused native specs without stub fallback, and
  includes checked opt-in SPL memtrack compatibility counters plus
  receiver-dispatched `rt_push`. Those counters do not cover core-C
  RuntimeValue allocations and are not Stage-3 heap-domain evidence.
- WARN: the replacement Stage 2 supports only `compile` and `native-build`, not
  the Stage-4 `test`/SPipe commands. The focused system executable linked and
  ran, but 3/4 scenarios failed. Its final bounded run proved nested aggregate
  return corruption directly: scalar lifecycle fields were coherent while
  returned `accepted` counters became invalid large values. The focused scalar
  owner/inbox/session shards remain PASS; the system assertions remain intact.
- WARN: the deployed Stage-4 wrapper still exits 139 at its bounded test ABI
  probe. Consequently focused Simple tests, SPipe docgen/maintenance, and the
  compiler/lib/MCP/LSP Stage-4 gates are not admitted.
- REVIEW: the independent final audit's three source findings were resolved:
  real-child flows use owner-issued identity, issuance is monotonic under the
  sole parent mutex with zero/exhaustion rejected, and lock-failure receipts do
  not read canonical state. The reviewer still correctly withheld ACCEPT
  because the executable WARN gates above remain open.

The blockers are Stage-2 nested aggregate-return corruption, the Stage-3 RSS termination tracked in
`doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`
and the existing deployed-runtime failure tracked in
`doc/08_tracking/bug/native_selfhosted_run_segfault_startup_normalize_2026-07-24.md`.
No Rust seed result was substituted for Simple acceptance evidence.

## Modern SSpec continuation (2026-08-16)

- PASS by source inspection: the process scenario now uses a closed
  `parent-commit-piped-result/v1` observation/oracle pair; all four scenarios
  have manual steps, and the authored mirror/test plan include cancellation.
- PASS by source inspection: a separate actor/channel scenario and authored
  mirror cover the implemented same-thread scheduler-authority boundary with
  closed `actor-channel-authority/v1` evidence. Cross-thread ingress and typed
  heap payloads remain excluded.
- BLOCKED: the exact command
  `SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native`
  exited 1 before scenario execution with `deployed Simple runtime failed its
  bounded test ABI probe`. No Rust seed was substituted.
- BLOCKED: the exact command
  `SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/actor_channel_authority_spec.spl --mode=native`
  independently exited 1 at the same bounded Stage-4 ABI probe before scenario
  execution. It was attempted once and was not retried.
- BLOCKED: neither authored mirror has pure-Simple docgen provenance or a
  seven-score maintenance verdict. Static gates are recorded after the final
  documentation diff; they cannot promote these executable blockers.
- REVIEW ACCEPT: a separate highest-capability reviewer accepted the corrected
  Modern SSpec/manual/plan delta after cancellation traceability stopped
  claiming moved-source invalidation. AC-5..AC-7 remain open.

## Non-Phase-4 repair continuation (2026-08-16)

- PASS: `src/lib/nogc_async_mut/actor/mailbox.spl` now keeps its bounded
  closed/full admission condition on one parser-safe line. The admitted
  pure-Simple Stage-2 compiler, with the documented SHA-256, no longer reports
  `expected Indent, found Self_` in the mailbox and advances into
  `actor/spawn.spl`.
- BLOCKED after the mailbox parse: the one bounded Stage-2 compile exited 70 on
  the existing flat-AST tag-39 conversion gap followed by the compiled
  `str.clear` receiver-dispatch gap. It was not retried, and no Rust seed or
  Phase-4 command was used.
- PASS: `runtime_memtrack.c` is normalized from mixed CRLF/LF to canonical LF;
  its staged semantic diff is empty and
  `normalize-line-endings.shs --check` passes.
- PASS: staged direct-runtime and numbered-artifact guards, repository diff
  whitespace, generated-spec layout (`0` misplaced `.spl` files), and the
  focused stub scan pass.
- EXCLUDED: the old `codex/runtime-server-actors-01a00035` branch was not
  merged. Its `STP1` codec duplicates the canonical `SPRF1`/`SPRS` boundary and
  its usage-spec paths are stale.
- EXCLUDED by user directive: every Phase-4 test, docgen, maintenance, and core
  CLI gate.

STATUS: FAIL (blocked)

Integration reachability and post-rebase tree state are recorded after the
serialized push; they do not change `STATUS: FAIL (blocked)`.
