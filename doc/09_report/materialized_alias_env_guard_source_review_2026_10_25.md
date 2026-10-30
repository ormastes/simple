# Materialized-alias env guard source review — 2026-10-25

Status: **WARN / native NOT_RUN — focused source review complete; no open scoped P0/P1/P2 findings**. Independent review against HEAD `7bc0826bf89d6f6b5a240468b1453435505f94a8`, limited to the three files frozen in `build/review/env-guard-alias-source-freeze-v1.sdn` and their focused v2/v3 corrections. Concurrent CoreMux/Smux/Caret changes were preserved. The reviewer launched no fixture matrix, compiler, native helper, SSpec, product, or watchdog and made no production edits.

## Exact source pins

All three hashes independently match the freeze manifest and retained infrastructure receipt.

| Path | SHA-256 |
|---|---|
| `scripts/audit/direct-env-runtime-guard.shs` | `5f9a03ed09e2a7e83307de250cdf119b13e1f5ac38db164f995a393f8f8de556` |
| `scripts/audit/unchanged-materialized-alias.py` | `e3b03ba2fb8076ba02f0ae015cf662affdb56171649cf9784642dcb5cab3ef56` |
| `scripts/check/check-env-guard-materialized-aliases.py` | `be3f75b4893234a795dab4e61119baa755eb4b51d0900858f15dce6311b1f14e` |

## Original v1 finding (production source-closed by v2 below)

**P2: classifier resource use lacks a whole-invocation and byte budget.** The new normal guard invocation calls Python directly. The classifier's Git calls each have a ten-second timeout, but `check_output(cat-file blob)` buffers an unbounded blob and two `read_bytes()` calls buffer complete file contents. There is no content-size ceiling or whole-classifier deadline; the fixture harness's thirty-second timeout does not apply to the actual shell guard. A large committed descendant behind a legitimate alias can cause multiple complete allocations, while many path components/Git calls can accumulate their separate time limits. This affects a guard intended to conservatively refuse ambiguous cases instead of hanging or consuming unbounded memory.

Requested bounded correction: cap alias/path metadata and accepted leaf/blob size, check declared blob/file sizes before reading, use capped reads/output, and enforce a finite overall classification budget that returns refusal on exhaustion. Oversized, timeout, or uncertain cases must leave the original forbidden-call finding in place. Add only focused new infrastructure controls for the changed acceptance/resource boundary; do not rerun the already-green unchanged sixteen-case matrix without a relevant change.

## Reviewed authority and failure behavior

The shell invokes the classifier only after detecting a forbidden direct call, only in `--working`, and only in a Git checkout. Success skips this duplicate path; missing Python or any nonzero classifier status preserves the original finding. Allowed-owner handling and all/staged modes retain their prior behavior. The classifier does not consume a materializer receipt, so an old or forged receipt cannot authorize exemption.

The first qualifying alias must be a HEAD mode-120000 entry with an identical stage-zero index entry. Actual symlink text must equal the committed declaration; Windows junctions must resolve to that declared target. Alias parents, target components and canonical descendant components must be plain, rejecting nested symlink/reparse traversal. Relative target normalization happens before checking containment under the resolved repository root. Absolute, drive-qualified, backslash and control-bearing declarations are refused; canonical escape cannot become authority by resolving a junction.

The canonical leaf must be a regular HEAD-tracked blob with an identical index entry, outside the guard's canonical app/gc_async scope. The alias and canonical path must identify the same file. Both actual byte sequences must equal the committed blob. Filter and working-tree-encoding attributes refuse exemption. No EOL, text, case, clean-filter or other byte normalization is performed: CRLF divergence remains a finding. Thus new/modified/untracked/staged/retargeted/missing/escaping descendants do not gain an exemption merely because they look like a materialized alias.

The classifier rechecks alias/file identities, alias resolution, same-file identity, HEAD and index entries after reading. Exceptions and per-Git timeouts fail closed. These checks are conservative source classification, not a guarantee against a malicious concurrent filesystem administrator or unrestricted concurrent repository mutation. The resource issue above remains separate from alias-authority correctness.

## Retained infrastructure evidence

The author ran the actual production classifier and shell guard through `scripts/check/check-env-guard-materialized-aliases.py`, retaining private Git fixtures and logs under `build/review/env-guard-alias-fixtures-v1/`. Receipt: `receipt.sdn`; narrative: `build/review/env-guard-alias-repair-cycle1.md`. The receipt records **16/16 expected infrastructure assertions**, **16 classifier invocations**, and **15 shell-guard invocations**. This review independently matched all thirty-two retained production script copies to the frozen source hashes and inspected representative actual unchanged/modified guard logs. No matrix was rerun.

The fixture assertions compare actual process exit codes with the expected outcomes; they do not return a canned pass. Cases cover unchanged aliases, modified/new descendants, retargeting, untracked/staged aliases, staged canonical divergence, missing targets, escaping targets, filter/encoding ambiguity, an independent ordinary app violation, allowed-owner compatibility, nested reparse, forged receipt plus changed bytes, and CRLF divergence.

The missing-leaf case has classifier refusal and guard zero because no file/call remains to scan; this is not an exemption. The nested-reparse case executes the classifier only; its shell-guard value is -1/NOT_RUN to avoid Git recursively enumerating the deliberately cyclic fixture. It must not be counted as a shell-guard pass. Fixtures are retained, not recursively deleted, and test output-directory creation refuses reuse.

These are real infrastructure checks, **not native/Simple/SSpec application execution**. Native cases executed: **0**. The original failed working-tree receipt remains failed and untouched. Canonical working/staged checks and any actual application qualification remain separate parent-owned gates after source review closes.

## Focused v2 resource review

The three hashes independently match `build/review/env-guard-alias-source-freeze-v2.sdn`. Shell guard bytes are unchanged. The original sixteen-case matrix was not rerun. This review inspected only changed resource/supervision logic and the six new retained controls.

The production classifier now limits accepted source/blob reads to 1 MiB, alias declaration blobs to 4 KiB and metadata output to 64 KiB. It checks actual stat/fstat and committed `cat-file -s` sizes, reads at most the corresponding ceiling plus one, and refuses oversized or changed-size content. A controller gives its read-only daemon worker a five-second budget, then cancels admission of further Git spawns and kills/waits the registered child with a one-second reap bound. The registration lock does not cover output reads or waits. The standalone entrypoint exits without waiting for a daemon stuck in filesystem I/O. Git runs without lazy fetching, paging or filesystem-monitor hooks and with noninteractive settings. Unsupported flags/errors retain the shell finding. These changes close the original resource P2 for the scoped standalone classifier; a kill/reap error remains a nonzero failure, not an accepted duplicate or a claimed successful cleanup.

Actual focused infrastructure evidence in `build/review/env-guard-alias-resource-v2/receipt.sdn` records six new expected assertions passing: exact 1 MiB admission; oversized actual source; oversized committed blob with a small working file; oversized alias declaration; a blocked-child supervisor probe; and a blocked-read supervisor probe. There were four real shell-guard calls, four classifier CLI calls and two probes importing the exact production supervisor. The probes shorten only the imported wall-budget constant to 0.2 seconds. The child probe injects a real sleeping Python child at Popen and records accepted=false, 0.203 seconds, PID 45696 terminated/reaped with exit 1. The read probe records accepted=false at 0.188 seconds with no child. This is actual supervisor failure-path evidence, **not an actual hung-Git observation**, and the receipt's probe exit zero means its negative assertions succeeded, not that the classifier admitted an alias.

### V2 P2: fixture cleanup on supervisor exception (closed by v3 below)

`deadline_probe` restores its Popen substitution in a finally block, but recorded child cleanup occurs only after `classify` returns. If classification raises, for example from cancellation kill/wait, control skips that cleanup and can leave its real sixty-second fixture child alive. The existing successful receipts are valid for their observed paths, but the failing fixture path lacks owned cleanup.

Requested bounded correction: an outer finally always attempts kill/wait for every recorded fixture child, preserves exception/failure receipts, and keeps the **pre-cleanup supervisor-reaped observation** distinct from harness cleanup. Cleanup by the test must not convert a supervisor failure into PASS. Only a new controlled-exception infrastructure case is needed; do not repeat the unchanged sixteen original or six resource controls. No production classifier redesign was requested.

### V2 source pins

| Path | SHA-256 |
|---|---|
| `scripts/audit/direct-env-runtime-guard.shs` | `5f9a03ed09e2a7e83307de250cdf119b13e1f5ac38db164f995a393f8f8de556` |
| `scripts/audit/unchanged-materialized-alias.py` | `96e4530473c72a584213b542e9b3771c78ecee345106105ff93b6ab3c8267aae` |
| `scripts/check/check-env-guard-materialized-aliases.py` | `3f8240239c4cc77a411b9103c73e3e56ce8c5e7663076093eb08bf830350835c` |

## Focused v3 fixture-cleanup review

The author confirmed source freeze before review. All three hashes independently match `build/review/env-guard-alias-source-freeze-v3.sdn`; both production files retain their v2 bytes. Only the test harness changed. The source review is complete with no open scoped P0/P1/P2 findings.

The deadline probe now catches and records the classification failure and uses an outer finally to restore its Popen boundary and attempt kill/wait on every recorded child. Cleanup errors are retained. It snapshots whether the supervisor had reaped the children **before** the harness cleanup, and successful deadline assertions require both that observation and final cleanup. A supervisor exception or test cleanup cannot become a passing production-supervisor result.

The one new exception control deliberately substitutes a callable that spawns a real Python fixture child and then raises. This tests the harness's exceptional cleanup path, not the production classifier's exception-generation behavior. The retained `build/review/env-guard-alias-exception-v3/failed-probe.sdn` reports RuntimeError, accepted=false, supervisor_children_reaped=false, all_children_reaped=true, cleanup_errors=[], and passed=false. Probe exit is 1. PID 54744 is recorded terminated/reaped with exit 1. The outer control asserts exactly that failed inner outcome plus successful cleanup; its own receipt records one expected assertion passing. This distinction is truthful: it is one passing failure-control, not a classifier or native feature pass.

No original sixteen-case or six-case resource matrix was repeated. Retained evidence remains sixteen initial assertions, six additional resource assertions, and one harness exception-cleanup control at their respective source identities. Native/Simple/SSpec execution remains **0**. Canonical working/staged guard runs still belong to the parent and have not been represented as passing by this review.

### Final v3 source pins

| Path | SHA-256 |
|---|---|
| `scripts/audit/direct-env-runtime-guard.shs` | `5f9a03ed09e2a7e83307de250cdf119b13e1f5ac38db164f995a393f8f8de556` |
| `scripts/audit/unchanged-materialized-alias.py` | `96e4530473c72a584213b542e9b3771c78ecee345106105ff93b6ab3c8267aae` |
| `scripts/check/check-env-guard-materialized-aliases.py` | `faad2679e271dc9a3866a136ba7ca87cb85375f643901a28f941ee09f145d0e0` |
