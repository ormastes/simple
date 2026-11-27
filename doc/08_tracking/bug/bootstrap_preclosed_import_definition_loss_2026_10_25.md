# Bootstrap preclosed source admission drops imported definitions

Status: provisional repaired-producer Hello and two-module positive passed;
rejected-admission runtime verification and full CLI checks remain pending.
This is independent of the exhausted MIR provider-diagnostic verification lane.

## Actual failure

The c635 producer's full Phase 3 run finished with exit 1 and quiescent cleanup,
without an RSS kill. The go-to-end receipt records 65 HIR errors in the entry
`app.cli.bootstrap_main`, one subsequent missing-entry-HIR MIR error, and zero
objects. The preserved child log records `preclosed:admitted selected=1455
closure_walks=0`. All 1,454 explicit `phase3:hir:file:done funcs=` records are
zero, with no missing function-count field. Generic memory-snapshot HIR counters
were unpopulated and are not evidence of actual function or symbol counts.
Monomorphization separately reported no generic functions or roots. The explicit
function-count audit is retained in the old run's
`evidence/explicit-hir-function-forensics.sdn`.

An independent two-module public native-build reproduced the same boundary:
`preclosed:admitted selected=2`, unresolved entry call `answer`, and the provider
reaching MIR with zero functions/instructions despite its real `answer() -> i64`
body returning 42. Native exit was 1, cleanup quiescent, peak RSS 74608 KiB,
requested jobs 24. Evidence is retained outside the source tree at
`C:/dev/simple-gnu-bootstrap-import-repro-20261025/evidence/compile-result.sdn`.
The minimal source is retained in `test/fixtures/bootstrap/preclosed_import_definition`.

## Source proof and bounded repair

`driver_source_pipeline_loading.spl` authenticates the preclosed request and its
source rows, but its `admitted_preclosed != nil` route deliberately skips the
entry walk. Both existing closure-mode publications are therefore skipped:
the ordinary entry walk and the mutually exclusive full-inventory branch.

`flat_ast_to_module` intentionally returns `flat_empty_module` for bootstrap
nonentry paths unless `flat_is_bootstrap_entry_path` observes legitimate closure
mode. This loses imports, public headers, and bodies before the streaming
surface builder can project them. Per-file HIR reparsing invokes the same
selected frontend, so it repeats the loss. HIR `module_build.spl` independently
needs this mode to resolve imported symbols. Removing only the parser guard
would leave that second gate incorrect.

The repair publishes `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` only at the final
successful preclosed source-load boundary, after physical source checks,
collisions, interface-index validation, and scan-cache release. Setter failure
and a failed driver-reader readback produce attributable errors with the
snapshot root. Existing signatures, closure receipts, source policy, parser
guard, and normal entry/full-inventory branches remain intact.

The marker remains live through selected parsing and HIR, matching the existing
entry-walk policy. The in-process native-build wrapper owns saving/restoring its
caller's state; child workers own their process lifetime. Rejected admissions
must leave the caller's prior marker unchanged. No environment override is
required in a launcher.

The driver gate consults explicit entry or the live closure marker. Bridge and
HIR readers directly call the real environment provider rather than memoizing
this value. Driver readback alone does not prove the compiled bridge/HIR
readers; the real two-module positive run is required. Streaming parsing keeps
its existing per-file transient scopes and ownership promotions. No whole-tree
AST retention is introduced.

HIR cache scope includes the closure marker, so existing empty-mode records
are naturally invalidated. Frontend flat-pool restoration still executes the
current bridge; it does not restore an authoritative empty ParserModule.
Nonbootstrap preclosed builds may incur a normal HIR cache miss after this
mode correction. No key, schema, or cache-admission bypass is added.

## Verification gates

- Actual Fable 5.1 high plan review ran, exit 0, model usage recorded. Its
  requested mandatory readback and post-release insertion are implemented.
- Actual Fable 5.1 high production code review ran, exit 0, actual model usage
  retained. It approved the 14-line patch text and explicitly gated merge on
  positive and rejected-admission validation. This is not a native or SSpec pass.
  Its example "exit 42" describes the returned value incorrectly: the fixture
  checks 42 internally and the successful executable must exit 0.
- Readback uses SOSIX's imported `io_runtime.env_get_nullable`, whose only
  provider call is `rt_env_get`, matching both consumers. Source loading makes
  no HIR-cache calls; streaming HIR computes the key after source-load success
  and surface parsing. No pre-marker HIR key is retained by this owner.
- Actual repaired producer `a0ca1dbc368c781f7162909dd14e1be164ed63f3d414d66226c2f68a2a7dab75`
  built in 53.7 seconds with 1,498 normal cache hits, three fresh modules,
  zero failed modules, native exit 0 and quiescent cleanup. Its real Hello
  and same two-module BOOT1 positive passed. The latter admitted both rows,
  retained one explicit function per module, resolved the imported call, and
  ran with exit 0 and `two-module-import-42` followed by LF. This is provisional
  compiler qualification, not full bootstrap or full CLI verification.
- The following full Phase 3 reached 100 explicit HIR completions and 1,573
  functions before the normal RSS guard stopped it with exit 88. MIR did not
  complete and zero objects were produced. This resource failure is retained;
  the preclosed definition repair is not a full Phase 3 success claim.
- Required rejection checks: genuine SCV/published selection with a corrupted
  receipt and a late source-admission failure must return failure while prior
  marker 0/1 is unchanged. A direct in-process harness must restore BOOT, entry,
  and closure state before its assertions on every outcome. These checks are
  authored but unexecuted. The four-case receiver uses a corrupted copy of a
  genuine receipt and a real `a-b.spl` / `a_b.spl` normalized-name collision,
  retaining original SCV custody. Its approved bootstrap-only build used the
  immutable 5a6 seed, exact repaired 60304 source and a private copy of the warm
  cache. Normal lookup reported zero reusable modules and 1,328 to compile;
  the minimum-one-cache-hit guard stopped the owned job with outer exit 143,
  quiescent cleanup, and peak RSS 1,225,964 KiB. No diagnostic executable was
  produced or run; no cold override, key forcing, or automatic retry followed.
  The collector final receipt was absent after interruption; the guard's raw
  root exit `0x0` is not compiler semantic success. Evidence is retained at
  `C:/dev/simple-preclosed-owner-negative-storage-20261025/evidence/terminal-result.sdn`.
  The receiver's separate Fable review timed out without a verdict. Negative
  marker preservation remains source-audited only, not a native-test pass.
- No full Phase 3 retry, Rust seed rebuild, codec retry, or relaxed memory guard
  has been used to validate this repair. The new cause has its own finite
  six-cycle maximum; the old MIR diagnostic lane remains stopped.

## Final rejection verification: six-cycle stop

The first minimum-zero bootstrap diagnostic attempt retained the same original
receiver source and normal private cache. It reached 1,245 per-file timing
completions before the unchanged 5,859,375 KiB RSS guard stopped it with exit 88:
peak RSS 5,921,700 KiB, peak commit 6,517,228 KiB, quiescent cleanup. No diagnostic
executable was produced and no receiver assertion ran. Cache performance remains
open; the changed entry closure had zero normal cache hits, not forced reuse.

The receiver then copied the real slim driver constructor and actual environment
policy resolver, avoiding the full backend facade. It still invokes the genuine
`load_sources_impl`, SCV acquisition and receipt publication, and preserves all
four cases and 24 assertions. The final source is SHA256
`ce387baa00c4081d180aed04d103efd9c4de2ba5a0c0b57c10d986854ee19a49`.
Its bootstrap-only compile built 1,058 fresh modules with zero failures in
177.1 seconds, native exit 0 and quiescent cleanup. Peak RSS was 5,228,680 KiB.
The actual link command selected generated core-C `simple_runtime.lib`; the
nominal Rust058 runtime directory is not evidence of its actual link provider.
This is diagnostic compilation evidence, not qualification of a Rust058 parent.

The first run wrapper failed before target startup because the fresh output
parent was missing (guard root PID 0, no samples). Its failed evidence was
preserved. The authorized corrected run used the same immutable executable,
SHA256 `3cdccde832e0ea57228d8ee0e3864a793d17dec20a1b7fa360bea9712124b0ae`.
It created the real temporary project, then exited 1/raw `0x1` at setup with
`actual diagnostic producer digest unavailable`, before any receiver assertion.
Cleanup was quiescent; peak RSS was 56,260 KiB and peak commit 104,608 KiB.

The failure boundary is the fixture's real `cli_current_exe_path()` followed by
`file_hash_sha256()` and its 64-hex requirement. Its stdout does not identify
whether executable-path lookup or the digest provider failed. This does not
demonstrate failure of the production 14-line source-admission change. The
four-case/24-assert negative requirement has NOT passed. No case is marked PASS.
Final bound evidence: `C:/dev/simple-preclosed-owner-negative-lean-storage-20261025/evidence-attempt3/final-terminal-result.sdn`
(SHA256 `7e0b1c4ed528cffef4b5355fbdeb9441c3fc73f9b34950813fa3a1350726d886`).

Conservative feature cycles are: old two-module reproduction (1), repaired
producer compilation (2), minimum-one stop (3), original receiver RSS failure (4),
lean receiver compilation/run-wrapper failure (5), corrected final run (6).
The six-cycle budget is exhausted. The preclosed feature is frozen: no further
fixture, build or run retry. Negative verification and mandatory full CLI gates
remain incomplete; the PR remains a draft. Independent read-only runtime-cause
analysis does not reset this feature budget.
