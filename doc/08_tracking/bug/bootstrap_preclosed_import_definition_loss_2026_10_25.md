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
