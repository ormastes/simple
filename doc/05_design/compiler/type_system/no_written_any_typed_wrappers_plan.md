# Written-Any removal: typed wrappers, no erasure (design, read from origin/release/1.0.0)
Fable review 2026-10-27: closure-free kept-list adopted; generic-extern ABI and kept-list classification verified.

## 0. Key finding
`rt_rc_share/retain/release/count` and `rt_heap_graph_bytes` are ALREADY declared generic: `extern fn rt_rc_share<T>(value: T) -> bool`
(src/lib/nogc_sync_mut/sffi/host.spl:434-443). The `Any` in the 19 sites was never needed to call them. Most sites need NO erasure.

## 1. Classification of all 19 sites
| # | site | stores / reader | class | rationale |
|---|------|-----------------|-------|-----------|
| 1-5 | global_dataset.spl:23,27,31,35,39 `_sffi_*(value: Any)` | param of 1-line ffi shims | (a) | make fn `<T>(value: T)`; body stays `unsafe(ffi)` |
| 6-10 | global_dataset.spl:44-48 RcPort `fn(Any)->..` | injected port; caller = GlobalDataset only | (a) | `RcPort<T>` |
| 11 | global_dataset.spl:92 `values: [Any]` | rows of ONE dataset; product callers: none | (a) | `[T]` |
| 12 | global_dataset.spl:111 `_count(v: Any)` | private | (a) | `v: T` |
| 13 | global_dataset.spl:149 `put(value: Any)` | spec only | (a) | `value: T` |
| 14 | global_dataset.spl:175 `acquire -> Any?` | spec only | (a) | `T?` |
| 15 | build_session.spl:71 `_sffi_session_rc_share(Any)` | shim | (a) | `<T>` shim inside thunk helper |
| 16 | build_session.spl:81 `SessionEndPort.share: fn(Any)` | called once per kept value | (c)->thunk | heterogeneous, share-only, never read back |
| 17 | build_session.spl:115 `end(kept: [Any])` | only caller driver_orchestration:195 | (c)->thunk | `SessionKept` |
| 18 | build_session.spl:131 `end_with(kept: [Any], port)` | spec + end() | (c)->thunk | same |
| 19 | driver_orchestration.spl:201 `-> [Any]` | 3 [Error]/[Warning]-like lists, 4 mir/hir lists, CompileResult | (c)->thunk | open heterogeneous, behaviour-only |
Class (b) closed enum: not applicable (kept values are unrelated structs; an enum would only re-wrap them and force every module to import all
product types into build_session). Class (d) dyn Trait: no `dyn` in syntax_quick_reference.md; not needed, a closure is the behaviour.
Key<T>/type-id (c-classic): NOT needed. Nothing ever reads a kept value or a dataset value back by heterogeneous key; the only `get`
(`acquire`) is per-dataset homogeneous. No type-id/type-name intrinsic exists (grep host.spl, reflection: none), so Key<T> would first need a
new intrinsic; recommend against. If a heterogeneous dataset is ever required: one `GlobalDataset<T>` per T, owned by the consumer.

## 2. Storage constraint and the three options
written_any_unsafe_depth (types.spl:107, checked :1351/:1353) is only bumped by the `unsafe(capabilities:[type_erasure])` EXPRESSION
(expression_core.spl:1332-1335; lambda bodies reset it to 0 at :1151-1181). Field/param/return annotations are lowered outside it, so a
field typed `Any` can never be legal. Verdict per option:
- (c) generic-all-the-way: CHOSEN for all 19 sites. Zero erased storage, zero casts, zero `unsafe(type_erasure)`; only `unsafe(ffi)` remains
  inside the rt_rc_* shims. Because there is no erased field, the constraint is moot.
- (a) raw handle (i64): no box/unbox-to-handle op for arbitrary T is exposed in host.spl (searched rt_value_*box/unbox/handle: none).
  Would need a NEW runtime pair; also loses refcount typing. Reject. (Only fallback if a site proves un-genericizable: none found.)
- (b) `@unsafe(capabilities:[type_erasure])` on struct/class/fn raising the depth while signatures lower: `@unsafe(reason, capabilities)`
  already parses on extern fn (host.spl:434). Change = read that attr in the decl-signature lowering (the callers that lower field/param types,
  then `self.written_any_unsafe_depth += 1` around them, mirror of expression_core.spl:1332-1335) ~25-40 lines + parser accept on struct/class
  + 1 spec. Not needed now; keep as the sanctioned escape for a future genuine erasure. I did not locate the exact decl-lowering line.
  (b) would also be where test/ gets its escape if chosen (see 5).

## 3. New signatures
### 3.1 src/lib/nogc_sync_mut/mem/global_dataset.spl
```
fn _sffi_rc_share<T>(value: T) -> bool          # + _retain/_release; _count<T> -> i64; _sffi_heap_graph_bytes<T> -> i64
struct RcPort<T>:
    share: fn(T) -> bool
    retain: fn(T) -> bool
    release: fn(T) -> bool
    count: fn(T) -> i64
    graph_bytes: fn(T) -> i64
fn rc_port_runtime<T>() -> RcPort<T>
class GlobalDataset<T>:   # fields as today, `values: [T]`, port: RcPort<T>
    fn _count(v: T) -> i64
    me put(key: text, value: T) -> Result<bool, text>
    me acquire(key: text) -> T?
    # release/remove/clear/stats/entry_count unchanged
fn global_dataset_with_port<T>(port: RcPort<T>, limits: GlobalDatasetLimits) -> GlobalDataset<T>
```
The `unsafe(type_erasure)` blocks in `_count`, `put`, `acquire` are deleted (they only existed to excuse Any).
Singleton `global_dataset()` / `var _global_dataset` : a generic module `var` cannot exist and it has ZERO callers in src/test
(grep: only the spec uses `global_dataset_with_port`). DELETE it (CLAUDE.md: never keep unused code). Add `global_dataset_new<T>() -> GlobalDataset<T>`
(= with_port(rc_port_runtime<T>(), limits_load())) only if a product consumer appears.
### 3.2 src/compiler/80.driver/session/build_session.spl
Drop the duplicate `extern fn rt_rc_share<T>` at build_session.spl:43; import the host.spl declaration instead.
```
struct SessionEndPort:  heap_end: fn(u32) -> bool        # share removed; no longer generic
struct SessionKept:     all_ok: bool, values: [(T, bool)]  # snapshots active && end_enabled; eagerly shares each value, records result
fn session_kept_begin(session: BuildSession) -> SessionKept:  # snapshot active and end_enabled to a bool at call time
    SessionKept(all_ok: session.active and session.end_enabled, values: [])
me keep<T>(k: SessionKept, value: T) -> void:  # eager share; record result without lambdas
    var ok = rt_rc_share(value)
    k.all_ok = k.all_ok and ok
    k.values.push((value, ok))
me end(kept: SessionKept) -> bool:  # share all in order, fail closed on first false, then heap_end if all succeeded
    var heap_ok = true
    if kept.all_ok:
        heap_ok = heap_end(0)
    heap_ok and kept.all_ok
me end_with(kept: SessionKept, port: SessionEndPort) -> bool:  # same order and fail-closed semantics
    # loop each value in order: if not all_ok or port call fails, eprint and return false at first failure
    # then heap_end only if all succeeded
```
Behaviour identical to today: share all in order, fail closed on first false, then heap_end. No lambdas; eager share eliminates closure-capture risks.
### 3.3 src/compiler/80.driver/driver_orchestration.spl:201
```
fn session_kept_values_v1(result: CompileResult) -> SessionKept:
    var kept = SessionKept(shares: [])
    kept.keep(self.ctx.errors); kept.keep(self.ctx.warnings); kept.keep(self.ctx.visibility_warnings)
    if retain-products: kept.keep(mir_modules); keep(cold_hir_typed_receipts); keep(runtime_std_hir_emissions); keep(runtime_std_mir_emissions)
    kept.keep(result); kept
```
No `unsafe` block at all (the existing one is deleted).

## 4. Callers to migrate (grep, all of src/test/examples minus compiler_rust)
- global_dataset: only test/01_unit/lib/mem/global_dataset_spec.spl (lines 7-8, 48-54: `RcPort<i64>`-style port + `GlobalDataset<T>` annotations;
  fns `_f_share` etc. take T). native_build_main.spl:1056 and bootstrap_hir_store_spec.spl:165 are comment-only.
- build_session: driver_orchestration.spl:195/201 (BuildSession.end), driver_types.spl:21/640 (`build_session_inactive`, unchanged API),
  test/01_unit/compiler/driver/build_session_end_spec.spl:8-9,32-33,36,79 (SessionEndPort fake -> thunk fakes).
- No other importer of SessionEndPort/RcPort/session_end_port_runtime/rc_port_runtime.

## 5. PR split (each: red spec first, then green; spec runs in interpreter mode, which never forbids Any, so red = a new native-compile/
##    lowering spec asserting zero E-ANY-COMPILE-001/W-ANY-COMPILE-001 for the touched file, using forbid_written_any=true like written_any_scan)
1. PR-A global_dataset generic: red = `global_dataset_generic_spec` (GlobalDataset<text> and GlobalDataset<[i64]> in one process, put/acquire typed, no `Any`
   in file via written_any_scan.spl). Green = 3.1; delete singleton; update existing spec. Regenerate scripts/check/any_inventory_baseline.txt with the ratchet's --generate-baseline (it FAILs stale when the count falls); if the ratchet's selftest fails on the host, record that and regenerate on Linux CI.
2. PR-B SessionKept/SessionEndPort: red = build_session_end_spec rewritten to `SessionKept` + failing-thunk-at-index test (fail-closed, heap_end not called).
   Green = 3.2 + 3.3 together (same atomic change since end() signature moves). Regenerate scripts/check/any_inventory_baseline.txt; if ratchet selftest fails on host, regenerate on Linux CI.
3. PR-C ratchet-to-zero evidence: spec that runs written_any_scan over src/ minus compiler_rust and asserts 0 product sites (red until A+B merged;
   do not land C before them). Cleans stray `unsafe(type_erasure)` blocks left empty. Regenerate scripts/check/any_inventory_baseline.txt; run check-any-inventory-ratchet.shs to verify --generate-baseline succeeds.
4. PR-D test/ + fixtures (see 6), then PR-E flip.
5. PR-E: `driver_hir_forbids_written_any` (driver_hir_pipeline_lowering.spl:264, TODO at :263) -> `ctx.options.mode != Interpret` (drop the strictness
   clause). Exclude src/compiler_rust by construction (seed lib copies are not compiled by the self-hosted driver; the 314 sites there are not touched
   and a path guard `not path.starts_with("src/compiler_rust/")` is added if the driver ever sees them). Red: spec compiling an `Any` field in non-interpret
   ctx expects E-ANY-COMPILE-001 error (today warning). Cache identity already folds the flag (driver_hir_source_body_custody_identity_v1.spl:50,99).
   Also remove the stale 5 unconditional eprint sites only if still reachable (warning path unreachable once error). Limit the flip to build modes `Aot` and `Jit`
   (driver_compile_options.spl:94; driver_api_compile_single.spl:22 defaults Check); must not apply it in Check/LSP, or PR-D must also wrap natively compiled specs.

## 6. test/ and fixtures (reuse of anycensus census, scratchpad/anycensus/report.md, written_any_scan.awk)
Census: 776 outside-unsafe sites; src/compiler_rust 314 (excluded); product src ~27-29 lines (of which our 19 + ~8 others are in the census scope
list in report.md and must be checked in PR-C); test/01_unit 230 + test/unit 131 (mirror dup of 01_unit) + test/fixtures 48 + other test/ 24 = 433,
~300 unique after de-mirroring. Interpreter-mode specs are unaffected by the flip (mode == Interpret never forbids), so the 02_integration/unit
specs run by `bin/simple test` keep working. Recommendation:
- test/01_unit and test/unit specs (run interpreted): EXEMPT for the flip, do not wrap in unsafe (wrapping 300 sites adds noise and hides that most are
  concurrency/mock fixtures that should become `<T>`); instead keep the ratchet script (check-any-inventory-ratchet.shs, per census item 4) at current count, tighten on touch.
- test/fixtures (48): these are compile probes (e.g. any_optional_boxing.spl) and ARE natively compiled -> the only place Any-in-unsafe is right:
  wrap the Any use in `unsafe(capabilities:[type_erasure]):` or, where the probe intentionally tests Any lowering, mark it expected-diagnostic.
- Natively compiled specs (test/05_perf 7, test/native 1, test/03_system natively-built ones): same as fixtures.
After PR-E, run `--mode native/compile` over test/01_unit (test_runner_execute.spl:909,1327) and `check`/LSP on specs to verify error detection.
Do the fixture/native wrap in PR-D BEFORE PR-E, else native test lanes go red.

## 7. Dependency on TLDR generic-instance work
Status: open. doc/08_tracking/bug/generic_instance_plan_has_no_consumer_pg6_2026-10-25.md (P-G6, filed by P-G5 #4628): the instance build
plan (generic_instance_build_plan_v1.spl) has NO consumer; instances are still emitted once per using object with COMDAT linkage; generic
function templates have no ConcreteTldrKey (Gap 2: only generic struct/class are keyed). Impact: PR-A/B add `RcPort<T>`, `GlobalDataset<T>`,
`SessionKept.keep<T>`, `_session_share_thunk<T>` (generic FUNCTIONS, the Gap-2 kind). They are SAFE NOW: correctness is unchanged (COMDAT per object),
cost is up to 9 duplicate thunk instances in driver_orchestration's object, which is negligible. They do NOT need to wait for P-G6, but note the
cache effect: generic-fn instances in the driver object are not independently cacheable until Gap 2 closes. Owner not recorded in the bug file
(filed by P-G5 / #4628 author); ask that owner before PR-B if cold-cache driver rebuild time matters.
Risk retired: the kept-list uses no closures (eager share in keep<T>), so the capturing-generic-lambda native gap does not apply.
