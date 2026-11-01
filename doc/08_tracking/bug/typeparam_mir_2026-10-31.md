# typeparam MIR failure: static generic class factory leaves T unsubstituted (2026-10-31)

## Root bug
`Future.from_value(x)` / `Future.pending()` (static fns of generic `class Future<T>`,
src/lib/nogc_async_mut/async/future.spl) reach MIR lowering with `T` unsubstituted in the
stage2 compiler: `E-MIR-TYPE-TypeParam` (src/compiler/50.mir/_MirLowering/function_lowering.spl).
Explicit `Future<bool>.from_value(..)` and a typed `val f: Future<bool> = ...` do not help
(verified with pinned stage2). Direct construction
`Future(state: [], poll_result: Poll.Ready(v))` under a concrete return type lowers fine.

## Workaround sites (all tagged `@workaround bug=typeparam-mir-20261031`)
- src/compiler/80.driver/cache/module_artifacts_v1.spl: helper `_ready_future_bool_v1`; 7 call sites in `module_artifact_publish_atomic_async_v1`
- src/compiler/80.driver/cache/source_reader_v1.spl: helpers `_ready_future_text_v1`, `_ready_future_module_v1`; 2 sites in `SourceReader`
- src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl: helpers `_ready_future_blob_v1`, `_pending_future_blob_v1`; 2 sites in `future`

## Removal condition
Remove once the root fix (mono/HIR substitution of class type args for static generic
calls) is in the stage2 used for bootstrapping.

## Update 2026-11-01: lib.nogc_async_mut.io.buffer and stage3 status

### io.buffer workaround (phase-3 unblocker)
The 2026-10-31 lambdaabi workaround (a81f7765c79) replaced the eight `.then` lambdas in
`src/lib/nogc_async_mut/io/buffer.spl` with inline `poll()` matches, but every branch still
returned through `Future.from_value(..)` (18 sites) or `Future.pending<R>()` (8 sites) --
exactly the static generic factories that trip this bug. Pinned stage2
(`C:/dev/p3new/stage2.exe`, 2026-10-27) therefore still failed the module with
`E-MIR-TYPE-TypeParam` on current `release/1.0.0` (see evidence below).

All 26 sites now go through file-private helpers, tagged
`@workaround bug=typeparam-mir-20261031`, that construct the Future directly under a concrete
declared return type (same shape as the cache-module helpers above):
- `_ready_bytes_result_future` / `_pending_bytes_result_future` -- `Future<Result<[u8], IoError>>`
- `_ready_text_result_future` / `_pending_text_result_future` -- `Future<Result<text, IoError>>`
- `_ready_unit_result_future` / `_pending_unit_result_future` -- `Future<Result<(), IoError>>`
- `_ready_count_result_future` / `_pending_count_result_future` -- `Future<Result<i64, IoError>>`

Behaviour is identical: `Future.from_value(v)` is `Future(state: [], poll_result: Poll.Ready(v))`
and `Future.pending()` is `Future(state: [], poll_result: Poll.Pending)` (future.spl:30-47).

One more stage2 failure in the same module was masked behind the TypeParam errors and
surfaced once they were gone: `unresolved method call: slice` in `AsyncBufferedReader.read`
(`val chunk = data.slice(0, take)` in the `case Ok(data)` refill arm). Typing only the
receiver (`val refill: [u8] = data`) or only the index (`val take: i64 = ...`) each still
failed; the site now slices the just-assigned typed field (`self.buf.slice(0, take)`) with an
`i64`-annotated `take`, same shape as the working buffered-path site a few lines above.
Tagged with the same `@workaround bug=typeparam-mir-20261031` marker.

Evidence (pinned stage2 `C:/dev/p3new/stage2.exe`, `compile --format=smf --source src/lib
--source src/compiler --source src/app` on an entry importing `std.nogc_async_mut.io.buffer`,
64-module closure, 8 GB watchdog, peak RSS <1 GB, ~56 s each):
- original buffer.spl: `failed=2`, 18x `E-MIR-TYPE-TypeParam` + 2x pre-existing
  `E-RTI-007 enum:Poll::unwrap` (lib.nogc_async_mut.async.poll, out of scope)
- workaround buffer.spl: `failed=1`, 0x `E-MIR-TYPE-TypeParam`; only the poll module remains
- minimal repro above: the `Future.from_value` form adds exactly one `E-MIR-TYPE-TypeParam`
  on top of the poll errors; the direct-construction form does not.
A `native-build --entry-closure` of the same 64-file closure exceeded the 8 GB cap at ~207 s
in the in-process HIR shard and was killed; the SMF path reaches the same MIR lowering.
Regression spec: `test/01_unit/lib/nogc_async_mut/io/async_buffer_typeparam_wa_spec.spl`
(Ready/Ok, Ready/Err, Pending per element type, plus a source guard that no
`Future.from_value(` / `Future.pending<` call returns to buffer.spl).

The three cache modules named in the 2026-10-27 phase-3 log
(`compiler.driver.cache.module_artifacts_v1` x7, `compiler.driver.cache.source_reader_v1` x4,
`compiler.driver.cache.daemon.cache_single_flight_v1` x2) were already covered by the
2026-10-31 helpers listed above (035619a4f4a); no `Future.from_value`/`Future.pending` call
remains in them. Re-verified 2026-11-01 with pinned stage2 (`compile --format=smf`, entry
importing all three modules, 282-module closure, peak RSS 4.26 GB, 504 s):
0x `E-MIR-TYPE-TypeParam`, 281/282 modules lowered; the only failure is the poll module below.

### Minimal repro
```simple
use std.async.future.{Future}

fn ready_flag() -> Future<bool>:
    Future.from_value(true)

fn main() -> i64:
    if ready_flag().is_ready(): 0 else: 1
```
Expected: builds. Actual (stage2 2026-10-27, `native-build --entry-closure`):
`MIR lowering error: E-MIR-TYPE-TypeParam: unsubstituted generic type parameter 'T' reached MIR lowering`.
Replacing the body with `Future(state: [], poll_result: Poll.Ready(true))` builds.

### Root cause in current src/compiler (stage3) -- still present, source-traced 2026-11-01
Not verified by running a stage3 binary (none was available in this session); traced in source:
- Callee side: `src/compiler/20.hir/hir_lowering/_Items/class_declaration_lowering.spl:163-165`
  marks every method of a generic class -- static ones included -- `is_generic_template = true`;
  `src/compiler/50.mir/_MirLowering/module_lowering.spl:3540-3543` skips lowering such functions
  and 3450-3453 only records them in `generic_template_fn_symbols`. With the 40.mono pass removed
  (ab9305d783e, 56c0499ebd1) nothing instantiates `Future<bool>::from_value`.
- Guard: `refuse_generic_template_call` (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:230-248`,
  E-GEN-001) has one caller (line ~8627) and covers plain direct path calls only.
- Gap: static method calls go through `lower_method_call`
  (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, `StaticMethod` resolution
  ~2390, static branch 4432-4556). That branch lowers the arguments against the callee's declared
  parameter types (`value: T`, line ~4538) and takes the return type from
  `resolved_call_return_type(resolved_static_method_id)` (`Future<T>`, line ~4541); both reach
  the `HirTypeKind.TypeParam` arm in `function_lowering.spl:1460-1464`. The owner's generic
  arguments -- from an explicit `Future<bool>.`, the expected type, or the argument types -- are
  never bound when the static receiver is resolved by its bare class name, which is why the
  explicit forms do not help. It then emits a direct call to a symbol that is never emitted.
- Fix options (owner: the concurrent generics erased-body work in `src/compiler/50.mir`;
  not changed here): bind owner type args for `StaticMethod` calls from the explicit receiver
  type args / expected type / argument unification before lowering parameter and return types,
  and instantiate (or erase) the static template; or at minimum route the static branch through
  `refuse_generic_template_call` so the failure is E-GEN-001 at the call site rather than
  E-MIR-TYPE-TypeParam deep in type lowering.
