# rb4 Phase 3 AVs in surface_build on any struct field of fn type with parameters (turbofish `_sffi_tuple_get<[Type]>` return erased by the pre-#10930 Phase 2) (2026-11-23)

Status: OPEN (draft, uncommitted — W38/W39 localization). Compiler-side fix already on
`origin/release/1.0.0` (`37f7c2b6d8e`, PR #10930); the rb4 pin `a8bb3822cf2c` predates it.
Severity: blocks the Phase 3 -> Phase 3 fixpoint (and P3 -> P4) on Windows MSVC.
Compiler under test: canonical rb4 Phase 3 `stage3/x86_64-pc-windows-msvc/simple.exe`
(sha256 `217e9a9de4f275ab…`, built by the fixed Phase 2 rb4 `stage2-admitted/simple.exe`
(sha256 `cf131adc7dbb278…`) from release/1.0.0 `a8bb3822cf2c`; 9/9 shards, 1619/1619 modules;
hello_world, p2_add and the W35 probe PASS when P3 compiles a small closure).
Lane: `C:/dev/simple-release-boot-20261122/build/rboot/manual-p3to3-rb4.sh` (exact Stage 3
transcript argv/env replay, `SIMPLE_MIR_SHARDING=1 SIMPLE_FRONTEND_CACHE=0`, `SIMPLE_BINARY`
overridden to P3, private caches; W38 in `build/rboot/WORKAROUNDS.md`).

## Symptom (W38)

`manual-p3to3/manual-p3to3.log:16513`:

```
[mir-shard] owner=0/9@0 status=CRASH exit=-1073741819 claimed=0 sealed=0 finished=false ntstatus=0xC0000005 (access violation)
```

Last worker progress line (`:16512`), file 64/1627 of `phase=surface_build`:

```
[build] phase=surface_build ... done=64 total=1627 ... current=.../src/compiler/70.backend/backend/static_backend_llvm_port.spl
```

`log_build_progress("surface_build", …, source.path, …)` is emitted AFTER
`ModuleSurfaceBuilder.add_parsed` returns (`driver_source_parse_retained.spl:380-391`), so the
AV is in file 65 = `src/compiler/70.backend/backend/static_jit_lane.spl` (same order in the
canonical run), not in llvm_port. All 1627 files were already parsed (last
`phase2:parse:file:done …/sffi/net.spl` at +814493 ms; crash ~4 s later). Frontend cache OFF
(not W27). Two attempts, same place.

## Root cause

`static_jit_lane.spl:17-22` declares

```
pub struct StaticJitLaneV1:
    jit_run_fn: fn([MirModule]) -> CompileResult
    execute_smf_fn: fn(text) -> CompileResult
    hir_jit_fn: fn(HirModule) -> Result<BackendResult, BackendError>
    ...
```

The surface builder collects the named-type dependencies of every struct field through
`compiler.frontend.parser_types_expr.parser_type_named_dependencies_into`
(`src/compiler/10.frontend/parser_types_expr.spl:346`). Its `TypeKind.Function` arm at the pin is

```
    if disc == rt_enum_discriminant(TypeKind.Function([], placeholder)):
        if val params = _sffi_tuple_get<[Type]>(payload, 0):
            for param in params:
                parser_type_named_dependencies_into(param, names)
```

`_sffi_tuple_get<T>` (`:44`, `fn _sffi_tuple_get<T>(tuple: i64, index: i64) -> T?`) is a
generic direct call with an explicit turbofish. The pre-#10930 Phase 2 does NOT substitute the
turbofish type args into the direct-call return type, so `params` lowers as an erased/Infer
value instead of `[Type]`; the `for` then hands each element to the recursive call as a bare
word, and the callee's first field read `val kind = type_.kind` dereferences it. In P3 the
decoded value was `0x52db0c7dfc` (tag bits 4, i.e. not a record pointer):

```
=== AV-1ST ===  ExceptionAddress: 00007ff753b1d3d6 (simple+0x28d3d6)  c0000005  Attempt to read from address 00000052db0c7dfc
rcx=rdx=00000052db0c7dfc
  mov eax,ecx ; and eax,7 ; mov rdx,rcx ; and rdx,~7 ; cmp eax,1 ; cmovne rdx,rcx ; mov rax,[rdx]   <- AV
simple+0x28d3d6 = compiler.frontend.parser_types_expr.parser_type_named_dependencies_into+0xb6   (aot-2292d040….o)
return addresses on the raw stack (no unwind info in the P3 image):
  parser_type_named_dependencies_into+0x814  (the recursive call, Function arm)
  parser_type_named_dependencies+0x10e
  compiler.hir.hir_lowering.module_surface_declarations.module_surface_from_owner+0x2ed0
```

(`build/rboot/gate-probe2-cdb/p3/cdb.log:51-400`; symbolized with `scratchpad/dbg2/sym.py`.)
Zero-parameter fn types never enter the loop, which is why `driver_types.spl:397`
(`fn() -> Result<KernelImageDigestV1, text>`, file 43 of the Stage 3 order) passed.

### Minimal reproducer (20 s per build, `build/rboot/gate-shapes-rb4.sh`, `build/probe/shapes/*.spl`)

Single-file entries (hello-world shape + one declaration), `native-build --backend llvm
--runtime-bundle core-c-bootstrap --entry-closure --mode one-binary`:

| shape | declaration | P3 (217e9a9d) | P2 (cf131adc) |
|---|---|---|---|
| A | `struct SA: f: fn(text) -> bool` | **AV 139 in surface_build** | PASS |
| B | `struct SB: f: fn([text]) -> bool` | **AV** | PASS |
| C | `struct SC: f: fn() -> Result<bool, text>` | PASS | PASS |
| D | `struct SD: f: fn(text) -> Result<bool, text>` | **AV** | PASS |
| E | `struct SE: f: fn([text]) -> Result<bool, text>` | **AV** | PASS |
| F | `fn set_op(op: fn(text, [text]) -> bool) -> bool` (fn-typed PARAMETER, no struct) | PASS | PASS |
| G | struct with `fn(text, text, [text], text) -> Result<bool, text>` field + module `var` holding it | **AV** | PASS |

So: every struct field whose type is `fn(<one or more params>) -> …` crashes P3 in
surface_build; P2 (same source) passes. `build/rboot/gate-probe2-rb4/`: the 623-file closure
of `build/probe/scan_probe2.spl` crashes P3 at file 44 `src/lib/nogc_sync_mut/io/group_process_owner.spl`
(`:27 operation: fn(text, text, [text], text) -> Result<bool, text>`), P2 passes its
surface_build 613/613.

### Known-family match

YES — the "erased tuple/array handle through a generic (turbofish) direct call" family of
PR #10930 (`37f7c2b6d8e fix(hir,runtime): substitute turbofish direct-call returns and silence
rt_tuple_len probe`, 2026-11-23 06:03). Not #10920 (`byte_at().to_i64()`), not #10925
(optional-bool join), not #10932 (`.to_int()` on erased receiver), not `be3ddb1579b`.

### Fixed on latest

YES. `37f7c2b6d8e` is on `origin/release/1.0.0` (merged via `eb0fc11a6f4`, PR #10930) and is
NOT an ancestor of the rb4 pin `a8bb3822cf2c` (`git merge-base --is-ancestor` false — #10925
was merged at 06:35 from a branch that did not contain #10930). It carries BOTH halves:
(a) the compiler fix (HirLowering prescans generic return types / type-parameter names and
substitutes explicit turbofish `type_args` into direct generic call return types, incl. `if val`
binders), and (b) the source-side rewrite of exactly this function — `val param_list: [Type] =
params; parser_type_list_named_dependencies_into(param_list, names)` and typed
`val x: Type = …` rebinds for the Reference/Projection/Pointer arms — "so Stage 2 pre-fix seed
compilers also avoid erased element decoding".

## Second symptom — P3 computes a different closure than P2 (1627 vs 1619; 623 vs 613)

For the same `bootstrap_main` entry the P3 run loads 8 more files (path-only diff of the
`phase1:load_sources:input:start` sequences): `src/lib/nogc_async_mut/io.spl` and its import
closure (`io/tcp.spl, io/pipe.spl, io/event_loop.spl, nogc_sync_mut/io/tcp.spl, io/tcp_socket.spl,
sosix/network.spl, sffi/net.spl`), and visits `70.backend/backend_types.spl` /
`00.common/runtime_value_v1.spl` later than P2 does. Source bytes are identical in both SCV
snapshots (they differ only in 110 materialized t32/cmm symlink targets outside both closures).
The only `std.io` imports in the closure are the two `use std.io.*` lines INSIDE the leading
docstring of `src/lib/nogc_sync_mut/io.spl` (lines 10/16); `std.io` resolves
(`driver_entry_closure_core.spl:1973-2010`) through the family loop whose first entry is
`nogc_async_mut`, i.e. to that file. Candidate owners: the scanner's docstring tracking
(`_driver_entry_import_module_paths_text_fallback`, `:923-1086`) or the resolver. Not yet
localized — `build/probe/scan_probe2.spl` (calls the real scanner/resolver) crashes P3 in
surface_build before running (the defect above), and a verbatim standalone copy
(`build/probe/scan_probe.spl`) behaves identically under P2 and P3. Re-run `scan_probe2.spl`
with the next Phase 3. The extra files are harmless by themselves (they are real library
modules), but a closure that depends on the compiler is a determinism defect.

## Reproduction notes

- `build/rboot/manual-p3to3-cdb.sh` (`SHARD=1`): identical replay under `cdb -o -G` with child
  debugging, two-stage AV handler (`.exr -1; r; kv; u; dqs`). Needs `_NO_DEBUG_HEAP=1` —
  without it the debuggee ran under `RtlDebugFreeHeap` (~10x slower, 50 min with no output).
- The full-fidelity replay (`manual-p3to3-cdb1/`) was stopped after ~22 min while the coordinator was
  still in its closure walk (`_driver_entry_import_module_paths_text_fallback`); the in-process
  reproduction above made it unnecessary. The earlier debug-heap attempt is kept as
  `manual-p3to3-cdb{1,0}.debugheap-run/`.
- Symbolization: P3 has no PDB (`/DEBUG:NONE`). `scratchpad/dbg2/relink.sh` relinked the 1494
  canonical Stage 3 ledger objects + runtime objects re-harvested from a P3 hello build on the
  same pinned runtime source (`build/rboot/harvest-rt-rb4/keep`) + a regenerated 257-init entry
  stub with `/DEBUG /MAP`; the result's `.text` is byte-identical to the real P3 for the first
  0x14651e1 of 0x14eba00 bytes (all aot code), so `scratchpad/dbg2/sym.py <base> <addr>` maps
  real-P3 addresses (`simple-p3-dbg.map`).

## Recommendation

(a) Rebuild Phase 2 from a release/1.0.0 commit that contains `37f7c2b6d8e`, then Phase 3,
then P3 -> P3. Minimal-delta pin: `e1141effaa6` (merge of #10932, 2026-11-23 07:09) — it
descends from the current pin `a8bb3822cf2c`, from the #10930 merge `eb0fc11a6f4` (this fix)
and carries #10932 (`.to_int()` on erased receivers), i.e. exactly the two fixes the rb4 pin is
known to miss and nothing unrelated; the current `origin/release/1.0.0` tip also qualifies but
brings ~30 more commits into a 6 h rebuild. No new
compiler-source fix is needed; the fix is already landed. Minimal MIR-shape spec for the gate:
`test/01_unit/compiler/50.mir/generic_turbofish_call_return_subst_spec.spl` (added by `37f7c2b6d8e`) plus shape A
above (`struct SA: f: fn(text) -> bool` must surface-build under the NEW Phase 3).

(b) If rebuilding from a newer commit is not acceptable, cherry-pick only the source-side half
of `37f7c2b6d8e` for `parser_types_expr.spl` (typed `val param_list: [Type] = params` +
`parser_type_list_named_dependencies_into`, typed rebinds in the Reference/Projection/Pointer
arms) onto the a8bb3822cf2c pin and rebuild P2 -> P3; the upstream commit message states the
pre-fix Phase 2 lowers the typed rebind correctly — verify with shape A before trusting it.
Audit for other `if val x = <generic><T>(…)` + `for` sites in the Stage 3 closure before
trusting (b) alone.

(c) is ruled out: the defect reproduces in-process (shapes A/B/D/E/G, scan_probe2) with the P3
binary as the compiler of a tiny closure, independent of the shard-worker route; the Stage 3
worker crash is the same code path on file 65.

Gate for the next Phase 3: `bash build/rboot/gate-shapes-rb4.sh` (edit the `S3` executable) —
all seven shapes must build and run.
