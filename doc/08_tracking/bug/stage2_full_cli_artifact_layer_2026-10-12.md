# Stage2 full-CLI artifact builds: post-MIR lowering layers (2026-10-12)

Campaign: release_phase3 step-1, cycle 7 evidence
(`.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`,
overall=FAIL). Cycle 8 (this doc's fixes landed) advances the builds past the
MIR phase; the layers below are what the MIR fixes UNBLOCKED. All repro
commands use the admitted stage2
(`.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
sha256 4a49280ac268ebf647310e8be3d3c2ad7f34df32289c26a20934aa6c350664b1) or the
locally rebuilt candidate (`build/repro-stage2-fix/stage2-candidate/simple`); repro
harness: `build/repro-stage2-fix/run_mcp_repro.sh` (admitted) /
`run_mcp_repro2.sh` / `run_runner_repro.sh` (candidate).

## Fixed in this cycle (commit on release_phase3, see git log)

1. `unresolved method call: trim (module: lib.nogc_sync_mut.database.core)` —
   `raw_cols.map(&:trim)` (core.spl:246). `&:method` desugars to
   `\__p0: __p0.method()` with an untyped lambda param; closure conversion lifts
   it with an erased param type, so the primitive-text builtin arm (which
   required static text proof) rejected it. Fix: erased-receiver allowance in
   `method_calls_literals.spl` — admit the text-builtin arm when the receiver
   type is Any/Infer/Error (or absent), resolution is unresolved, and the
   lowered local is not a proven runtime array/dict/struct owner. Verified:
   `test/_probe_root_tmp/stage2-fix/fix_symproc_trim.spl` compiles and runs.
2. `for-in over non-array iterables (#143) ... collection mir type: Tuple;
   module: lib.common.json.array_ops` at array_ops.spl:479 —
   `val nested = json_to_array(elem)` has declared type `any?`, which lowers
   to `Tuple(Bool, word)`; the erased-word for-in fast path only accepted bare
   I64 locals AND required a HIR array element type. Fix: erased-collection
   lane in `mir_lowering_stmts.spl lower_for_iterator` — a collection whose
   declared HIR type is `Any`/`Optional(Any)` iterates as a counted index loop
   with erased-word (I64) elements, unboxing `Optional(Any)` via the existing
   `rt_unwrap_or_self` helper (same ABI as the annotated
   `val xs: [any] = json_to_array(e)` spelling, which already worked).
   Verified: `fix_json_flatten.spl` no longer reports the :479 error; the mcp
   build's MIR phase completes with ZERO MIR errors.
3. Diagnostic: "unresolved method call" error/placeholder now names
   `self.current_module_id` (was location-blind; receiver span is (0,0) for
   generated lambda bodies).

## Layer 2 (next): AOT/LLVM stage — latent in the admitted stage2

The admitted stage2 fails these identically (repro with `fix_crc.spl`), so
they predate this cycle's changes; the MIR failures previously masked them.

- `unsupported LLVM value conversion from i1|i64 to void
  function=lib.nogc_sync_mut.compression.gzip.crc.crc32_verify value=%l9 at
  crc.spl:47:12` — `crc32_verify(data, expected)` has UNTYPED params and no
  declared return; the `==` result (i1) is requested as type `void` in the
  LLVM text emit (`_MirToLlvm/core_codegen.spl:1401 emit_value_type_conversion`,
  dst_ty "void"). Same class at crc.spl:23/28 (i64 -> void). A fixture
  importing `lib.nogc_sync_mut.compression.gzip.crc` reproduces with the
  admitted compiler (`build/repro-stage2-fix/fix_crc.spl`, log
  `fix_crc.log`).
- `MIR module has no functions or static data` (driver_aot_native_output.spl:3709)
  for 19 units in the mcp closure, e.g. lib.string_core, lib.io_runtime,
  lib.common.io.traits, lib.format_utils, lib.nogc_async_mut.env.*,
  lib.nogc_sync_mut.env.*, lib.nogc_sync_mut.storage_roots.model,
  lib.common.storage_roots.__init__, lib.common.debug.contracts_v1,
  lib.common.encoding.simd_text_ffi. Needs a unit-granular repro (module-only
  native-build per unit) to see why the MIR module is empty.
- mcp build end state after this cycle's fixes:
  `build failed: 19 failed, 0 unverified, 120 ok of 139 unit(s)` (AOT stage).

## test_runner_build (status=1): record-element owner sentinel

`record collection payload owner is unavailable in the consumer:
owner=__no_struct_element__ consumer=lib.nogc_sync_mut.test_runner.sdoctest.extractor
declared_symbol=3 consumer_symbol=SdoctestModifier
consumer_symbol_owner=lib.nogc_sync_mut.test_runner.sdoctest.types source=:0:0`

Fires in `expr_dispatch.spl:950 rebind_record_element_owner` for a struct field
`modifiers: [SdoctestModifier]` (types.spl:88) where the element type is the
ENUM `SdoctestModifier`. The recorded `struct_field_type_ownership_key` for
that field is the sentinel `__no_struct_element__` — the sentinel is written by
the fn-return-type prescan (module_lowering.spl:1444-1456) and by
`bootstrap_fn_ret_array_element_shape_register`; the consumer-side field lookup
apparently resolves to a key list containing that sentinel (bare-name key
collision between the struct layout key and a same-named array-returning fn is
the prime suspect; `struct_field_order` has the 2026-08-07 collision canary —
check whether it fired in the runner repro log). Consumer-side repro:
`build/repro-stage2-fix/runner_repro.sh` (candidate; error persists).

## compiler_cli_build (status=88): RSS tree-cap kill, not a compile error

`compiler_cli_build.log` tail is only the RSS session summary; status=88 is
the process-tree RSS cap (5,859,375 KiB) per `tree-rss-policy.shs` ("80 jobs
killed at the 5.59 GiB cap (exit 88)"). The build was killed at ~490s during
`phase=surface_alias` (2483-file closure) while the test_runner worker built
concurrently (two full-compiler closures on one host). max_rss measured 1.18GB
for the wrapper child, so the tree cap counted shard workers. Likely
transient/environmental; if it recurs in cycle 8, consider lowering
tool_build_concurrency for phase2 or raising the per-task tree budget.

## Erased-dict `.keys()` on `any` receivers (design decision, unfixed)

`lib.common.json.serializer` (`for key in pairs.keys()`, pairs: any) and
`lib.common.json.utilities:67` fail with `unresolved method call: keys` when
compiled (fixture `fix_json_flatten.spl` pulls serializer). The dict-method
probe (`local_is_runtime_dict`) rejects erased I64 locals. Admitting it needs
an element-typing decision: `lower_dict_keys_or_values_array` decodes elements
by the dict's key MIR type, and for an erased dict that type is unknown —
decoding JSON's text keys as I64 corrupts tagged handles (see the
native_dict_keys_iter_index comment in method_calls_literals.spl). Options:
stamp `Opaque("str")` (correct for JSON objects, wrong for int-keyed erased
dicts) or route through a tag-aware decode. Not in the mcp closure today;
likely in the compiler_cli closure.

## Update 2026-10-13: AOT empty-module layer CLEARED (commit on release_phase3)

Root cause (two parts, both in the frozen-capsule worker lane):
1. `driver_native_frozen_source_lookup` failed closed on `path_count=2`: under
   SCV snapshots the same physical file is listed twice in the phase-1 source
   owners (closure scan + snapshot admission), so the alias guard rejected the
   read-only lookup for exactly the facade modules. Rejected lookup ->
   `driver_native_module_is_objectless` could not classify the (legitimately
   empty) export-shim facade -> Phase 1 scheduled it -> the capsule worker
   hard-failed "MIR module has no functions or static data". Fix: admit
   duplicate rows when every duplicate carries the same captured whole-content
   sha (inventory duplication, not aliasing); conflicting shas stay fail-closed.
2. `_compile_selected_module`'s emptiness check ignored `mir_module.constants`
   while the Phase-1 objectless check counts them, so constants-only modules
   (lib.string_core, lib.crypto.sha3) were scheduled and then rejected. Fix:
   count constants in the worker check too (constants are inlined by the
   native backends; the module still produces an empty object, and the
   objectless-proof spec's fail-closed invariants are untouched).

Minimal repro (test/_probe_root_tmp/stage2-fix/facade/): a 3-module closure
whose middle module is `export answer from inner` failed before, compiles and
runs (returns 42) after.

Verified with a candidate rebuilt from the fixed source:
- mcp artifact build: 19 failed -> 1 failed; the remaining unit is
  lib.nogc_sync_mut.compression.gzip.crc failing at the DOCUMENTED next layer
  (untyped-param fns: 'unsupported LLVM value conversion from i64 to void',
  crc.spl:23/28/47). 18 empty facades are now correctly objectless-skipped
  (139 -> 121 scheduled units).
- test_runner artifact build: 57 failing units -> 0; all 192 units compile,
  and the build now reaches LINK, failing on 4 undefined global symbols:
  g_*_test_runner_types_spl__TEST_OUTPUT_CAPTURE_BYTES (a cross-module `val`
  constant) and 3 lexer/module-path `var` slots from
  compiler/10.frontend/core/_Ast/decl_nodes.spl. Both defining modules
  compiled; the reference and definition spell the module-qualified global
  differently -- the stage2_cross_module_call_mangling_asymmetry family
  (2026-09-13 doc). That mangling-asymmetry layer is the new frontier.

## Update 2026-10-13: crc ICE fixed (untyped-return inference)

The last mcp compile blocker is cleared. Root cause: `fn crc32_finalize(crc):`
et al. in lib/nogc_sync_mut/compression/gzip/crc.spl have NO declared return
type, so the MIR body return type is Unit and the LLVM signature pre-pass +
translate_function emitted `define void`, while the Ret terminators carry
real values (i64/i1 locals) -> "unsupported LLVM value conversion <t> to
void" -> module ICE. The seed infers untyped returns from the body. Fix in
_MirToLlvm/core_codegen.spl translate_function (and the signature pre-pass):
a Unit-declared body whose Ret terminators return a LOCAL operand (kind
Copy/Move) becomes word-returning (i64). Const-only returns stay Unit.
Verified: fix_crc.spl compiles (0 errors); the mcp artifact build completes
with 0 failed modules.

Independently observed runtime layer (NOT caused by this fix, unrelated cast
path): `crc32("hello".bytes()).to_i64()` -- a `.to_i64()` cast on a u32 value
returned from a cross-module call -- segfaults at runtime under the stage2
candidate. crc32_text in the gzip module hits exactly this, so the produced
binaries' crc paths are runtime-unqualified. Logged here as the next runtime
layer; the campaign's current bar is compile-level parity.
