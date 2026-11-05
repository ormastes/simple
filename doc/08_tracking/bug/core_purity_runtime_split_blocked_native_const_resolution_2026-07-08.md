# Bug: JS-engine cross-module `NATIVE_*` constant resolution blocks the runtime.spl core-purity split

- **ID:** core_purity_runtime_split_blocked_native_const_resolution_2026-07-08
- **Severity:** P2 (blocks the last core-purity violation #35 Step 4; also indicates a latent
  correctness fragility in the JS engine's native-dispatch constant graph).
- **Area:** `src/lib/common/js/engine/runtime.spl` (`JsRuntime` + `NATIVE_*` id constants +
  `dispatch_native`), the `interpreter*` clusters across tiers, the module-system's cross-module
  `val` resolution.
- **Status:** OPEN — found 2026-07-08 attempting #35 Step 4 (move `JsRuntime` out of the pure CORE
  tier). Steps 1-3 (lzma2 + js/mod + js/module_loader) landed cleanly (`952208f1`, gate
  `core_purity_new` 4→1). Step 4 reverted after the regression below.

## What was attempted (and why it failed)

`common/js/engine/runtime.spl` trips the gate via 5 impure imports (nogc `interpreter*`+`parser`) that
`JsRuntime` pulls in. The plan: keep the **pure** `NATIVE_*` id constants + `dispatch_native` in
common, move the impure `JsRuntime` class to `nogc_sync_mut/js/engine/runtime.spl`, and have the moved
class `use std.js.engine.runtime.{dispatch_native, NATIVE_*}` back from common.

**Result: regression.** `test/01_unit/lib/common/js_runtime_host_property_spec.spl` goes
**pass → fail** (verified by restoring the pre-Step-4 files from the parent commit: 1/0 there, 0/1
with the split). `JsRuntime.initialize()` registers ~30 native functions by id
(`_define_global_fn("parseInt", NATIVE_PARSE_INT)` …); after the move those `NATIVE_*` no longer
resolve to their defined values across the module boundary, so the native-id table + the interpreter
object-store arrays desynchronise.

A minimal probe (`use std.js.engine.runtime.{NATIVE_PARSE_INT}` in a standalone file) fails with
`error: semantic: variable NATIVE_PARSE_INT not found` even though the constant IS defined in common —
i.e. cross-module `val` import of these constants does not resolve the way same-file reference does.

## Why the constant system is already fragile (context)

`interpreter_native.spl` (nogc) imports **~150** `NATIVE_*` from `std.js.engine.runtime`, but common
only **defines ~48** of them (the WEBASSEMBLY/NODE/DATA_VIEW/STREAM/SET_IMMEDIATE families are imported
but undefined). It "works" today only because the toolchain is lenient about importing undefined
`val`s (and a JIT run surfaces `Unknown variable: NATIVE_SET_IMMEDIATE while lowering
JsInterpreter.eval_expression`). So the native-id constant graph is position/order-sensitive and
partially undefined — moving `JsRuntime` (a heavy consumer of it) across the module boundary is not a
mechanical relocation; it perturbs this fragile resolution.

## Options (none is a mechanical purity edit)

1. **Fix the module system**: make cross-module `val`/const import resolve reliably (and reject
   undefined-const imports instead of tolerating them). Largest blast radius but fixes the root.
2. **Full-move**: relocate `NATIVE_*` + `dispatch_native` + `JsRuntime` together to nogc and repoint
   the ~11 constants-only `interpreter*` importers (across all tiers) — risks the same cross-module
   const resolution on the interpreter side; needs the full JS suite to verify.
3. **Reconcile + define the ~100 missing `NATIVE_*`** first (separate correctness fix), then re-attempt
   the split. Untangles the fragility before the move.

Recommend (1) or (3) — both are their own tracked work, not a rider on the purity fix. Until then,
`common/js/engine/runtime.spl` stays the last baselined-adjacent core-purity item (gate
`core_purity_new=1`).

## Resolution note (2026-11-05, work/libbug-w6-corepurity-20261105)

Root cause was NOT a general module-system `val`-resolution defect. Probe
diagnosis (canary: changing the id value in `common/js/engine/runtime.spl` did
not change what a `use std.js.engine.runtime.{NATIVE_JSON_PARSE}` importer
observed) showed that `std.js.engine.runtime` from higher tiers binds
`src/lib/nogc_sync_mut/js/engine/runtime.spl` (tier fallback), while the
"common defines ~48" constants — `NATIVE_PARSE_INT`, `NATIVE_CONSOLE_LOG`,
`NATIVE_MATH_*`, `NATIVE_STRING_*`, `NATIVE_ARRAY_*`, the `*_CONSTRUCTOR`
family, etc. — exist ONLY in `src/lib/common/js/engine/runtime.spl`, reachable
there under the distinct name `std.common.js.engine.runtime`. So cross-module
`use std.js.engine.runtime.{NATIVE_PARSE_INT}` failed with "variable not
found" because the constant genuinely does not exist in the bound copy.

Fix (std-lib only, no purity weakening — the pure constants stay in common as
the single source of truth):

1. `src/lib/common/js/engine/runtime.spl`: the 30 previously private
   `val NATIVE_*` are now `pub val` and are listed in explicit `export`
   statements (mirroring the nogc copy's existing convention).
2. `src/lib/nogc_sync_mut/js/engine/runtime.spl`: `export use
   std.common.js.engine.runtime.{...}` re-exports those 30 constants, so every
   tier whose `std.js.engine.runtime` lookup falls back to this copy resolves
   them. Names the nogc copy already defines locally (a divergent-id duplicate
   set: `NATIVE_FETCH`, `NATIVE_RESPONSE_*`, `NATIVE_STORAGE_*`,
   `NATIVE_BLOB_TEXT`, `NATIVE_NAVIGATOR_GPU_REQUEST_ADAPTER`) keep their local
   values — reconciling those duplicated ids remains separate work (option 3).

Regression spec: `test/01_unit/lib/common/js_runtime_native_const_cross_module_spec.spl`
(RED: `semantic: variable NATIVE_PARSE_INT not found`; GREEN after fix).
