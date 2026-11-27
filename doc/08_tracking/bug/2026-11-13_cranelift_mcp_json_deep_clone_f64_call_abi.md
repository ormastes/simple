# Cranelift `app.mcp` build: every module reported `CRASH` — one f64 call-ABI panic in `json_deep_clone`

- **Date:** 2026-11-13
- **Status:** FIXED (source) — `src/lib/common/json/validation.spl`
- **Severity:** High — the whole Cranelift `src/app/mcp/main.spl` native build fails; LLVM is unaffected
- **Area:** `src/lib/common/json/validation.spl:74` (`json_deep_clone`),
  `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1743` (diagnostic)

## Symptom

Frozen Windows Phase 2 (`build/diag-phase4/phase2.exe`, release tip
`4b7375e435a`), `native-build --backend cranelift --entry src/app/mcp/main.spl`:
HIR clean, then

```
[mir-shard] owner=0/1@0 status=CRASH exit=-1073740791 claimed=282 sealed=282 finished=false (fast-fail abort 0xC0000409 ...)
[mir-shard] failed module: CRASH app.cli._QueryVisibility.feature_visibility
... (all 282 modules)
MIR shard aggregate failure
```

The per-module `CRASH` lines are attribution, not 282 failures: the single
shard worker owns every module, so its death marks all of them. The worker had
in fact finished MIR (`[mir] 282/282`), AOP weave and native-cache, and was in
`native_compile` (190 `.o` files emitted to `TMPDIR`) when it printed

```
E-BACKEND-CRANELIFT-CALL-ABI: lib.common.json.types.json_number: arg 0 is i64 but the callee declares f64; convert it explicitly at the call site
```

and `panic()`ed — the 0xC0000409 fast-fail. `lib.common.json.validation` is the
one json module with no `.o`.

## Root cause

`json_deep_clone` rebuilt a number with `json_number(json_to_number(value))`.
`json_to_number` returns `any?` (an erased i64 word); `json_number` declares
`value: f64`. The Cranelift import-ABI guard (`cl_call_abi_mismatch`)
deliberately rejects an int-register argument to an f64 parameter instead of
passing it in the wrong register. The type checker accepted the `any? -> f64`
argument without inserting a conversion, so only the Cranelift guard caught it.

## Fix

Rebuild the tagged tuple directly from the stored payload,
`("number", value.1)` — the same shape `json_number` returns, with no f64
crossing. Regression: `parsers_json_ops_spec.spl` "clones a fractional number
without routing it through an f64 parameter".

The first `E-BACKEND-CRANELIFT-CALL-ABI` panic site now names the calling
function too (`... : call in <func>: ...`), matching the second site, so the
next occurrence points at the caller instead of only the callee.

## Evidence

4-module fixture (`json_number` + `json_deep_clone`), frozen Phase 2,
`--backend cranelift`, `SIMPLE_NATIVE_BUILD_THREADS=1`:

- release tip `4b7375e435a` (unfixed): same `E-BACKEND-CRANELIFT-CALL-ABI`
  line, `status=CRASH exit=-1073740791 claimed=4`, "MIR shard aggregate
  failure" — the 282-module failure reproduced at 4 modules.
- with this fix: `build rc=0`, `[mir-shard] done ... passed=4`, binary links.
- interpreter: `parsers_json_ops_spec.spl` 65/65 passed.

## Open

- **Separate Cranelift runtime defect, pre-existing, not fixed here:** the
  fixed fixture binary prints `json_get_type(json_number(2.5))` as `null`
  with `[simple-runtime][error] rejected invalid array handle before
  dereference; probable compiler/FFI ABI mismatch`, then segfaults (rc 139)
  in `json_to_number(n)`. This happens on the tuple built directly by
  `json_number`, before any clone, so the f64-payload tuple read through
  `any` (`value.0` / `value.1`) is miscompiled by Cranelift independently of
  this change. Needs its own bug.

- The Phase 2 compiler only stops at the first such call; other
  `any`-to-`f64` call sites in the `app.mcp` closure, if any, appear only
  after a rerun.
- The type checker silently accepting `any?` for an `f64` parameter is the
  underlying gap; not addressed here.
