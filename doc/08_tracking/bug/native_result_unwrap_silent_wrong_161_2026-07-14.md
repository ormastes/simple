# native-build: `.unwrap()`/`.unwrap_or()` on `Result` silently returns 161

**Status:** RESOLVED 2026-07-15

**Severity:** high (silent-wrong — violates the never-loud→silent discipline)
**Found:** 2026-07-14, errhandling lane
**Resolved:** 2026-07-15
**Backend:** native-build `--entry` (pure-Simple MIR lowering)

## Symptom

Calling `.unwrap()` or `.unwrap_or(d)` on a `Result<T,E>` value returns a fixed
wrong constant (`161`) for **both** `Ok` and `Err` — never panics, never emits a
diagnostic, never matches the payload.

```simple
fn f() -> Result<i64, text>: return Ok(7)
fn main() -> i64:
    print(f().unwrap())   # native prints 161; oracle prints 7
    return 0
```

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` L156-260:
`.unwrap`/`.unwrap_or` branch **exclusively** on `rt_is_some`/`rt_is_none`, which
is the **Option** runtime representation. There is no case for `Result`'s
`rt_enum_new`/`rt_enum_discriminant` representation, so the payload extraction
reads the wrong slot and yields a constant.

## Resolution

MIR now recovers a receiver's declared `Result<Ok,Err>` type through the same
typed-expression/symbol/call-return helper used by Result match lowering. A
shared Result-only unwrap path branches on `rt_enum_discriminant`, extracts the
raw Ok payload through `rt_enum_payload`, lazily evaluates the `unwrap_or`
default for Err, and calls `rt_panic` for `Err.unwrap()`.

The existing Option implementation remains unchanged. The first safe scope is
`i64` and `text` Ok payloads; other Result payload shapes fail compilation with
`unsupported Result unwrap payload type` instead of being silently coerced.

`scripts/check/check-native-seed-parity.shs` covers numeric/text `unwrap`, both
`unwrap_or` branches, unchanged numeric Option behavior, an unsupported
`u64` loud failure, and a required runtime panic diagnostic in the 43-case
gate. The Result case is native-authoritative because the seed oracle's
`Result.unwrap_or` behavior is itself broken.

## Reproduce

`/tmp/wt_errhandling/p*.spl` (errhandling lane probes). Oracle:
`env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`; native:
`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.

## Follow-up (2026-07-16): Option-text tail of the parity case

The gate's `result_unwrap` case (expected `779yes08optoptFfallback`) still
failed on its **Option** tail: `absent_text.unwrap_or(option_fallback())`
(receiver `text? = nil`) evaluated the fallback lazily (the `F` printed) but
then printed the fallback string's raw char* as a decimal pointer
(e.g. `...optoptF98015628508273`). Minimal repro:
`val t: text? = nil; print(t.unwrap_or("fallback"))` → decimal pointer.

**Root cause (one layer above MIR):** the flat-AST bridge encodes every `T?`
annotation as `TypeKind.Named("Option", [T])`
(`10.frontend/_FlatAstBridge/convert_nodes.spl`, TYPE_OPTION_I64/F64/TEXT/BOOL
tags) — never as `TypeKind.Optional`. `lower_named_kind`
(`20.hir/hir_lowering/types.spl`) special-cases `Result` and `Dict` but had no
`Option` case, so the name fell through to the unresolved-symbol branch (no
`Option` symbol exists) and the whole annotation collapsed to
`HirTypeKind.Error`. MIR's `option_inner_hir_type` then saw no `Optional`,
typed the `unwrap_or` merge slot `i64` (nil-initialized receivers have no
`local_is_str` rescue), and `print()`'s numeric-coercion branch rendered the
text pointer as a decimal.

**Fix:** map 1-arg `Named("Option", [T])` → `HirTypeKind.Optional(T)` in
`lower_named_kind`, mirroring the existing `Result`/`Dict` cases. Argless
`Option` (the parser only threads i64/f64/text/bool inners through dedicated
tags) keeps its previous fall-through behavior. After the fix the case prints
exactly `779yes08optoptFfallback`; native-smoke-matrix stays 15/15
(fail=0, codegen_fallback_hits=0).

**Verification hazard:** `build/native_cache` is keyed by a compiler hash that
does NOT change when the live-interpreted `src/compiler/*.spl` sources change;
`--clean` does not invalidate it either. After editing compiler sources,
`rm -rf build/native_cache` or the old per-module objects keep being linked
(observed: fixed MIR lowering ran and traced correctly while the produced
binary still contained the pre-fix code).

**Separate gate defect found while verifying:** in
`scripts/check/check-native-seed-parity.shs`, `record()` assigns `mode="$2"`,
clobbering the global `mode` that `run_strict_dual_backend_case` reads for its
second (cranelift) loop iteration — so every `*_llvm_cranelift` leg
deterministically fails with `invalid --mode 'strict-llvm'` after the llvm
leg's `record` call. Pre-existing (reproduces at de7cb5a238a); needs a distinct
local variable name in one of the two functions.
