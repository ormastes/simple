# native-build: Option.map/.filter/.unwrap_or lambda codegen emits invalid ptr<->i1 casts

**Severity:** high (build-breaking, `llc` rejects the emitted IR)
**Found:** 2026-07-16, parity case `option_is_none_map_llvm`
(`scripts/check/check-native-seed-parity.shs`, `write_case_option_is_none_map`)
**Status:** fixed
**Backend:** pure-Simple `native-build` MIR lowering (`50.mir`) + LLVM codegen
(`70.backend/backend/_MirToLlvm`)

## Reproduction (minimal)

```simple
fn main() -> i64:
    val some: i64? = 5
    print(some.map(fn(x: i64) -> text: "v").unwrap_or("d") == "v")
    return 0
```

```
error: ... llc failed (exit 1): invalid cast opcode for cast from 'ptr' to 'i1'
```

A second, independent repro (same parity case, later statement):

```simple
fn main() -> i64:
    val some_bool: bool? = true
    print(some_bool.map(fn(x: bool) -> bool: not x).unwrap_or(true))
    return 0
```

```
error: ... llc failed (exit 1): invalid cast opcode for cast from 'i1' to 'ptr'
```

And, without `.map()` at all:

```simple
fn main() -> i64:
    val some_bool: bool? = true
    print(some_bool.unwrap_or(false))
    return 0
```
fails the same way — `bool?` handling was broken independent of `.map()`.

## Root causes (three, all in the Option.map/.unwrap_or/.filter family)

### 1. `option_map_value_hir_type`'s bare-variant match was corrupted by a nested early-return

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, function
`option_map_value_hir_type`: the fallback branch built its result via
`val kind = match type_.kind: ... case MirTypeKind.Opaque(name): if name ==
"str": HirTypeKind.Str else: return nil ... ; return Some(HirType(kind: kind,
...))`. Under the seed interpreter that drives native-build's live
compiler-source execution, a match-arm that mixes a **bare no-payload enum
variant as a value** (`HirTypeKind.Str`) with a **sibling arm that does an
early `return` from inside a nested `if/else`** corrupts the bare variant's
tag: the caller's `match found_inner_uo.kind: case HirTypeKind.Str: ...`
silently fell through to `case _`, even though the value had genuinely been
constructed as `HirTypeKind.Str`. That made `.unwrap_or()`'s
`uo_is_text`/`uo_result_type` detection fail for a `.map()` result whose
lambda returns `text`, so the result got the wrong (default `i64`/derived
`bool`) MIR type, and a later `decode_runtime_value` Bool-tag decode
(`raw == 11`) ran on a **string handle**, storing an `i1` where a text
handle was expected — the initial `ptr -> i1` crash.

Fix: rewrite `option_map_value_hir_type`'s fallback to `return Some(...)`
directly from every arm (no intermediate `val kind = match ...:` assignment,
no nested nested-if-with-return-as-a-match-arm-value). Confirmed via
targeted `eprint` instrumentation (temporary, removed) that the bare `Str`
variant now matches correctly at the call site.

### 2. `rt_text_eq_any`'s raw i64 0/1 result was never marked `Bool` for print formatting

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, the `bin_is_str_eq`
text-equality intercept: `rt_text_eq_any` returns its real C ABI type (`i64`
0/1, per `declare i64 @rt_text_eq_any(...)`), and the MIR result type was
declared `MirType.i64()` to match. But `print()`'s bool-vs-int render-fn
dispatch (`lower_bootstrap_print_call`'s `is_bool` check) only fires on a
genuinely `Bool`-typed local, so `print(a == "hello")` printed `"1"`/`"0"`
instead of `"true"`/`"false"` — independent of the Option chain, but exercised
by this parity case's `.unwrap_or(...) == "..."` assertions.

Fix: narrow the raw i64 result through a genuine `icmp eq ... , 1`
(`MirBinOp.Eq`, result type `MirType.bool()`) — mirrors the codebase's own
`decode_runtime_value` Bool-tag-decode pattern — rather than relabeling the
wide value's declared type (which would desync from its real bit width).

### 3. `Option<bool>` receivers are ptr-shaped but never bridged to/from real `i1`

`Optional(inner)` lowers (`function_lowering.spl`) to `Tuple([Bool, inner])`,
which the backend primes as a pointer (`alloca ptr`). For `Option<i64>` this
is representationally free (an i64 payload IS pointer-width, so the raw
bit pattern is usable as an integer with no conversion) — but `Option<bool>`'s
1-bit payload is not: two related bridges were entirely missing.

- **Store direction (i1 -> ptr):** `value_as_type`
  (`70.backend/backend/_MirToLlvm/core_codegen.spl`) has no `i1 -> ptr` rule
  and fell through to its generic `"bitcast"` default — invalid (mismatched
  bit widths). Fixed by special-casing `src_ty=="i1" and dst_ty=="ptr"` to
  emit a real `zext i1 -> i64` then `inttoptr i64 -> ptr`, mirroring the
  existing i64 "handle unbox" convention.
- **Read direction (ptr -> i1):** binding a `bool?` receiver directly as a
  `.map()` lambda parameter, or as `.unwrap_or()`'s "some" value, left the
  raw ptr-shaped receiver flowing into code that expects a real bool (e.g.
  `not x` on a `ptr` operand was misinterpreted as an is-null check on the
  pointer itself). Added `option_bool_value()` (ptrtoint to i64, then trunc
  to i1) and wired it into both `.map()`'s `some_val_map` and bare
  `.unwrap_or()`'s `some_val_uo` assignment, gated on the inner type being
  `Bool` and not already covered by the existing
  `runtime_value_locals`/`decode_runtime_value` path (which already handles
  a **chained** `.map(...).unwrap_or(...)` correctly once fix #1 makes the
  map lambda's return type detection work, since `box_runtime_value`'s Bool
  case already tags `true`/`false` as 11/19 — always non-null, so
  `decode_runtime_value`'s existing Bool branch just needed a correctly
  produced boxed value to decode).

## Files changed

- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` —
  `option_map_value_hir_type` rewrite (root cause #1); new
  `option_bool_value` helper + wiring into `.map()`/`.unwrap_or()` (root
  cause #3, read direction).
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` — text-equality
  intercept narrows its result to a genuine bool (root cause #2).
- `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` —
  `value_as_type` gains an explicit `i1 -> ptr` bridge (root cause #3, store
  direction).

**CONFLICT-FLAG:** `expr_dispatch.spl` and `method_calls_literals.spl` are
both under `50.mir/_MirLoweringExpr/` (general MIR lowering/dispatch
territory), and `core_codegen.spl` is under `70.backend/backend/_MirToLlvm/`
— per campaign notes, a separate lane may be working on comparison codegen
in this same area. All three edits here are narrowly scoped (one function
body each) and guarded by specific type checks, but please diff against any
concurrent changes to `bin_is_str_eq`, `value_as_type`, or
`option_map_value_hir_type`/`.map()`/`.unwrap_or()` before merging.

## Verification

- Minimal repros (`some.map(fn->text).unwrap_or(text) == text`,
  `some_bool.map(fn->bool).unwrap_or(bool)`, bare `some_bool.unwrap_or(bool)`)
  each build and run to the correct output in isolation.
- Full parity case source builds and runs to
  `011099truetrue1truefalse2`, matching the seed oracle exactly.
- `NATIVE_PARITY_CASES="option_is_none_map" sh scripts/check/check-native-seed-parity.shs`:
  `option_is_none_map_llvm` PASS; `option_is_none_map_cranelift` XFAIL
  (pre-existing, unrelated — seed lacks `rt_cranelift_*` SFFI externs).
- `sh scripts/check/native-smoke-matrix.shs`: see campaign report for the
  full `total=15 pass=15 fail=0 codegen_fallback_hits=0` gate result.
