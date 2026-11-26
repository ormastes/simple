# MIR does not resolve `i64.to_string(radix)`

Bug ID: `mir_int_to_string_radix_unresolved_2026-11-14`
Severity: P3. Status: RESOLVED (MIR fix verified in tree; `src/lib` workaround retired in `41cbec8c26d`). Layer: `50.mir` (pure-Simple MIR lowering).

## Symptom

`code.to_string(16)` on an `i64` receiver fails pure-Simple MIR lowering with
`unresolved method call: to_string route=runtime-fallback`. This happened in
`lib.gc_async_mut.http_client.types` (`url_encode`, old line 57) during the
llm_caret native-build on the frozen Windows Phase 2 compiler (log
`/c/dev/wt-lane2/build/diag-phase4/q_caret/build.log`). The Rust seed
interpreter accepts the radix overload.

## Location

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:5493` handles
only the zero-argument conversion:

```simple
val is_text_conversion = (method == "to_text" or method == "to_string") and args.len() == 0
```

No arm handles `to_string` with a single integer radix argument, so the call
falls through to the runtime fallback and is fatal.

## Workaround (source, behaviour-preserving)

`src/lib/gc_async_mut/http_client/types.spl` `_url_encode_hex_upper(n)` spells
out uppercase base-16 digits (landed in PR #9022). Tagged
`# @workaround bug=mir_int_to_string_radix_unresolved_2026-11-14`.

## Fix / removal

Add a radix-aware `to_string(radix)` lowering for integer receivers (route to
a runtime primitive or a pure-Simple helper), then restore
`code.to_string(16).upper()` in `url_encode` and drop the helper.

## Verification 2026-11-26 (bf-2 lane, Windows host)

- Verified `lower_int_to_string_radix_v1` is present in
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2182-2388, 6224-6226`
  (landed in commit `4b107dfd6a7`).
- `test/01_unit/compiler/mir/mir_int_to_string_radix_spec.spl --mode=interpreter`
  (via `wa3_shared_bin/simple.exe`): 4/4 passed.
- `test/01_unit/compiler/mir/mir_int_to_string_radix_prevention_spec.spl --mode=interpreter`:
  1/1 passed.
- `test/01_unit/compiler/backend/llvm_interp_logical_and_or_spec.spl --mode=interpreter`:
  lowers `code.to_string(16).upper()` through frontend -> HIR -> MIR -> LLVM IR
  with 0 errors, and host `clang version 23.1.2` (`clang.exe -x ir -c`) accepted
  the emitted IR (`exit=0`).
- Workaround already retired prior to this lane: commit `41cbec8c26d` (2026-11-25,
  ancestor of `origin/release/1.0.0`) removed `_url_encode_hex_upper` and its
  `@workaround` tag from `src/lib/gc_async_mut/http_client/types.spl:57` (now
  `code.to_hex().upper()`), leaving zero remaining
  `mir_int_to_string_radix_unresolved_2026-11-14` `@workaround` tags in `src/`
  (guarded by `test/01_unit/lib/common/wa_lib_mir_remaining_retirement_spec.spl`
  and `test/01_unit/compiler/mir/wa_lib_mir_remaining_lowering_spec.spl`).
