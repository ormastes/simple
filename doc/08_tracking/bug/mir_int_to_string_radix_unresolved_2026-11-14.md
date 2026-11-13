# MIR does not resolve `i64.to_string(radix)`

Bug ID: `mir_int_to_string_radix_unresolved_2026-11-14`
Severity: P3. Status: open. Layer: `50.mir` (pure-Simple MIR lowering).

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
