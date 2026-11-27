# BUG: native --entry-closure leaves bare built-in method symbols unresolved at link

- **ID:** `llm_caret_native_entry_closure_bare_builtin_method_symbols_2026-11-04`
- **Severity:** P2
- **Split from:** `llm_caret_compiled_carrier_build_latency_2026-08-02` (2026-11-04)

## Symptom

The 95-module PureDatabase / messaging carrier native build compiles and reaches
the final link, which then fails with undefined references to bare method names:
`len`, `trim`, `starts_with`, `unwrap_err` (and siblings). These are text/array/
Result built-in methods that must be lowered to runtime calls (`rt_string_len`,
`rt_string_trim`, `rt_string_starts_with`, ...), never emitted as a symbol named
after the method.

## Reproduction

```sh
bin/simple native-build --source src/app --source src/lib --entry-closure \
  --entry src/app/llm_caret/messaging/hook_worker.spl --strip \
  --output build/database/llm_caret_messaging_hook
# link: undefined symbol len / trim / starts_with / unwrap_err
```

## Suspected root cause (located by source inspection, NOT yet proven by a build)

MIR method-call lowering picks the runtime symbol from the receiver's static type.
Under `--entry-closure` the lowering leaves `receiver.type_` nil for locals/params
that cross module boundaries -- the code already documents this at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` ~L2668
("entry-closure lowering leaves receiver.type_ nil") and ~L3161 (Dict receiver
mis-typed in an entry-closure build). The erased-receiver admission chain
(`erased_recv_ty_ok`, ~L2640-2700) only recognises receivers it can prove as
text/array/dict; when the receiver type is nil and none of those proofs hit, the
call falls through to the generic path that emits a call to the BARE method name
(a `Call` to an extern symbol `len`), which no object defines.

Next step for the owner: build the 95-module closure with MIR dump, find the
`Call` whose callee is the bare name, and print `receiver.type_` at that site in
`method_calls_literals.spl`; fix by resolving the receiver type from the callee
module's HIR (or by routing nil-typed receivers of these method names through the
tagged-value runtime entry points, as `rt_any_to_int` does for `to_i64`).

## Acceptance

`nm` on the linked carrier shows no undefined bare `len/trim/starts_with/unwrap_err`;
the carrier runs the tokenizer probe. Add a MIR-level spec asserting no `Call` to a
bare built-in method name in an entry-closure lowering of a two-module fixture.

## Resolution (2026-11-10): closed-obsolete, premise does not hold on the current tree

The suspected mechanism -- `method_calls_literals.spl` emitting a `Call` to the
bare method name when `receiver.type_` is nil -- does not exist on
`release/1.0.0`: the unresolved-method path is fail-closed (`rt_panic` +
const-0, Task #145) and no site in `src/compiler/50.mir` emits the raw method
name as a call target. Literal/primitive receivers are pinned by
`test/01_unit/compiler/mir/bare_builtin_method_literal_receiver_spec.spl`
(6/6) and cross-module nil-typed receivers by
`test/01_unit/compiler/mir/bare_builtin_method_carrier_link_probe_spec.spl`
(3/3; its negative probes were vacuous -- escaped-quote pattern the serializer
never emits -- and are now live). The 95-module native link failure was never
reproduced; if it recurs, re-file naming the lane (Rust seed native-build vs
stage2) with the MIR dump of the bare `Call`.
