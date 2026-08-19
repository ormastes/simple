# Closure-captured instance loses `me`-method self-mutation (2026-08-19)

**Status:** FIXED (Rust interpreter, `interpreter_call/core/lambda.rs`)
**Family:** 6th interpreter write-back defect (with match-arm read-path, match-expr
write-back, for-loop block-local, engine2d factory dict, struct-receiver decay —
see `engine2d_factory_returns_dict_under_test_runner_2026-08-19.md`,
`struct_receiver_decays_to_empty_dict_under_test_runner_2026-08-19.md`).

## Repro (failing pre-fix)

```simple
class Counter:
    n: i32
    me bump():
        self.n = self.n + 1

var d = Counter(n: 0)
val cb = fn(x: i32) -> i32:
    d.bump()
    d.n + x
val r = cb(1)      # inside sees n=1
print(d.n)         # BUG: 0 outside; expected 1
```

Direct method calls write back fine; only closure-captured instances lost it.

## Mechanism

The interpreter's `Env` is a value snapshot. `exec_lambda`
(`src/compiler_rust/compiler/src/interpreter_call/core/lambda.rs`) clones the
lambda's `captured_env` into a throwaway `local_env`, runs the body, and wrote
back only *argument* bindings (Bug #19 path). A `me`-method self-update inside
the body updates `d` in `local_env` only; the caller's binding and the lambda's
captured snapshot never see it — the mutation dies with `local_env`.

## Fix

After a successful body run, for every non-local, non-parameter overlay entry of
`local_env` that (a) was genuinely captured (present in `captured_env` before
the call), (b) holds a container value (`Object`/`Array`/`Dict`/`Tuple`), and
(c) changed, propagate the post-body value to: the captured snapshot, the
caller's env when it binds the same name, and `MODULE_GLOBALS` when the name
lives there (same mirroring policy as commit 47411747677).

## Impact

Removes one blocker for `browser_session_textarea_lifecycle_spec`
(dispatch_dom_event_route passes `fn(...) executor.execute(...)` into
`be_dom_dispatch_*`; `executor.runtime` mutations previously never propagated).
That spec is still RED after the fix, identically pre/post: the remaining
failure is a separate JS-engine defect (`[browser-session] ReferenceError: i is
not defined` / `all is not defined`, then pixel check "expected truthy, got 0"),
unchanged by this fix.

Verified 2026-08-19 on the fixed seed: repro green; engine2d_drawing 2/2,
vulkan_strict 17/17, base_encoding_utf8_guard 5/5, editor_controller 88/92
(baseline held).
