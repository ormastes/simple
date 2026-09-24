# Method/field access on a `Result<T,E>` compiles and returns a garbage sentinel instead of a type error
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-06
**Status:** OPEN
**Found by:** orchestrator, while re-running the caret_workbench RED-before
reproductions — a stale probe accessed `.content` on a `Result<MuxCapture,text>`
and produced two FALSE test failures that looked like live defects.
**Binary:** `src/compiler_rust/target/release/simple` (37,328,472 B, 2026-09-05
21:22), macOS arm64. Also reproduces on `target/bootstrap/simple`.

## Symptom

Calling a method (or reading a field) on a `Result` value — rather than on its
unwrapped payload — is accepted by the compiler and yields a garbage sentinel at
runtime. No error, no warning, no diagnostic.

## Reproduction

`build/nb/fixtures/probe_result_field.spl`:

```simple
fn mk(ok: bool) -> Result<i64, text>:
    if ok: Ok(42) else: Err("nope")

fn main():
    val r = mk(true)
    print("ok_case_len={r.len()}")
```

```
$ src/compiler_rust/target/release/simple run build/nb/fixtures/probe_result_field.spl
ok_case_len=<value:0xffffffffffffffff>
```

`i64` has no `.len()` either, so this is not payload auto-deref — the call is
resolving to nothing and the result is an uninitialised sentinel.

## Why this matters more than an ordinary type gap

It silently converts a **signature change into a false test failure**. When
`smux_capture` changed from returning `MuxCapture` to `Result<MuxCapture, text>`,
an older probe reading `cap.content` kept compiling and started producing wrong
values. Two of its six examples then failed, and those failures read exactly like
unfixed product defects — they cost a verification pass real time and nearly
produced a wrong conclusion that two shipped fixes had not landed.

The correct behaviour of both code paths was confirmed separately with proper
`match` handling:

```
H001 send_text_on_childless_pane_is_ok=false     # refused, not buffered
H001 capture content=<>  echoed=false            # no echo
H003 typed_error=unknown pane: no-such-pane      # not a fabricated row
```

So the product was right and the probe was wrong — but nothing in the toolchain
said so.

## Unblock condition

A method or field access on a `Result<T,E>` that is not a member of `Result`
itself must be a compile-time error naming the needed `match`/unwrap. Silently
accepting it and returning `<value:0xffffffffffffffff>` is the part that must not
survive.

Related family — silent-wrong-value defects found in the same session:
`doc/08_tracking/bug/nested_array_element_bound_to_var_copies_2026-09-05.md`
(binding a nested array element copies; writes vanish) and
`doc/08_tracking/bug/module_var_write_lost_when_rhs_method_reads_me_2026-09-05.md`
(module-level `var` write discarded when the RHS reads `me`). All three fail in
the same direction: the program keeps running and gives a plausible wrong answer.

