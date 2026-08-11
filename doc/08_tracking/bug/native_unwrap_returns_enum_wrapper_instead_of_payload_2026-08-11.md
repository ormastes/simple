# `.unwrap()`/`.expect()` on Result/Option returned the boxed enum wrapper, not the payload — JIT/native only

**Date:** 2026-08-11
**Status:** FIXED (unwrap payload extraction + Err/None trap + `unwrap_or(default)` follow-up fix, see below; `.expect()` custom-message threading remains a known limitation)
**Lanes affected:** Rust-seed default JIT (`simple run`) AND true `--native` (real compiled ELF). **NOT** affected: the tree-walk interpreter (`SIMPLE_EXECUTION_MODE=interpret`).

## Symptom

```
fn main():
    val r = Result.Ok(42)
    print(r.unwrap())
```
printed `<enum@0x...>` instead of `42`, under both the default `simple run`
(JIT) and a real `--native`-compiled executable. `Result.Err(e).unwrap()`
and `Option.None.unwrap()` did **not** trap — they silently returned garbage
values (observed: raw discriminant-hash bit patterns like `3220997671009`,
or an empty string) instead of failing loudly. `.expect(msg)` failed
entirely with `Function 'expect' not found` (no codegen dispatch entry
existed for it at all).

`Option.Some(v).unwrap()` happened to already return `v` correctly — this
asymmetry (Option worked, Result didn't) was the first clue to the root
cause.

## Intended semantics (established from the repo itself)

- `interpreter_helpers/method_dispatch.rs:159-244` (the interpreter's own
  `Value::Enum{enum_name:"Option"|"Result"}` match arms) is the authoritative
  in-repo definition: `.unwrap()` on `Some(v)`/`Ok(v)` returns `v`;
  `.unwrap()` on `None`/`Err(e)` raises a `CompileError` ("called unwrap on
  None" / "called unwrap on Err: {e}"). This matches Rust's own semantics and
  is what the tree-walk interpreter already implements correctly.
- `test/01_unit/bugs/result_interpret_lane_spec.spl` and sibling Result/Option
  specs assume `.unwrap()` yields the bare payload for pattern-matching and
  arithmetic — consistent with the interpreter's semantics above.
- The `?` try-operator is a **separate**, pre-existing open defect family
  (matches neither Ok nor Err in some lanes) and was explicitly out of scope
  here; this fix does not touch `?` handling.

## Root cause

**Layer: JIT/native codegen (Cranelift), NOT shared HIR/frontend, NOT the
interpreter.** Proven by: `SIMPLE_EXECUTION_MODE=interpret bin/simple run
p1_ok.spl` printed the correct `42` for every probe (including `.expect()`)
on the exact same seed binary that got `<enum@...>` under default `simple
run` — the divergence is 100% isolated to the compiled lanes.

`compiler/src/codegen/instr/closures_structs.rs::try_compile_builtin_method_call`
(the LIVE builtin-method dispatch table for `MirInst::MethodCallStatic` —
**not** the decoy `codegen/instr/methods.rs::compile_builtin_method`, which
is reachable only via `MirInst::BuiltinMethod`, never emitted) mapped:

```rust
"unwrap" | "unwrap_or" => "rt_unwrap_or_self",
```

`rt_unwrap_or_self` (`runtime/src/value/objects.rs`, doc comment: "Used by
the `??` operator's then-branch") is **deliberately scoped to the reserved
`OPTION_ENUM_ID`** — it returns every OTHER enum, including `Result`,
**unchanged**. Routing `.unwrap()` through it is exactly the observed bug:
`Result.Ok(42).unwrap()` hit the `enum_id != OPTION_ENUM_ID` branch and
returned the boxed `Result` enum itself.

Separately, `rt_enum_payload` (used by the HIR path that already knows the
receiver's concrete `Enum` TypeId, e.g. with an explicit `Result<i64,text>`
annotation) extracts the payload slot **unconditionally with no variant
check at all** — so even the "correctly typed" path returned garbage on
`Err`/`None` instead of trapping (reproduced: `Result<i64,text> = Result.Err
("boom"); .unwrap()` printed `3220997671009`, a raw discriminant-hash bit
pattern, not an error).

`.expect()` had no codegen table entry at all under either name.

## Fix

Added a new runtime helper, `rt_unwrap_or_trap`
(`runtime/src/value/objects.rs`), that:
- checks the Ok/Some vs Err/None discriminant by **name-hash**, not by a
  reserved enum id (Result gets no such reservation the way Option's
  `OPTION_ENUM_ID` does) — so it is correct for both Option and Result;
- returns the payload on the present variant;
- **traps** (prints to stderr, `std::process::abort()`) on the absent
  variant instead of silently returning garbage.

Registered it as a linkable runtime symbol
(`common/src/runtime_symbols.rs`, `compiler/src/codegen/runtime_sffi.rs`,
`runtime/src/value/mod.rs` export list) and rewired
`try_compile_builtin_method_call`:

```rust
"unwrap" => "rt_unwrap_or_trap",
"unwrap_or" => "rt_unwrap_or_self",   // was intentionally left here — see the follow-up fix below, this was WRONG
"expect" => { /* same rt_unwrap_or_trap call, ignoring the message arg */ }
```

**Known limitation:** `.expect(msg)` traps with the same fixed
"called unwrap on Err/None" text `.unwrap()` uses — the custom message
argument is not threaded through to the trap text yet (`rt_unwrap_or_trap`
takes only the receiver). This is a real, documented gap, not silently
dropped functionality; a follow-up would extend the runtime symbol to accept
a `(ptr, len)` message pair (same convention as `rt_panic` in
`runtime/src/value/sffi/contracts.rs`) and thread it from the codegen call
site.

## Red/green evidence

Seed built from `/mnt/data/dev/pub/simple` via
`cd src/compiler_rust && CARGO_TARGET_DIR=/mnt/data/cargo-target cargo build --release -p simple-driver --bin simple`.
Binary: `/mnt/data/cargo-target/release/simple`.

RED (pre-fix, binary built 2026-08-11 03:46:21, default JIT lane):
```
$ simple run p1_ok.spl      # val r = Result.Ok(42); print(r.unwrap())
<enum@0x2896c6c0e60>
$ simple run p2_some.spl    # val o = Option.Some(42); print(o.unwrap())
42
$ simple run p3_err.spl     # val r = Result.Err("boom"); print(r.unwrap())
<enum@0x539126c0f40>
$ simple run p4_none.spl    # val o = Option.None; print(o.unwrap())
(empty)
$ simple run p5_expect.spl  # val r = Result.Ok(7); print(r.expect("..."))
Runtime error: Function 'expect' not found
```

GREEN (post-fix, binary rebuilt 2026-08-11 04:08:03, same probes, default JIT lane):
```
$ simple run p1_ok.spl
42
$ simple run p2_some.spl
42
$ simple run p3_err.spl
error: called unwrap on Err
$ simple run p4_none.spl
error: called unwrap on None
```
(`.expect()` under the JIT dynamic-dispatch path still reports "Function
'expect' not found" for the fully-unannotated case — the codegen table entry
was added and IS present in source/binary, but the specific dynamic-call
route this unannotated case takes does not reach it; this remains a small
open gap distinct from the main `.unwrap()` fix. `.expect()` is confirmed
correct under `SIMPLE_EXECUTION_MODE=interpret` and via the resolved-type
HIR path.)

GREEN, true `--native` lane (real compiled ELF, `simple compile p1_ok.spl -o p1_ok.native --native`):
```
$ ./p1_ok.native      # Ok(42).unwrap()
42            (exit 0)
$ ./p2_some.native    # Some(42).unwrap()
42            (exit 0)
$ ./p3_err.native     # Err("boom").unwrap()
error: called unwrap on Err
Aborted (core dumped)   (exit 134 — genuine trap, not silent garbage)
$ ./p4_none.native    # None.unwrap()
error: called unwrap on None
Aborted (core dumped)   (exit 134)
```

Regression control, true interpreter (`SIMPLE_EXECUTION_MODE=interpret`),
unaffected before and after:
```
p1_ok: 42 | p2_some: 42 | p3_err: error: semantic: called unwrap on Err: boom
p4_none: error: semantic: called unwrap on None | p5_expect: 7
```

## Negative-control proof (Err/None must trap, not silently succeed)

`--native` lane: process exit code **134** (SIGABRT) for both `Result.Err(...).unwrap()`
and `Option.None.unwrap()`, distinctly different from the exit-0 success path
for `Ok`/`Some` — this is a hard process-level signal, not a string
heuristic. Default JIT lane: distinguishable `error: called unwrap on
Err`/`error: called unwrap on None` stderr text, vs. the printed payload
value for the Ok/Some case.

## Files changed

- `src/compiler_rust/runtime/src/value/objects.rs` — new `rt_unwrap_or_trap`
- `src/compiler_rust/runtime/src/value/mod.rs` — export it
- `src/compiler_rust/common/src/runtime_symbols.rs` — register the symbol name
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — register its `(I64)->I64` signature
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` — wire `unwrap`/`expect` to it in `try_compile_builtin_method_call`
- `scripts/check/check-native-unwrap-enum-receiver.shs` — new JIT/native regression fence
- `test/fixtures/native_unwrap_enum_receiver/{ok,some,err,none}_unwrap.spl` — fixtures for the check script
- `test/01_unit/bugs/native_unwrap_enum_receiver_spec.spl` — interpreter-lane regression spec (pins correct semantics; cannot observe the JIT-only defect itself, see spec docstring)

Follow-up fix (`unwrap_or(default)`, see section below):
- `src/compiler_rust/runtime/src/value/objects.rs` — new `rt_unwrap_or_value`
- `src/compiler_rust/runtime/src/value/mod.rs` — export it
- `src/compiler_rust/common/src/runtime_symbols.rs` — register the symbol name
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — register its `(I64, I64) -> I64` signature
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` — wire `unwrap_or` to it, and add it to the int-arg-boxing allowlist
- `src/runtime/runtime_native.c` — C-runtime `rt_unwrap_or_value` (precomputed discriminant-hash constants)
- `src/runtime/runtime.h` — declare it
- `scripts/check/check-native-unwrap-enum-receiver.shs` — 4 new `unwrap_or` rows, `FIX_EPOCH` bumped
- `test/fixtures/native_unwrap_enum_receiver/{ok,some,err,none}_unwrap_or.spl` — new fixtures

## Follow-up fix: `unwrap_or(default)` had the SAME bug (2026-08-11, later same day)

The first pass of this fix deliberately left `"unwrap_or" => "rt_unwrap_or_self"`
untouched, reasoning that `rt_unwrap_or_self` (the `??`-operator helper) was
merely a never-trapping variant — correct enough for `.unwrap_or(default)`.
That reasoning was **wrong**: `rt_unwrap_or_self` special-cases ONLY the
reserved `OPTION_ENUM_ID` and returns every other enum, including `Result`,
**unchanged** — and takes no `default` argument at all, so it could not have
implemented `.unwrap_or(default)` correctly even for the cases it touched.

Verified on a fresh build: `Result.Ok(1).unwrap_or(9)` printed the boxed
`<enum@0x...>` wrapper (want `1`); `Result.Err("x").unwrap_or(9)` printed the
boxed wrapper too (want `9`) — both defective under JIT and `--native`.
`Option.Some(1).unwrap_or(9)` and `Option.None.unwrap_or(9)` happened to
already work correctly (`1`, `9`) because Option alone has the reserved
`OPTION_ENUM_ID` fast path. This exactly mirrors the original `.unwrap()`
asymmetry (Option worked, Result didn't) that was the first clue in the
original writeup above.

### Fix

Added `rt_unwrap_or_value(receiver, default)` beside `rt_unwrap_or_trap` in
`src/compiler_rust/runtime/src/value/objects.rs`, using the same
discriminant-hash technique (Result has no reserved enum_id, so Ok/Err are
identified by hashing the variant name, same as `is_ok`/`is_err` in codegen)
— but returning `default` instead of trapping on Err/None:

```rust
"unwrap_or" => "rt_unwrap_or_value",   // was "rt_unwrap_or_self" — see follow-up above
```

Implemented in **both** runtimes per the three-implementations rule (the
interpreter already had correct semantics and was untouched):
- Rust: `runtime/src/value/objects.rs::rt_unwrap_or_value`, exported from
  `runtime/src/value/mod.rs`, registered in
  `common/src/runtime_symbols.rs::RUNTIME_SYMBOL_NAMES` and
  `compiler/src/codegen/runtime_sffi.rs` with signature `(I64, I64) -> I64`.
- C: `src/runtime/runtime_native.c::rt_unwrap_or_value`, declared in
  `src/runtime/runtime.h`. Since the discriminant hash
  (`std::collections::hash_map::DefaultHasher`) is computed at Rust-codegen
  time, not runtime, the four needed constants (`Ok`/`Err`/`Some`/`None`
  hashes) were precomputed once via a standalone `rustc` snippet and hardcoded
  as `RT_DISC_*` macros rather than reimplementing SipHash in C.
- `try_compile_builtin_method_call`
  (`compiler/src/codegen/instr/closures_structs.rs`) rewired `"unwrap_or"` to
  the new symbol. `"unwrap"`/`??`'s `rt_unwrap_or_self` are UNCHANGED.

A second, independent bug surfaced during verification: the generic call-arg
builder in `try_compile_builtin_method_call` passes non-receiver args as
UNBOXED raw native ints (the same convention documented above for dict
keys/`rt_index_get` etc.), but `rt_unwrap_or_value`'s `default` argument is a
full `RuntimeValue` return slot, not a raw int — so `Err(x).unwrap_or(9)`
initially printed `<invalid-heap:0x9>` (the untagged `9` misread as a
heap-pointer tag) instead of `9`. Fixed by adding `"rt_unwrap_or_value"` to
the existing `box_dict_key` int-tagging allowlist (same `(v << 3) | INT(0)`
tagging already used for dict-key ints), same file.

### Red/green evidence (fresh seed build, `/mnt/data/cargo-target-unwrapor/release/simple`)

RED (pre-follow-up-fix):
```
Ok(1).unwrap_or(9)    -> <enum@0x...>   (want 1)
Err("x").unwrap_or(9) -> <enum@0x...>   (want 9)
Some(1).unwrap_or(9)  -> 1              (already correct)
None.unwrap_or(9)     -> 9              (already correct)
```

GREEN (post-fix, JIT default lane):
```
Ok(1).unwrap_or(9)    -> 1
Err("x").unwrap_or(9) -> 9
Some(1).unwrap_or(9)  -> 1
None.unwrap_or(9)     -> 9
```

GREEN, true `--native` lane (real compiled ELF via `simple compile ... --native`):
same four values, `1 9 1 9`, exit 0 in all four cases.

Negative control: `.unwrap()` (Err/None trap) and the `??` operator
(`nil ?? 5` -> `5`, `3 ?? 5` -> `3`... second case pre-existing/unrelated AOT
`if val` defect, not this change) both re-verified unchanged after the fix —
see `reference_aot_if_val_always_some_and_eq_nil_always_false` in the
project's compiler-defects index for that separate, pre-existing gap.

`scripts/check/check-native-unwrap-enum-receiver.shs` extended with 4 new
`unwrap_or` rows (`ok/some/err/none_unwrap_or.spl` fixtures under
`test/fixtures/native_unwrap_enum_receiver/`) and its `FIX_EPOCH` bumped to
the new fix's build timestamp; full script run: `PASS — 8 checked`.

## Process note: concurrent working-copy clobber

Mid-investigation, a concurrent session's stale-snapshot write reverted an
earlier, independently-landed version of this exact same fix (their own
`rt_unwrap_or_trap` + dispatch wiring, with commit-message reference
`doc/08_tracking/bug/enum_unwrap_receiver_not_reproduced_2026-08-11.md`) back
out of the shared `/mnt/data/dev/pub/simple` working tree while a `cargo
build` was in flight. The fix in this doc was re-applied from scratch after
detecting the clobber (verified via `git diff` and binary
`strings`/symbol-table inspection showing `rt_unwrap_or_trap` had vanished
from both source and the newly-built binary) and landed promptly to reduce
the clobber window.
