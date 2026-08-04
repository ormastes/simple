# JIT: `text.substring(n).to_int()` chained returns the raw text pointer, silently

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

Minimal repro (`build/tmp_gap/sub.spl`, run from the repo root so the relative
path actually compiles — an absolute path makes `simple run` exit 0 without
compiling):

```simple
fn main():
    val arg: text = "--timeout=800"
    print("chained={arg.substring(10).to_int() ?? -1}")
    val s: text = arg.substring(10)
    print("s=[{s}] len={s.len()}")
    print("viaval={s.to_int() ?? -1}")
```

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple run build/tmp_gap/sub.spl
chained=6445613581825          <-- WRONG (and differs run to run: it is a pointer)
s=[800] len=3
viaval=800                     <-- correct

$ SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpret bin/simple run build/tmp_gap/sub.spl
chained=800                    <-- interpreter is CORRECT
viaval=800
```

Expected: `chained == 800` on both engines.
Actual: under the JIT the chained form yields a large, run-varying i64 — the
heap address of the intermediate text — with **no error, no warning, exit 0**.
Binding the intermediate to a typed `val` first makes it correct, so the value
itself is fine; only the chained lowering is wrong.

`?? -1` does not rescue it: `to_int()` never reports failure here, it returns a
"successful" garbage integer.

## Root cause (proven)

`src/compiler_rust/compiler/src/codegen/instr/methods.rs:131`, inside
`compile_builtin_method`:

```rust
let from_ty = ctx.vreg_types.get(&receiver).copied().unwrap_or(TypeId::I64);
```

`to_int` is matched by the `numeric_cast_target` table a few lines above
(`"to_i64" | "to_int" => Some(TypeId::I64)`), and that block runs *before* the
text-receiver dispatch that would otherwise route to the `rt_string_to_int`
runtime helper (`codegen/instr/calls.rs:2817` and `:3369`,
`codegen/instr/closures_structs.rs:1702`).

When the receiver is a *directly chained* method result — `arg.substring(10)` —
its vreg carries no recorded type, so `vreg_types.get(&receiver)` misses and the
`unwrap_or(TypeId::I64)` default declares the receiver to already be an i64.
The very next branch is

```rust
let converted = if from_ty == to_ty { receiver_val }
```

`from_ty == to_ty == TypeId::I64`, so the cast compiles to **the receiver
unchanged** — the text pointer is handed back as the integer result. Binding to
`val s: text` records `TypeId` for that vreg, the miss does not happen, and the
correct `rt_string_to_int` path is taken.

This is the same failure shape the in-file comment at `methods.rs:110-120`
documents for `to_upper`/`to_utf8` (wildcard arm ⇒ `to_ty == from_ty` ⇒ silent
no-op); that fix corrected the *method-name* matching but left the *unknown
receiver type* default intact, so untyped receivers still collapse onto the
no-op arm.

## Blast radius

Any `<expr producing text>.to_int() / .to_i64() / .to_i32() / .to_u64() / ...`
where the receiver is not a named typed binding. It fails silently with a
plausible-looking integer, which makes it a false-green generator: an assertion
comparing two such values, or any arithmetic on them, will not raise.

One live instance was found and fixed in this lane:
`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` — the new
`--timeout=N` / `--seed=N` parsing had to be written with an intermediate
`val` (`timeout_value` / `seed_value`) because the chained form parsed
`--timeout=800` as `2363156932769`.

## Why not fixed now

The fix is in the Rust seed's Cranelift codegen, not in `.spl` — the standing
rule is to fix Simple source rather than the seed, and a codegen change here
needs a full Rust rebuild plus a regression sweep across every numeric-cast site
(the `numeric_cast_target` block is on the hot path for all of
`to_u8`…`to_f64`). The correct shape is almost certainly to stop defaulting an
unknown receiver to `TypeId::I64` and instead fall through to the regular
builtin dispatch (which knows how to call `rt_string_to_int`), but proving that
does not regress genuine integer-to-integer casts on untyped vregs is its own
lane.

Workaround until then: bind the intermediate to a typed `val`. Do **not** treat
that as the normal spelling — the chained form is valid Simple and works on the
interpreter.
