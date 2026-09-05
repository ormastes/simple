# A NONEXISTENT method (`ByteSpan.at(0)`) silently returns 3 instead of erroring

Status: STILL-OPEN (P1) — RUST-SEED defect, localized 2026-08-17 to
`src/compiler_rust/compiler/src/codegen/instr/calls.rs:3472`. Not fixed (seed
code; no guessed fix). Lane corrected: **JIT/native only — the interpreter now
errors correctly.** See Verification 2026-08-17b.
**Found:** 2026-08-17 — interpreter, `bin/simple run` probe (no daemon involved)

## Symptom

`ByteSpan.at(0)` — a method that **does not exist** — returns `3`, exit 0, no
diagnostic. A genuinely unknown name (`no_such_method_xyz`) correctly errors.

So the failure is not "unknown methods are ignored". Some resolution path
*matches* `at` against something and yields a value, while a name matching
nothing at all is properly rejected.

`3` is the nil tag word, so the caller receives the raw tag as if it were data.

## Why this is worse than a missing method

This is a silent-wrong-result GENERATOR, not a cosmetic gap. Any caller of a
misspelled, renamed, or not-yet-implemented method gets a plausible integer
instead of an error, and the mistake propagates silently into arithmetic and
comparisons. It also means "the method exists" cannot be inferred from "the call
returned something", which undermines probe-based triage everywhere else.

## Probable neighbourhood

Consistent with the qualified-name-resolved-by-bare-last-segment family found
the same day (a qualified `EnumName.Variant` resolving by its last segment
against global tables; `me char_code_at(v)` on a struct being stolen by
`rt_string_char_code_at` through codegen qualified-name SUFFIX resolution).
A suffix/partial match on `at` is the obvious hypothesis — `at` is a suffix of
`char_code_at`, `code_at`, and others.

## Not proven
Hypothesis above is UNVERIFIED — the resolution site was not located and no
suffix-collision probe was run. Only `ByteSpan.at` was observed. Whether the
JIT/native lanes behave the same is untested.

## Verification 2026-08-17b

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust seed, rebuilt 2026-08-17).

**Verdict: STILL-OPEN. Reproduced, root cause localized to the Rust seed, not
fixed** (per the rule against guessing a fix in `src/compiler_rust/**`).

### Repro (both files under .../scratchpad/)

`bs_at.spl` — the nonexistent method:

    use std.common.bytes.span.ByteSpan

    fn main():
        val b = ByteSpan.new([1u8, 2u8, 3u8])
        val r = b.at(0)
        print("at=${r}")

`bs_bogus.spl` — identical but `b.no_such_method_xyz(0)` (the control).

`at` really is absent from `ByteSpan`: `grep -n "fn " src/lib/common/bytes/span.spl`
lists `len is_empty get try_get slice slice_from to_bytes equals starts_with sum`
plus the statics — no `at`.

### Exact commands and exact outputs

    SIMPLE_EXECUTION_MODE=interpreter bin/simple run .../bs_at.spl
    error: semantic: method `at` not found on type `ByteSpan`
    rc=1

    SIMPLE_EXECUTION_MODE=jit bin/simple run .../bs_at.spl
    at=$nil
    rc=0

    SIMPLE_EXECUTION_MODE=interpreter bin/simple run .../bs_bogus.spl
    error: semantic: method `no_such_method_xyz` not found on type `ByteSpan`
    rc=1

    SIMPLE_EXECUTION_MODE=jit bin/simple run .../bs_bogus.spl
    Runtime error: Function 'ByteSpan.no_such_method_xyz' not found
    Runtime error: unresolved symbol -- this is a code-generation dispatch gap,
    not a program error. Refusing to substitute a placeholder value (it would
    render as the text 'error' and silently corrupt output).
    rc=70

**Two corrections to the original filing:**

1. The lane is **JIT/native, not the interpreter.** The interpreter rejects both
   names correctly, exit 1. The original filing attributed this to the
   interpreter; on this binary it is not reproducible there.
2. The observed value is `nil` (printed `at=$nil`), not the integer `3`. Same
   defect — a nil returned where an error is required — but the report's "`3`
   is the nil tag word reaching the caller as data" wording is a rendering of
   the same nil, not a separate integer result.

The control holds and is the whole point: on the SAME engine, same receiver,
same file shape, `no_such_method_xyz` fails closed with rc=70 and an explicit
"refusing to substitute a placeholder value" message, while `at` silently
succeeds with rc=0. So this is a NAME-KEYED match, exactly as suspected.

### Root cause — located, quoted, NOT fixed (Rust seed)

`src/compiler_rust/compiler/src/codegen/instr/calls.rs:3445-3472` — the
qualified-method fallback table, keyed on the method name after the last `.`,
with no receiver type available:

    if let Some(dot_pos) = func_name.rfind('.') {
        let method_part = &func_name[dot_pos + 1..];
        ...
        let runtime_func: Option<&str> = match method_part {
            "contains" | "contains_key" | "has_key" => Some("rt_contains"),
            "len" | "length" => Some("rt_len"),
            ...
            // `at` must NOT go straight to the text path: with an array
            // receiver that silently returned `nil` for every index.
            // `rt_at` tests the receiver and returns a real `Option` for
            // arrays while leaving text behaviour unchanged.
            "at" => Some("rt_at"),

`ByteSpan.at` reaches this table; `method_part` is `"at"`; the arm fires and the
call is lowered to `rt_at`. `rt_at` dispatches on the receiver, finds a
receiver that is neither text nor array, and returns nil — so the call
"succeeds". `no_such_method_xyz` matches no arm, falls through to the
unresolved-symbol path, and correctly aborts with rc=70.

The table's own comments already state the flaw ("this table cannot see the
receiver's type"), and it is the same class as
`doc/08_tracking/bug/array_guarded_method_names_no_mir_dispatch_2026-08-17.md`.
Sibling name-keyed tables carrying `"at"` that will need the same treatment:
`codegen/llvm/emitter.rs:334`, `codegen/llvm/functions.rs:2493`,
`codegen/llvm/functions/calls.rs:2219`, `codegen/instr/closures_structs.rs:1798`.

The original "suffix of `char_code_at`" hypothesis is **refuted**: the match is
an exact-equality arm on the segment after the final `.`, not a suffix match.
The record's "Not proven" section can be closed on that point.

## Verification 2026-08-17c — re-run on the NEWLY REDEPLOYED Rust seed

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime
2026-08-17 20:10:45 UTC.

**Verdict: STILL-OPEN — unchanged by the seed rebuild.** The rebuild carried no
change to the `calls.rs` name-keyed table, and the observed behaviour is
byte-identical to Verification 2026-08-17b.

    $ for m in interpreter jit; do for f in bs_at bs_bogus; do
        SIMPLE_EXECUTION_MODE=$m bin/simple run <scratch>/$f.spl; done; done

    --- interpreter bs_at
    error: semantic: method `at` not found on type `ByteSpan`
    rc=1
    --- interpreter bs_bogus
    error: semantic: method `no_such_method_xyz` not found on type `ByteSpan`
    rc=1
    --- jit bs_at
    at=$nil
    rc=0
    --- jit bs_bogus
    Runtime error: Function 'ByteSpan.no_such_method_xyz' not found
    Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a program error. Refusing to substitute a placeholder value (it would render as the text 'error' and silently corrupt output).
    rc=70

**Not fixed:** the fix belongs in `src/compiler_rust/**` and requires deciding
whether `rt_at` should fail closed on an unknown receiver (which would change
behaviour for every other receiver type reaching it) or whether the table must
gain a receiver-type guard. That is a seed change, and this task's rules forbid
guessing one.
