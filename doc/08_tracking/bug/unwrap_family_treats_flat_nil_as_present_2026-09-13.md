# `unwrap_or` / `unwrap` treat a FLAT nil as a present value (2026-09-13)

Status: OPEN. Pre-existing; found while fixing
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` and deliberately
NOT fixed there, because it is a change to shared helpers that both the LLVM and
Cranelift lanes execute and the Stage 2 lane was the priority.

## Symptom

```
val n: text? = nil
print n.unwrap_or("/fallback")     # prints EMPTY, not /fallback
```

Measured on the Rust seed's `native-build --backend llvm` (1-unit module,
2026-09-13), both before and after the LLVM unwrap-routing fix — the routing fix
is orthogonal and neither introduced nor repaired this.

## Mechanism

The Optional family has TWO representations: a boxed `Option` heap enum
(`OPTION_ENUM_ID`, discriminant `Some`/`None`), and a FLAT nullable where the
value is stored bare and absence is the nil sentinel. `rt_is_none`
(`src/compiler_rust/runtime/src/value/objects.rs:546`) handles both — it tests
`value.is_nil()` FIRST and only then looks for a boxed None.

The unwrap helpers do not. Each opens with:

```rust
let Some(p) = get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum) else {
    // Not a boxed enum — bare/flat-nullable payload convention: return
    // the raw value unchanged
    return value;
};
```

- `rt_unwrap_or_value` (`objects.rs:437`): a flat nil is "not a boxed enum", so
  it returns the nil instead of `default`.
- `rt_unwrap_or_trap` (`objects.rs:388`): same shape — a flat nil returns nil
  rather than trapping with `called unwrap on None`.
- `rt_expect_or_trap` (`objects.rs:~480`): same shape.

The "return the value unchanged" convention is right for a PRESENT flat value
and wrong for a flat nil, which is exactly the absent case these methods exist
to discriminate. `rt_is_none` already establishes that the runtime knows a flat
nil means absent, so the two halves of the same representation disagree — the
same class of split that
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` documents on the
present side.

## Scope

**All three engines, measured.** The helpers are shared: Cranelift routes
`.unwrap()` to `rt_unwrap_or_trap` (`codegen/instr/closures_structs.rs:2055`)
and LLVM now does too, so this is NOT a backend-parity defect. The tree-walk
interpreter is wrong as well — measured 2026-09-13, `simple run` on the same
source prints:

```
flat-nil unwrap_or: [nil]
present unwrap: [/present]
```

`interpreter_helpers/method_dispatch.rs:909` returns `recv_val` for any non-enum
receiver, and a flat nil IS a non-enum receiver, so it returns the nil for the
same reason the runtime helpers do. An earlier draft of this record claimed the
interpreter got it right; that was inferred from the fix for the PRESENT case
and is false. There is no correct reference engine to differential-test against
here — the expected behaviour has to come from the language definition, not from
a passing lane.

## Suggested fix

A one-line `if value.is_nil()` guard at the head of each of the three helpers,
BEFORE the `get_typed_ptr` probe:

- `rt_unwrap_or_value` -> return `default`
- `rt_unwrap_or_trap` -> `eprintln!("error: called unwrap on None"); abort()`
- `rt_expect_or_trap` -> take the caller's-message trap

**Scoping caveat for the trap half.** The `unwrap_or -> default` change is
unambiguous. The `unwrap`/`expect` -> trap change is NOT, because the measurement
above shows the tree-walk interpreter also returns nil silently on a flat nil:
making the native helpers abort would make native STRICTER than the reference
engine and create a NEW cross-engine divergence, which is the opposite of what
the rest of this family's fixes were for. The interpreter has to move in the same
change, or the trap half should be left alone and only `unwrap_or` fixed.

Landing this changes behaviour on code that currently gets a silent nil, so it
wants its own PR with the same runtime unit-test pattern as
`runtime/src/value/object_tests.rs:254` and a Stage 2 run behind it, not a
drive-by.
