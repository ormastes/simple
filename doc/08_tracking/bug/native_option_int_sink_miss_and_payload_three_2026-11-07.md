# Native Option -> integer sink: a MISS reads as 3, and a stored 3 reads as None

- **ID:** `native_option_int_sink_miss_and_payload_three_2026-11-07`
- **Severity:** P1 (silent wrong value)
- **Status:** open (proposal only; behaviour unchanged)
- **Layer:** `src/compiler/50.mir` integer sinks + runtime `rt_unwrap_or_self`
- **Follow-up of:** `native_list_any_get_i64_sink_returns_option_handle_2026-11-07`

## Defect 1 — MISS into an i64 sink is a silent 3

`fn f(w: [i64], i: i64) -> i64: w.get(i)` with `i` out of range (and the same
for `w: list` after the 2026-11-07 sink fix): the integer sinks unwrap through
`rt_unwrap_or_self` (`src/runtime/runtime_native.c:6269`,
Rust twin `objects.rs:530`). The None handle carries payload 3, and
`rt_unwrap_or_self` returns that payload, so the caller sees `3` with no
diagnostic. The interpreter's behaviour on a miss into a declared i64 is not
a valid integer either. Present for typed `[i64]` since the scalar-sink unwrap
landed (`optional_scalar_runtime_classified_three_becomes_none_2026-10-11`).

**Proposal:** at implicit-tail / `return` / `val y: i64 =` integer sinks
(`option_scalar_payload_of` and `option_payload_for_int_sink` in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`), emit
`rt_unwrap_or_trap` (already declared at `src/runtime/runtime.h:940`) instead
of `rt_unwrap_or_self`, for both typed scalar and `Optional(Any)` inners, so a
None reaching a non-optional integer slot traps loudly. `??`, `if val` and
`.unwrap_or` keep their own paths. Needs native verification after a Stage 2
rebuild; check the trap symbol is backed on every lane before switching.

## Defect 2 — a stored element 3 is classified None

`lower_array_first_or_last` normalizes the decoded element through
`ensure_option_handle` -> `normalize_option_handle` (runtime Some check:
already a handle -> unchanged, word 3 -> None, else Some). For a `list`
(`Array(Any)`) element, the element is int-decoded first, so a stored `3`
becomes the word 3 and is classified **None**: `w.get(0)` with `w = [3]` reads
as a miss (`?? -1` gives -1). The typed `[i64]` path does not have this
problem, because there `local_is_provably_scalar_payload` picks Some
statically.

**Proposal:** in `lower_array_first_or_last`, the some-arm is reached only
after the bounds check, so its payload is present by construction. Build Some
statically there (disc 0) instead of classifying at runtime.

## Related limit

`option_payload_for_int_sink` assumes an int-decoded payload. That holds only
for the array get/at/first/last producer. Other `Optional(Any)` producers
(`any?` params, tagged raw-probe dict reads) carry a tagged word, so the sink
returns the tagged word rather than the value. The limit is documented in the
helper's docstring.
