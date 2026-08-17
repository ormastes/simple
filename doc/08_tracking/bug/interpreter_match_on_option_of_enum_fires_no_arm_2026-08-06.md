# Interpreter: `match` on an `Option<Enum>` value directly fires no arm

- **Filed:** 2026-08-06
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** Medium-High — silent, no error, no crash
- **Component:** interpreter — Option/enum discriminant
- **Engine:** `SIMPLE_EXECUTION_MODE=interpret` ONLY. The JIT handles this case correctly.

## Fix landed (2026-08-06)

Root-caused and fixed in the pure-Simple interpreter's own match-pattern code
(`src/compiler/10.frontend/core/interpreter/eval.spl`,
`match_enum_variant_pattern`), independent of the Rust-seed measurement
below (confirmed a genuinely different root cause from the sibling JIT bug,
exactly as this doc predicted).

**Root cause.** `match_enum_variant_pattern` recognizes the "boxed enum"
runtime shape purely by the presence of a `__tag` field (`val_is_boxed_enum`),
then compares that field's TEXT directly against the target pattern's variant
name. An `Option::Some`/`Option::None` wrapper (the boxed struct
`eval_option_binding_value`/`eval_try` already know how to unwrap by struct
name elsewhere in this same file) is itself boxed exactly the same way
(`__tag` = `"Some"`/`"None"`, `__payload` = the wrapped value) — so when the
scrutinee is such a wrapper, the tag compared was the WRAPPER's own tag,
never the enum's: `"A"`/`"C"` can never equal `"Some"`, so every real-variant
arm silently failed and control fell to `case _` (or, with no wildcard arm,
returned nil with only a warning). The bare-name pattern path (`case Red:`,
same file, ~line 823) had the identical defect via its own duplicate
boxed-tag comparison.

**Fix.** `match_enum_variant_pattern`, when the scrutinee is boxed and the
target variant is neither `"Some"` nor `"None"`, now checks the scrutinee's
own STRUCT NAME (not merely the presence of `__tag`) for literally
`"Option::Some"` / `"Option::None"` before comparing tags. If so it unwraps
one layer — recursing into the payload for `Some`, or reporting no-match for
`None` — before ever comparing the outer tag against the target variant. This
mirrors how `!`/`.unwrap()` already unwrap such a wrapper elsewhere in this
interpreter (`eval_try` in `eval_access.spl`). The bare-name pattern path now
delegates to the same fixed function instead of duplicating the (buggy)
tag-compare logic.

**Verified directly, not just via the Rust seed.** Both
`match_enum_variant_pattern` and the value constructors it depends on
(`val_make_struct` et al.) are plain exported functions in the pure-Simple
interpreter, reachable from an sspec `it` block via
`use compiler.core.interpreter.eval.{match_enum_variant_pattern}` /
`use compiler.core.interpreter.value.{val_make_struct, ...}` — this let the
bug be reproduced and the fix be verified as REAL BEHAVIOR (not a
source-text assertion) entirely inside the pure-Simple interpreter, without
needing a full bootstrap: before the fix,
`match_enum_variant_pattern(Option::Some(E::A(7)), "A", [])` returned
`false`; after the fix it returns `true`, with the plain-boxed baseline
(`match_enum_variant_pattern(E::A(7), "A", [])`) unaffected (`true` in both
cases). (Driving the FULL pipeline — `core_interpret`/`_core_run_pipeline`,
which would exercise the exact fixture's `main()` end-to-end — hit unrelated
cross-module symbol-resolution gaps, `jit_init_with_backend not found` then
`val_reset not found`, when invoked this way from a hosted spec; calling the
fixed function directly sidesteps that and is a strictly stronger check of
the actual defect anyway.)

**Regression spec:**
`test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl`
(7 examples: plain-boxed baseline positive/negative, `Option::Some`-wrapped
payload-carrying and payloadless variants, `Option::Some` wrapper against an
unrelated variant, `Option::None` wrapper against any real variant, and that
`Some`/`None` patterns still match the wrapper itself rather than being
unwrapped). Sabotage-checked: reverting the fix reproduces exactly 2 failures
(the two "the bug" examples) while the other 5 (including the
`Some`/`None`-still-match-wrapper case) stay green; reapplying restores all 7.

## Symptom

Matching an `E?` value **directly**, without force-unwrapping it first, falls
through every declared arm under the interpreter. Nothing throws; the match
executes and simply recognizes no variant.

## Why this is filed separately

This is the **exact inverse** of
`enum_match_no_arm_when_entry_in_same_package_2026-08-06.md` (the `?`-to-`!`
force-unwrap defect, which is JIT-only). Same fixture, opposite engines:

| case | JIT (default) | `interpret` |
|---|---|---|
| direct construct + match | `A7` | `A7` |
| payload variant after `!` | **FALLTHROUGH** | `A7` |
| payloadless variant after `!` | **FALLTHROUGH** | `Green` |
| **match the `E?` value directly (no `!`)** | `A7` | **FALLTHROUGH** ← this bug |

They are two distinct defects with opposite engine polarity and almost certainly
different causes, so fixing one will not address the other.

## The consequence worth internalizing

**Neither engine is a control for the other on Option/enum matching.** "It works
under `interpret`" is not evidence the JIT path is sound, and "it works under the
JIT" is not evidence the interpreter path is sound. Any triage that uses one
engine to validate the other on this code shape is invalid.

Both failures are also *silent*: a reducer that matches no arm returns unchanged
state. A spec asserting post-match state fails with a confusing diff; a spec
asserting only that the surrounding code ran **passes vacuously**.

## Repro

`test/fixtures/repro/compiler/enum/enum_match_after_option_unwrap_repro.spl`,
line 4 of its table. Run it under `SIMPLE_EXECUTION_MODE=interpret`.

Measured with the Rust bootstrap seed
`bin/release/x86_64-unknown-linux-gnu/simple` (md5
`ed53cc5f255e269ca27c4cd83b17aef9`), which is what `bin/simple` currently is.

## Not yet done

- ~~Cause not localized.~~ DONE — see "Fix landed" above:
  `match_enum_variant_pattern` compared an `Option::Some`/`None` wrapper's own
  tag instead of unwrapping it first.
- ~~Not determined whether payloadless enums behave the same here~~ DONE —
  they do (see the payloadless regression example); payloads are irrelevant
  here too, same as the sibling JIT defect.
- ~~No fix attempted: the measured failure is in the Rust seed~~ SUPERSEDED —
  the same defect shape was independently reproduced and fixed directly in
  the pure-Simple interpreter (in scope), verified by real execution rather
  than by relying on the Rust-seed measurement. Not re-verified against the
  ORIGINAL committed fixture end-to-end (that requires driving `main()`
  through the full pipeline, which hit the unrelated symbol-resolution gaps
  noted above) — still worth doing once a pure-Simple self-hosted binary is
  available and those gaps are separately resolved.

## Related

- `enum_match_no_arm_when_entry_in_same_package_2026-08-06.md` — the inverted,
  JIT-only sibling. Read both together.
- Interpreter Option encoding uses `__tag`, not a struct name.
- Neither engine is trustworthy in isolation (2026-07-27).

## ALREADY_FIXED — verified 2026-08-17 (P2 triage, compiler lane)

Reproduce-first re-run of the recorded reproducer at HEAD:

```
$ bin/simple test test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl
Results: 7 total, 7 passed, 0 failed          # rc=0
```

`match` on an `Option<Enum>` value now fires the correct arm. Closing as
already fixed; no source change was made by this lane.
