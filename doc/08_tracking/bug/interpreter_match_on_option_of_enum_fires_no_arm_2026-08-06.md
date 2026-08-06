# Interpreter: `match` on an `Option<Enum>` value directly fires no arm

- **Filed:** 2026-08-06
- **Status:** Open
- **Severity:** Medium-High — silent, no error, no crash
- **Component:** interpreter — Option/enum discriminant
- **Engine:** `SIMPLE_EXECUTION_MODE=interpret` ONLY. The JIT handles this case correctly.

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

- Cause not localized. The sibling JIT defect was traced to a missing
  `HirExprKind.Unwrap` arm in MIR lowering; this one is in the interpreter's
  own Option/enum discriminant handling and has not been traced.
- Not determined whether payloadless enums behave the same here (they do for the
  JIT defect — payloads were irrelevant there).
- No fix attempted: the measured failure is in the Rust seed, which is out of
  scope by policy.

## Related

- `enum_match_no_arm_when_entry_in_same_package_2026-08-06.md` — the inverted,
  JIT-only sibling. Read both together.
- Interpreter Option encoding uses `__tag`, not a struct name.
- Neither engine is trustworthy in isolation (2026-07-27).
