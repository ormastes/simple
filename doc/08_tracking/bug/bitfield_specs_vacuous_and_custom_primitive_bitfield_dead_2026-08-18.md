# Bitfield "coverage" is vacuous, and `custom_primitive_bitfield.spl` is unreachable code

- **Status:** OPEN
- **Date:** 2026-08-18
- **Area:** `test/01_unit/compiler/mir/bitfield_mir_spec.spl`,
  `src/compiler/50.mir/custom_primitive_bitfield.spl`
- **Severity:** Medium (reported coverage does not exist; 285 lines of dead source)
- **Found while:** binary_runtime_hardening lane, goal 4 (SSpec bitfield/bit-table infra).

## Finding 1 — `bitfield_mir_spec.spl` asserts on string literals, not on the compiler

The file declares 19 examples and passes, but **every** assertion in it is of
this shape:

```
it "recognizes bitfield definitions":
    val code = """
    bitfield Flags(u32):
        enabled: bool
        priority: u4
    """
    check(code.contains("bitfield"))
    check(code.contains("Flags"))
```

`code` is a string literal defined three lines above; `code.contains("bitfield")`
is true by construction. Measured: the file contains 19 `it "` blocks, and
grepping every assertion line that is *not* `check(code.contains(...))` returns
only the two helper definitions at lines 5-9 — i.e. **zero** assertions reach
any bitfield implementation.

Consequences:

- The spec cannot fail for any compiler defect. Deleting all of
  `src/compiler/50.mir/mir_bitfield.spl` would leave it green.
- It inflates the bitfield example count (19 of the ~73 bitfield examples in
  the tree) with examples that test the Simple `text.contains` builtin.
- It imports nothing, so it has no positive control proving a subject module
  loaded — the failure mode the lane's spec standard exists to prevent.

A replacement must import the module under test and assert on its output, and
must carry a positive control that fails if the import silently resolves to
nothing.

## Finding 2 — `custom_primitive_bitfield.spl` is dead

`src/compiler/50.mir/custom_primitive_bitfield.spl` is 285 lines defining four
classes (`BitfieldBackingCheck`, `BitfieldFieldCheck`, `BitfieldLayout`,
`BitfieldValidator`, headed "AC-5/AC-6 custom primitive wrappers as bitfield
backing/field types").

Measured reachability, excluding the file itself and `vendor/`:

| symbol | references elsewhere in the tree |
|---|---|
| `BitfieldBackingCheck` | 0 |
| `BitfieldFieldCheck` | 0 |
| `BitfieldLayout` | 0 |
| `BitfieldValidator` | 0 |

The module is also **not exported** from `src/compiler/50.mir/__init__.spl`
(grep for `custom_primitive_bitfield` there returns nothing), and no `.spl`
file anywhere imports its module path. The only mention repo-wide outside the
file is a *comment* in
`src/compiler/90.tools/verify/aorte_obligation_census_scan.spl:58` naming its
"layout overflow" error text.

So it is unreachable from every lane: interpreter, JIT, AOT, native.

## Why this is filed rather than fixed

The obvious next move on Finding 2 — per CLAUDE.md ("NEVER add unused code -
delete completely") — is deletion, not test-writing. It was tempting to close
the "biggest bitfield test gap" by writing ~285 lines of specs for these four
classes; that would have been coverage theatre for code nothing calls, and
would have made the dead module *harder* to delete by giving it dependents.

Deletion is not done in this lane because it removes compiler source whose
AC-5/AC-6 requirement trail (`doc/02_requirements/`) has not been checked here
— if those acceptance criteria are still owed, the right fix is to *wire the
module up*, not to delete it. That decision belongs to the bitfield/MIR owner.

**Required next step:** classify `custom_primitive_bitfield.spl` as either
(a) obsolete -> delete, or (b) owed functionality -> wire into the MIR bitfield
path and cover with non-vacuous specs. Do not leave it in the current third
state, where it is neither reachable nor removed.

## Investigation: Is `custom_primitive_bitfield.spl` owed functionality?

The file header references "AC-5: Custom primitive wrappers as bitfield backing types / AC-6: Custom primitive wrappers as bitfield field types". Investigation verifies these requirements are **already satisfied elsewhere**.

### AC-5/AC-6 Specification

Both criteria are defined in `doc/05_design/language/syntax/bitfield_custom_type_design.md`. This design doc presents a comprehensive three-tier system for using custom types in bitfields (automatic inference, explicit bits at use site, and type-level repr declarations). The file is 717 lines and dates 2026-02-05.

### AC-5/AC-6 Implementation — ACTIVE, TESTED

The actual implementation lives in THREE places, NOT in the dead module:

1. **Canonical type validation:** `src/compiler/30.types/custom_primitive_info.spl` — contains `PrimitiveTypeResolver` class with methods `is_valid_underlying`, `resolve_bit_width`, `resolve_byte_size`, `is_integer_type` — exactly the functions the dead module's header claims as canonical but never uses.

2. **Backend bitfield lowering:** `src/compiler/70.backend/bitfield.spl:202-222` imports and calls these ACTIVELY:
   - `custom_primitive_integer_bit_width_by_name(name)` — line 202
   - `custom_primitive_backing_bits_by_name(name)` — line 222
   - `custom_primitive_underlying_name_by_name(name)` — line 204

   These functions are defined in `src/compiler/10.frontend/core/types.spl` and are in active use.

3. **Test coverage:** `test/unit/compiler/custom_primitive_sffi_spec.spl` (14.8 KB, 385+ lines) exercises bitfield support with custom primitives. Commit `95735a32453` landed this with message "feat(compiler): custom primitive SFFI public API — metadata, ABI mapping, bitfield support, lint classification, domain wrappers — 20 tests PASS" (2026-05-18).

### Conclusion: OBSOLETE — DELETE

The dead module duplicates validation logic that is already implemented, exported, and actively used in the backend. No AC-5/AC-6 functionality is missing; the requirement was completed via Option B (shared resolver) in commit `95735a32453`. The `custom_primitive_bitfield.spl` file is an incomplete, unreachable, never-wired predecessor to that implementation and serves no purpose in the current compiler.

**Recommendation:** Delete `src/compiler/50.mir/custom_primitive_bitfield.spl` (285 lines). The acceptance criteria AC-5 and AC-6 are proven satisfied by passing tests in the bitfield + custom-primitive integration test suite.

## RESOLVED — 2026-08-18 (both findings)

**Finding 1 (vacuous spec) — fixed.** `test/01_unit/compiler/mir/bitfield_mir_spec.spl`
was rewritten. 19 vacuous examples became 14 genuine ones. The new spec imports
`compiler.backend.bitfield.{BitLayout, bits_needed, would_straddle_word}` and
carries an explicit positive-control example that fails if the import resolves
to nothing. Every assertion now compares a COMPUTED value to a constant: mask
and shift arithmetic against the module's real `mask()`, write-then-read
round-trips proving the neighbouring field is untouched, truncation of a 5-bit
value into a u4, 3-field packing (u4@0, bool@4, u8@5) with each field
re-extracted, a u12 at offset 6 spanning two byte boundaries, signed i4 range
(-8..7), enum width inference, and word-straddle detection at 32- and 8-bit
words.

Evidence that it is no longer vacuous: on its first run the new spec went RED
(`14 total, 13 passed, 1 failed`) on a wrong expectation about
`would_straddle_word`, which returns `false` by design when
`field_width >= word_bits`. The module was correct and the expectation was
wrong; it was corrected and the genuine crossing cases `(6,4,8) -> true` /
`(4,4,8) -> false` were added. A vacuous spec cannot produce that signal.

```
before: Results: 19 total, 19 passed, 0 failed   (all assertions on string literals)
after:  Results: 14 total, 14 passed, 0 failed   (imports the module under test)
```

**Finding 2 (dead module) — deleted.** `src/compiler/50.mir/custom_primitive_bitfield.spl`
(285 lines) is removed. It was classified OBSOLETE, not owed, on this evidence:

- AC-5/AC-6 are specified in
  `doc/05_design/language/syntax/bitfield_custom_type_design.md` and were
  **completed** by commit `95735a32453` (2026-05-18, "custom primitive SFFI
  public API — metadata, ABI mapping, bitfield support ... 20 tests PASS").
- The live implementation is elsewhere and actively called:
  `src/compiler/70.backend/bitfield.spl:202-222` calls
  `custom_primitive_integer_bit_width_by_name`,
  `custom_primitive_underlying_name_by_name`, and
  `custom_primitive_backing_bits_by_name`, all defined at
  `src/compiler/10.frontend/core/types.spl:912,930,938`. Verified by grep, not
  taken on report.
- The deleted module duplicated exactly the validation its own header called
  canonical in `30.types/custom_primitive_info.spl`, and never called it.

Post-deletion evidence that nothing regressed:

```
test/01_unit/compiler/custom_primitive_sffi_spec.spl  Results: 20 total, 20 passed, 0 failed
test/01_unit/compiler/mir/bitfield_mir_spec.spl       Results: 14 total, 14 passed, 0 failed
```

Stated limitation: a full 3-stage `bin/simple build bootstrap` was NOT run, so
this proves the compiler's modules still load and the AC-5/AC-6 behaviour still
works — not that a from-scratch self-hosted rebuild is unaffected. The module
had zero importers and was absent from `50.mir/__init__.spl`, so a build-order
effect is not expected, but it is not proven here.
