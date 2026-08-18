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
