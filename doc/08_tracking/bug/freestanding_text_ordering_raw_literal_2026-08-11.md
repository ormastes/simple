# Freestanding text ORDERING (`<`/`>`/sort) unreliable against a raw literal

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Status
**RESOLVED 2026-08-11.** Follow-up gap #1 flagged (but explicitly left open)
by `native_text_equality_against_empty_literal_unreliable_after_trim_lower_2026-08-11.md`
(commit `43aed2b9df8`), which fixed freestanding text **equality** against
raw literals but noted the **ordering** counterpart (`rt_text_cmp_any` /
`rt_native_cmp`) had the identical both-sides-heap requirement.

## Root cause (PROVEN)

Same class of defect as the equality fix, in the ordering primitive instead.
Three lanes actually implement string ordering (two others — `arm32`,
`x86_32`, plus `riscv64`/`riscv32` `baremetal_stubs.c` — define no
`rt_text_cmp_any` / `rt_native_cmp` at all, so there is nothing to fix
there: ordering operators are simply unsupported on those lanes):

| lane | file:line (pre-fix) | shape |
|---|---|---|
| x86_64 | `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:14630` | standalone `rt_text_cmp_any()`, required `IS_HEAP(left) && IS_HEAP(right)` else fell to a raw pointer/word compare |
| arm64 | `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:1035` | ordering inlined directly in `rt_native_cmp()`, same both-heap requirement |
| aarch64 | `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c:1624` | standalone `rt_text_cmp_any()`; `rt_as_string()` returns NULL for a raw literal, and the code then treated the raw side as a **zero-length string** (`blen = b ? b->len : 0`) rather than reading its actual bytes, so a heap string always compared "greater than" any raw literal regardless of content |

Hosted `rt_text_cmp_any` (`src/runtime/runtime_native.c:3396`) was already
correct — it goes through `rt_interp_cstr`, which normalizes both
tagged-heap and raw operands before `strcmp`. Only the freestanding lanes had
the gap.

Symptom: `x < "foo"` / `x > "foo"` / any sort comparator involving a raw
literal reflected the malloc/`.rodata` **address** of the two operands, not
their alphabetical content — same failure shape as the ordering-vs-address
bug already fixed for the general untyped case
(`jit_text_ordering_pointer_compare_2026-08-01.md`), but specific to a
literal operand on these lanes.

## Fix

Added a `rt_text_cmp_heap_vs_raw` (x86_64, arm64) / `rt_text_cmp_str_vs_raw`
(aarch64) helper per lane, mirroring the equality fix's safety rules exactly:
- raw is interpreted as `char*` **only** when the other operand is a proven
  heap string,
- a `< 0x10000` plausibility floor rejects nil/bool/small-int words (same
  `TAG_INT == 0x0` ambiguity as the equality fix, see
  `native_text_eq_any_untagged_smallint_deref_2026-07-23.md`),
- the scan is bounded by the heap string's own `len`, and a strcmp-style
  signed result (`-1`/`0`/`1`) is produced by comparing byte-for-byte and
  detecting the raw side's NUL terminator inline (no unbounded scan).

Files changed:
- `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`
- `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`

Fixed at the primitive — no call-site rewrite needed.

## Red-then-green (verbatim)

`src/runtime/test/rt_text_cmp_any_heap_vs_raw_selfcheck.c` (reimplements the
BEFORE/AFTER shape locally, same methodology as the equality selfcheck, so it
always demonstrates the defect regardless of the current state of the
production files; refuses to pass vacuously — exits 2 if the defect fails to
reproduce with the old predicate):

```
== BEFORE (shipped freestanding rt_text_cmp_any) ==
  REPRODUCED: heap "bar"/"foo"/"" vs raw same-content literal -> nonzero (pointer compare, not content)
== AFTER (heap-vs-raw content ordering) ==
  ok   cmp(heap "bar", raw "bar")   == 0                        = 0
  ok   cmp(raw "bar",  heap "bar")  == 0                        = 0
  ok   cmp(heap "",    raw "")      == 0                        = 0
  ok   cmp(heap "bar", raw "foo")   <  0                        = -1
  ok   cmp(heap "foo", raw "bar")   >  0                        = 1
  ok   cmp(heap "foo", raw "")      >  0                        = 1
  ok   cmp(heap "",    raw "foo")   <  0                        = -1
  ok   cmp(heap "bar", heap "foo")  <  0                        = -1
  ok   cmp(heap "foo", heap "foo")  == 0                        = 0
  ok   cmp(heap "foo", nil) does not crash, != 0                = 1
  ok   cmp(heap "",    small int 7) does not crash              = 1
  ok   cmp(heap "foo", small int 0) does not crash              = 1

PASS - 12 assertion(s) checked, defect reproduced before / fixed after
```

Negative controls included above: non-empty ordering still compares
correctly in both directions, the heap/heap path is unchanged, and small
non-pointer words are never dereferenced (empty string, small int 0/7, nil).

Guard red-then-green, confirmed by stashing the three fixed files and
re-running the guard:
```
FAIL — 3 of 5 check(s) failed; examples/.../x86_64/boot/baremetal_stubs.c examples/.../arm64/boot/baremetal_stubs.c examples/.../aarch64/boot/freestanding_runtime.c
```
then restoring the fix:
```
PASS — 5 check(s) passed, freestanding text-vs-raw-literal ordering fenced
```

## Guard

`scripts/check/check-freestanding-text-cmp-raw-literal.shs` — verdict as the
last stdout line (`PASS — <n> check(s) ...` / `FAIL` exit 1 / `ERROR —
nothing was checked` exit 2). Runs the selfcheck, asserts all three lanes
carry the fix, and FAILs on any **unlisted** freestanding
`rt_text_cmp_any`/`rt_native_cmp` definition so a newly added lane or
implementation cannot silently ship without it.

## Related
- `native_text_equality_against_empty_literal_unreliable_after_trim_lower_2026-08-11.md` (the equality sibling this follows up)
- `native_text_eq_any_untagged_smallint_deref_2026-07-23.md` (the tag-collision hazard both fixes guard against)
- `jit_text_ordering_pointer_compare_2026-08-01.md` (the general untyped-operand ordering defect, different lane)
