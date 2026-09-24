# phase 2: `str(i64)` returns a raw pointer instead of a text
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-09-13
**Lane:** phase 2 only (the pure-Simple Stage 2 compiler). Phase 1 (Rust seed) is correct.
**Severity:** high — silently wrong output, exit 0, no diagnostic.

## Symptom

```simple
var t = 0
t = t + 1
t = t + 2
var flag = 0
if t == 3:
    flag = 1
print "A_str=" + str(t)
print "B_eq3=" + str(flag)
print "C_lit=" + str(3)
```

| | phase 1 seed | phase 2 |
|---|---|---|
| `A_str` | `3` | `2083130940001` |
| `B_eq3` | `1` | `2083130938977` |
| `C_lit` | `3` | `2083130940001` |

## What this proves, and what it does NOT

`C_lit` is `str(3)` — a **literal**. It is corrupted identically, so nothing
about the arithmetic or the variable is at fault. And `str(t)` produces the
*same* word as `str(3)`, which independently confirms `t` really is 3: the
values are right, the conversion is wrong.

`str()` is handing back a pointer-shaped 64-bit word (~2.08e12, in the same
range as the other pointer-shaped corruptions seen in this lane) which `+` then
formats as a number instead of concatenating as text.

This is a SEPARATE defect from
`phase2_drops_loop_carried_accumulator_2026-09-13.md`, and finding it does not
retract that one. The accumulator bug was re-proved without any printing at all,
by branching on the value:

```
phase 2:  SUM_NOT_55 | SUM_IS_ZERO | COUNTER_OK
phase 1:  SUM_IS_55  | COUNTER_OK
```

So the loop really does lose `s`, and `str()` really does lose the conversion.
Two independent faults that happened to be visible through the same print
statements — which is exactly why the first probe's `sum=0` could have been
misread as a rendering artifact, and why it was worth re-proving by branch.

String interpolation (`"sum={s}"`) is NOT affected: it rendered `0` for a value
that is genuinely 0. Only the explicit `str()` call is broken.

## Reproduction

Phase 2 cannot finish a `native-build` (see
`phase2_file_size_garbage_breaks_capsule_receipt_2026-09-13.md`), so the object
is emitted with `compile --format=smf` and hand-linked:

```sh
. ./scripts/setup/windows-msvc-bootstrap-env.shs
sh build/p2run/build_and_run.sh <path-to-phase2-simple.exe> p2
```

`build/p2run/prog/zz_disc.spl` is the case above; `zz_sumproof.spl` is the
branch-only accumulator proof.

## Where to look

`str()` on an `i64` lowers to a runtime conversion that returns a heap text.
The returned word is reaching the caller undecoded — the same shape as
`rt_file_size` arriving as `1529351762689`
(`phase2_file_size_garbage_breaks_capsule_receipt_2026-09-13.md`). Whether
those share one cause in phase 2's SFFI return handling is unproven and worth
checking first, since a single fix might close both.

