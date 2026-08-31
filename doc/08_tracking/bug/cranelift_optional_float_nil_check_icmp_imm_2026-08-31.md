# Optional-FLOAT nil-check emits `icmp_imm.f32`, cranelift verifier rejects it, function is silently stubbed

Date: 2026-08-31
Backend: cranelift (native-build)
Severity: silent wrong-code risk — the build does not abort by default, it STUBS
the affected function.

## Symptom

```
inst130 (v168 = icmp_imm.f32 eq v164, 3): has an invalid controlling type f32
    (allowed set is ValueTypeSet { ... ints: {3,4,5,6,7} ... floats: {} })
[CODEGEN-STUB-FALLBACK] body compilation failed for 'parse_pct_value':
    ModuleError("Compilation error in 'parse_pct_value': Verifier errors")
```

`icmp_imm` is an INTEGER compare. The `eq ..., 3` shape is the optional
discriminant/tag test for a nil-check, but it is being emitted against the
**float payload** (`f32`) instead of against the tag. Cranelift's verifier
correctly refuses it — `icmp_imm`'s allowed controlling types are integers only,
and its float set is empty.

## Minimal reproduction (verified both ways)

Two fixtures, identical semantics, built with
`native-build --backend cranelift`:

**(a) FAILS — explicit nil-check on an optional float**

```simple
pub fn parse_a(s: text) -> f32:
    val n = s.parse_f64()
    if n != nil:
        val nval = n ?? 0.0
        return nval.to_f32()
    0.0
```
=> `exit=1`, `icmp_imm.f32` verifier error.

**(b) CLEAN — same semantics without the explicit nil-check**

```simple
pub fn parse_b(s: text) -> f32:
    val n = s.parse_f64()
    val nval = n ?? 0.0
    nval.to_f32()
```
=> `exit=0`.

So the trigger is specifically the **`!= nil` comparison on an optional float**.
The `??` coalesce operator needs the same discriminant test and lowers it
correctly, which localises the defect to the nil-comparison lowering path rather
than to optional-float representation in general.

## Why this is worse than a build failure

`native-build`'s default is `[CODEGEN-STUB-FALLBACK]`: the offending function is
replaced by an **empty stub** and compilation continues. The compiler's own
message says it plainly — `set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs
instead (unsafe — binary will silently misbehave)`. Any binary built through
this path therefore contains a silently non-functional `parse_pct_value`: every
CSS percentage would parse as 0. This is the same class as the 2026-08-21
`rt_unwrap_or_trap` incident, where a tolerated link-time hole became a runtime
SEGV.

## Where it bit

`src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl::parse_pct_value`, which
had the pattern twice (the `%` branch and the fallthrough). It blocked the
x86_64 SimpleOS WM desktop kernel build
(`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`).

## Source workaround applied (recorded, not silent)

Both branches were rewritten to the `?? 0.0` form. This is exactly equivalent:
a nil parse yields `0.0`, which is the same value the removed `return 0.0`
fallthrough produced. A comment at the site names this record so the change
cannot be mistaken for style churn or quietly reverted.

**The workaround is NOT the fix.** The pattern `if <optional float> != nil:` is
idiomatic and certainly appears elsewhere; every other occurrence is still
silently stubbed today. The real fix is in the nil-comparison lowering: emit the
discriminant test against the optional's TAG, not its payload.

## Suggested next step

Grep for `!= nil` / `== nil` on optional float-typed values across `src/`, and
add a codegen regression test asserting that fixture (a) compiles — a
verifier-rejected body must be a hard error for this pattern, not a stub.

---

## CORRECTION (same day): the trigger is the EARLY RETURN, not `!= nil`

The characterisation above ("the trigger is specifically the `!= nil` comparison
on an optional float") is **wrong**, and the workaround derived from it did not
work: rewriting `parse_pct_value` to `?? 0.0` while keeping its branch-and-
early-return shape reproduced the identical error on the identical function.

Proper bisection, each a standalone fixture built with
`native-build --backend cranelift`:

| fixture | shape | result |
|---|---|---|
| (a) | `!= nil` unwrap, inside branch with early `return` | **ICMP_IMM** |
| (b) | `?? 0.0`, single, tail position, no branch | CLEAN |
| (c) | `?? 0.0` x2, inside branch with early `return` (the failed workaround) | **ICMP_IMM** |
| (d) | as (c) but with `parse_f64()` bound to a `val` first | **ICMP_IMM** |
| (e) | `?? 0.0` **x2**, no branch, no early return | CLEAN |
| (f) | `?? 0.0` **x1**, inside branch with early `return` | **ICMP_IMM** |
| (g) | branch chooses the *string*; one `?? 0.0` in tail position | CLEAN |

(e) vs (f) is the decisive pair: two unwraps with no branch are fine, one unwrap
inside a branch that returns early is not. So the defect is **not** in the
unwrap operator (`??` and `!= nil` behave identically — both are fine in tail
position, both fail inside an early-returning branch), and **not** in the number
of unwrap sites.

**Correct statement of the bug:** unwrapping an optional FLOAT inside a
conditional branch that performs an early `return` emits the optional's
discriminant test as `icmp_imm` against the **float payload** instead of the
tag. The multi-exit control flow is what moves the test onto the wrong value;
in single-exit tail position the same source lowers correctly.

## Corrected workaround

`parse_pct_value` is now written in the (g) shape: the branch selects the
*string* to parse, and there is exactly one optional-float unwrap, in tail
position, with no early return. Semantics are unchanged (a `%` suffix is
stripped; an unparseable value still yields `0.0`).

## Method note, worth keeping

The first workaround was adopted from a two-fixture comparison — (a) fails,
(b) is clean — and the difference was attributed to the operator when the
fixtures ALSO differed in control flow. It cost a full ~1 hour rebuild to
discover. When two fixtures differ in more than one dimension, the bisection is
not finished. The pair that actually isolates a variable here is (e)/(f), which
hold the operator and the site count fixed and vary only the early return.
