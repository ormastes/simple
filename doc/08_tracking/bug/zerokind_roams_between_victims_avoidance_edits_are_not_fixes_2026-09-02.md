# E-MIR-TYPE-ZeroKind roams between victims — avoidance edits are not fixes

- **Filed:** 2026-09-02
- **Status:** SUPERSEDED — see addendum at the end of this record; the true
  causes have since been identified and both are fixed
- **Related:** `doc/08_tracking/bug/self_hosted_symbol_table_hirtype_garbage_at_rest_2026-08-31.md`
  (OPEN as of this filing — refuted three producer/reader fixes for the same
  symptom, concluded use-after-free)

## What this record is

A log of six consecutive attempts to make the `E-MIR-TYPE-ZeroKind` fatal in
Stage 3 MIR lowering go away by editing source at whatever call site it named.
Each attempt "worked" in the sense that the fatal's reported site moved
somewhere new after the edit; that was wrongly read as progress three times in
a row (runs B, C, D) before the pattern was recognised: the occurrence count
dropped once, from 6 to 2, on the very first edit (run B), and never moved
again across runs C through F. The table below is the only record of runs A
through E — no separate narrative for those five exists beyond what the table
columns capture (hypothesis tested, site, resulting count); do not infer detail
beyond that. Run F is the exception: it has its own write-up below the table
because, unlike A-E, its reasoning is now understood well enough to explain in
prose.

Summary of runs A-E from the table: **A** is the baseline measurement, 6
occurrences at `compile_specialized_template`, before any edit. **B** restored
an omitted Optional field (`entry_point: nil`) — this is the change later
submitted as PR #274 — and dropped the count to 2, at a new site (`_default`).
**C** changed a `-> text`-returning function to return `Ok(CompiledUnit(...))`
directly; count stayed at 2, site moved to `_release`. **D** switched a
constructor call from a static method to a re-exported free function; count
stayed at 2, site moved back to `_default`. **E** added a dead-copy guard at
`remember_local_hir_type`; count stayed at 2, site moved back to
`compile_specialized_template`. Run F (braced vs. unbraced import) is detailed
in its own section immediately below.

## Run F: braced-import hypothesis also refuted — the source-edit avenue is CLOSED

| run | hypothesis tested | site | count |
|---|---|---|---|
| A | (baseline) | `compile_specialized_template` | **6** |
| B | omitted Optional field (`entry_point`) | `_default` | 2 |
| C | `-> text` returning `Ok(CompiledUnit(...))` | `_release` | 2 |
| D | static-method vs re-exported free-fn constructor | `_default` | 2 |
| E | dead-copy guard at `remember_local_hir_type` | `compile_specialized_template` | 2 |
| F | unbraced `use a.b.C` vs braced `use a.b.{C}` | `_release` | 2 |

**Six runs. Five distinct, individually-plausible hypotheses. The count has not
moved off 2 since run B.** Only the very first drop (6 -> 2) was ever real.

Run F is worth its own note because the reasoning was the best of the five: it
explained a detail the others ignored — *why the fatal names a FUNCTION rather
than a statement*. `compile_specialized_template` is a stub whose every pipeline
step is commented out, so its parameters are unused; but lowering the SIGNATURE
still lowers each parameter type, which is why all three wrappers (identical
parameter lists) are interchangeable victims. Two of those six types
(`DiContainer`, `AopWeaver`) used the rare unbraced member-import form — 86
occurrences tree-wide against 5073 braced. Bracing them changed nothing.

The braced form is retained as convention normalisation, explicitly NOT as a fix.

### Conclusion: stop editing source against this

Five hypotheses at ~55 minutes per run produced **one bit** of information. Every
edit was an avoidance edit at a victim site; none touched the producer, because
the producer is the ABI itself. Continuing to guess at candidate crossings has
negative expected value.

**The next action must be the sibling doc's second-read tag probe** — read the
HirType tag twice across a suspect boundary and compare — which distinguishes
"dead copy minted in flight" from "use-after-free of the original" in ONE
instrumented run. Build the instrument before touching source again.

## Addendum (2026-09-02): the conclusion above is superseded

This record's conclusion pointed at the admitted Stage-2 native ABI as the
producer and recommended building the second-read tag probe before touching
source again. That diagnosis has been superseded: the residual count-2
behaviour was not one ABI-level defect but **two distinct, unrelated defects**
sitting behind the same symptom.

- The fill-path issue this record's run B avoided (an omitted Optional field
  falling through `ensure_option_handle` / `remember_local_hir_type`) was
  landed as PR #274, which clears **4 of the original 6** occurrences.
- The remaining 2 have a different producer entirely: a stolen `unwrap` at
  `expression_core.spl:50`, fixed in PR #295.

PR #291 (`work/stage3-segv-unwrap`) and PR #295 fix the same class of defect —
a bare `.unwrap()` silently hijacked by a module publishing its own `unwrap`
(e.g. `Poll`, `FailSafeResult`), returning raw 0 instead of failing safely —
at two different call sites. They are **one defect, two faces**: the same
stolen-unwrap mechanism, independently triggered in two places, which is why
building the tag probe recommended above was never necessary to explain the
roaming count.
