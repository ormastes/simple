# Bare-name registry collision: trigger conditions NOT established (lane PROBE1)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
renaming against is **unproven**, and the primary evidence for it has an internal
contradiction. Run inline by the orchestrator after the subagent lane was halted
on an API quota.

## Why this lane existed

Four lanes (ENUM1, QSK1, CKPT1, and PROBE1's own partial run) each failed to
reproduce the collision with a minimal probe. ~40 files have been renamed across
PTR1, PTR2, CKPT1 and QSK1 on the strength of a mechanism nobody had reproduced.

## What was tested (one factor per pair)

Engine: `bin/simple run` (deployed seed). Pre-rename tree = `git archive
5de6f3c56e8^` exported read-only to `/tmp`, containing all 9 colliding structs.

| # | Setup | Result |
|---|---|---|
| 1 | Real `SymbolKind`, exact `case Class \| Struct \| Enum \| Import:` arm from `is_static_method_call`, **post-rename** tree | correct (STATIC/STATIC/STATIC/STATIC/instance) |
| 2 | Identical probe, **pre-rename** tree (9 colliders present) | **correct — no collision** |
| 3 | Same + `use compiler.frontend.parser_types.{Class, Struct, Enum}` to force the colliders into scope | correct — but see the control below, this factor was never actually established |
| 4 | Same-file `enum Kind: Class...` + `struct Class:` **constructed and used**, bare `case Class \| Struct:` | correct |

### Control that invalidates test 3 — and probably the earlier lanes' probes

```
use compiler.frontend.parser_types.{TotallyNotARealName}   # name does not exist
→ exit=0, program runs normally
```

**An unresolved `use` silently succeeds.** So "I imported the colliding struct"
never establishes that the collider is in scope, and any probe whose premise was
an import proved nothing. Only a *declared and used* collider (test 4) is a valid
setup — and that one matched correctly too.

## The decisive discovery: this was already documented

`symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29.md`
already contains, at the section literally titled **"Negative controls (root
cause is NOT reproducible outside the real `HirLowering`/`SymbolTable`
machinery)"**:

- **Control #1** tested exactly this family — three sibling modules each
  declaring the same bare enum name, forcing the conflicting declaration to load
  first, construct-in-A / match-in-C — and it **matched correctly**. The doc
  concludes the registry-collision family is structurally real
  (`named_type_register` at `10.frontend/core/types.spl:559` is a flat,
  name-keyed, *not* module-qualified global; MIR's `enum_variant_index` is the
  same shape) "**but it is not what a small user-level program triggers under the
  currently-deployed engine**."

Every subsequent non-reproduction — four lanes plus this one — re-derived a
negative control that had been written down first. Nobody read it.

- **Control #3** records that `rt_enum_discriminant` **called from user `.spl`
  code returns garbage** and is "**itself unreliable as a raw diagnostic from
  user code; the real `match`/`case` dispatch is the trustworthy signal**."

## The contradiction at the centre of the campaign

DISC2 — the update that pinned the root cause as struct-name shadowing and
triggered every rename since — reached that conclusion by *"instrumenting
directly inside `SymbolTable.define` with temporary
`print(rt_enum_discriminant(...))`"*. That is the diagnostic the same document
declares unreliable in control #3.

So the causal claim rests on a signal the doc itself distrusts, while the doc's
own control #1 argues the proposed mechanism is not triggerable.

## What is still solid

The **symptom** is real and independently attested: DISC1's live repro reports
`fn_matched=false` / `mod_matched=false` — real `match`/`case` dispatch failures,
not just the suspect extern — for symbols inside the genuine
`HirLowering`/`SymbolTable` call graph. Something in that machinery does fail to
match. That part is not in doubt.

What is in doubt is **why**, and therefore whether renaming structs fixes it.

## Verdict

**Mechanism is different than believed, or at minimum unproven.** Not "cannot
reproduce" — the defect reproduces fine in situ; it is the *struct-shadowing
explanation* that no probe supports and one documented control contradicts.

## Implications for the landed renames

They are **not** retracted, and should not be: the diff-purity audits were clean,
no behaviour regressed, and the flat name-keyed registry is a genuine latent
hazard worth removing. But they must stop being described as *fixes for a
confirmed root cause*. The honest framing is **defensive hygiene against a
structurally real hazard whose triggering conditions are unknown**.

Anything downstream that claims "PTR1/PTR2 fixed the dead arms" is overstated —
including the claim that `is_static_method_call` was dead, which was derived by
source reading plus this mechanism, never by observing the predicate return the
wrong answer.

## Next step

Instrument inside the real `HirLowering`/`SymbolTable` call graph using **real
`match`/`case` dispatch as the signal** — never `rt_enum_discriminant` from user
code — and bisect what actually makes `fn_matched` false. Until that lands, treat
the mechanism as open.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN (cited line accurate)

The registry is still keyed on a BARE name with no module qualifier —
`src/compiler/10.frontend/core/types.spl:733`:

```spl
fn named_type_register(name: text, field_names: [text], field_types: [i64]) -> i64:
    val existing = named_type_find(name)
    if existing >= 0:
        ...
        return existing
```

Backing storage is flat parallel arrays (`var named_type_names: [text]`), so two
modules declaring the same type name resolve to one entry.
ROOT-CAUSE FAMILY: flat bare-name registries (see also
duplicate_type_name_collision_audit_2026-07-17,
diag_stage_facet_cross_module_collision_under_test_2026-07-06).
