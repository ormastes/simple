# Untyped-Evidence Migration Design

**Date:** 2026-08-08
**Status:** Design — not yet implemented
**Depends on:** `src/lib/common/spec/evidence/legacy_facade.spl` (landed), the typed-evidence
contract (`model.spl`, `evidence_comparator.spl`, landed)
**Motivates:** `doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md` E8 remainder

## 1. Why this is a separate lane

The `legacy_facade.spl` migration proved out and then exhausted itself against one specific
migration surface: specs that already call `scenario_evidence_artifact` /
`scenario_checker_evidence` from `std.common.spec.scenario_helpers` / `scenario_evidence`. A
full-repo search found exactly four such specs, and all four are now migrated
(`doc/07_guide/infra/sspec_legacy_migration.md`).

That search also surfaced the actual remaining problem: most existing specs in this repo do
**not** use `ScenarioEvidenceArtifact` at all. They assert on raw output some other way —
`print()` statements read back from a captured buffer, `to_contain()` substring checks against
constructed strings, or nothing beyond `assert_true`/`expect(...).to_equal(...)` on values
computed inline. There is no artifact to convert, because none was ever built. `legacy_facade`
has nothing to adapt in these specs — there is no `ScenarioEvidenceArtifact` object to hand it.

This is therefore not a continuation of the facade work. It needs its own adapter surface, and
a design decision about what "migrating" even means when there was never a typed capture to
begin with.

## 2. What "untyped evidence" looks like in this repo

Three distinct shapes, found by inspection, each needing a different adapter:

1. **Substring assertions on a captured value.** `expect(output).to_contain("expected text")`
   where `output` came from a real capture (process stdout, rendered text) but was never
   wrapped in `ScenarioEvidenceArtifact`. This is the closest to already being typed evidence —
   it has a real captured value, just no metadata envelope around it.
2. **Structural assertions with no capture at all.** `expect(result.field).to_equal(value)` on
   an in-memory value the spec computed directly. There is no "evidence" here in the typed-
   evidence sense — the spec is asserting on program state, not on an observation of a running
   system. These specs are **out of scope** for this migration; typed evidence is for
   observations, and forcing a fabricated `CanonicalEvidence` wrapper around a plain value
   comparison would violate the "expected values may not be derived from the actual observation
   under test" rule for no benefit.
3. **Print-and-eyeball output.** A spec prints something for a human to read in CI logs, with no
   machine assertion on it at all. This is worse than untyped evidence — it is unverified
   evidence. These need real assertions added before they need typed-evidence conversion; that
   is a correctness fix, not a migration, and should be tracked and executed separately from
   this lane (it is the `SSDOC-ORA-001` finding class from `sspec-maintain scan`, already
   covered by existing tooling — do not duplicate it here).

**Only category 1 is this lane's scope.**

## 3. Proposed adapter

```simple
# src/lib/common/spec/evidence/untyped_capture.spl  (proposed, not yet built)

pub struct UntypedCapture:
    label: text
    raw_value: text
    source_kind: text   # "stdout" | "rendered_text" | "log_line" | ...

pub fn untyped_capture_to_canonical(capture: UntypedCapture, profile_id: text) -> CanonicalEvidence
```

Unlike `legacy_evidence_to_canonical`, there is no old struct to convert losslessly — the
adapter's only job is to wrap an already-captured raw value into one `EvidenceNode` at path
`"value"`, tagged with `source_kind` so a reader can tell an untyped migration from a fully
typed one in the generated manual. This is deliberately minimal: it does not attempt to infer
structure from the raw text (that is what the format adapters — `text_protocol`, `json_document`
— are for, when the raw text actually has that structure). A spec whose captured value has real
structure should go through those adapters directly, not through `untyped_capture` first.

## 4. Migration rule, not a mechanical sweep

Because category-1 specs require a human (or an agent under review) to look at each `to_contain`
call and decide whether it is (a) actually observing a live system and worth converting, or (b)
better left as-is because the substring check is already sufficient and a typed wrapper adds
nothing, this cannot be a scripted repo-wide sweep the way the facade migration was close to
being. The rule for each candidate:

- Convert if the spec's assertion is checking something a `check_full_pattern` /
  `check_exact` / `check_multiset` would express more precisely than substring containment
  (e.g. an exact status code embedded in free text, a field that could legitimately repeat).
- Leave alone if the substring check is already the correct level of precision and a typed
  wrapper would only add ceremony — matches the anti-pattern guide's existing "don't over-
  engineer" stance.
- Never touch a spec in category 2 or 3 under this lane.

## 5. Acceptance for a future implementation pass

- One adapter module (`untyped_capture.spl`), one spec, sabotage/revert proof, following the
  same pattern as every other landed adapter this session.
- A small number of REAL migrated specs (expect single digits, based on the facade lane's
  actual corpus size) — not a claimed full-repo sweep, because the category-1/2/3 triage above
  requires per-spec judgment that does not scale to automated batch conversion.
- The migration guide (`doc/07_guide/infra/sspec_legacy_migration.md`) gets a second section
  covering this adapter, cross-referencing this design doc for the triage rule.

## 6. What this design deliberately does not do

It does not propose retrofitting typed evidence onto category-2 (pure in-memory value
comparison) specs, and it does not propose auto-generating assertions for category-3
(print-only) specs. Both would be scope creep beyond "migrate existing evidence onto the typed
model" into "rewrite existing test logic," which is a different, much larger, and much riskier
undertaking than this plan lane was ever scoped to cover.
