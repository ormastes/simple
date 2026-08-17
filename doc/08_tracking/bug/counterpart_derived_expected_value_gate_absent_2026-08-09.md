# Counterpart: the "converter derives expected value from candidate output" gate does not exist

- **Date:** 2026-08-09
- **Lane:** F9 (foundation red-team), Counterpart Conformance Wave 1
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** High. This is the gate that separates a differential test from a tautology.

## What the design requires

`doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`
§6.3 (Fail-closed routing) lists, as its final clause, that the framework must
reject "a converter deriving expected values from candidate output".

## What is implemented

Nothing. A repo-wide search of the landed foundation
(`src/lib/common/spec/evidence/counterpart/**`,
`src/lib/nogc_sync_mut/spec/evidence/counterpart/**`) finds no notion of
derivation-from-candidate anywhere:

- `src/lib/nogc_sync_mut/spec/evidence/counterpart/converter_registry.spl:115`
  `converter_manifest_rejections()` checks id, version, both schema versions,
  self-loop and determinism — nothing about where the expected value came from.
- `src/lib/nogc_sync_mut/spec/evidence/counterpart/converter_graph.spl:295`
  `resolve_route()` implements every OTHER §6.3 clause
  (`missing_schema_version`, `provider_schema_mismatch`, `zero_items`,
  `missing_input_hash`, `cycle`, `ambiguous_route`,
  `required_dimension_dropped`, `undeclared_default`,
  `exact_relation_through_lossy_route`) — and not this one.
- `ConverterManifest.preconditions`
  (`src/lib/common/spec/evidence/counterpart/model.spl:348`) is the only field
  that could carry such a declaration, and no code reads it for this purpose.

The only related text in the tree is a comment claiming innocence rather than
enforcing it: `src/lib/nogc_sync_mut/spec/evidence/counterpart/matrix_compare.spl:111`
("This is a stated projection, not a derived expected value").

## Reproduction

`test/02_integration/infra/counterpart/foundation_redteam_spec.spl`, scenario
"refuses a converter that derives its expected value from the candidate output".
It registers a converter whose manifest openly declares
`preconditions: ["derives_expected_from:candidate_output"]` and asserts the
registry refuses it.

Measured: `declared>=21 executed=21 passed=20 failed=1 dropped=0`, exit 1. The
single failure is this scenario. Every other acceptance-gate scenario in the
suite passes.

## Why this matters

A converter that computes the reference side from the candidate side makes every
downstream relation trivially true. The failure mode is total and silent: the
matrix goes green, `counterpart.comparisons.failed=0` projects into
CanonicalEvidence, and the generated manual reports agreement that was
manufactured, not observed. None of the other gates can catch it — the route is
short, deterministic, loss-free and unambiguous, which is exactly what makes it
pass every existing check.

## Unblock condition

Either (a) add a declared, enforced provenance field to `ConverterManifest`
(e.g. `expected_value_origin: reference | candidate | independent`) and reject
`candidate` in `converter_manifest_rejections()`, or (b) an equivalent check in
`resolve_route()` with a `derived_from_candidate` rejection code. Once landed,
the scenario above turns green with no change to its assertion. Do NOT weaken
the assertion to close this record.

## Resolution (2026-08-09, lane F5/F6)

Unblock option (b) was taken, and then hardened with (a)-style declared
provenance expressed through the existing frozen `preconditions` field, so the
Wave-0 contract in `src/lib/common/spec/evidence/counterpart/model.spl` did not
have to be reopened.

A precondition of the form `derives_expected_from:<source>` now declares where a
converter obtains an expected value. Naming the candidate there is refused:

- `src/lib/nogc_sync_mut/spec/evidence/counterpart/converter_registry.spl`
  — `precondition_derives_from_candidate()` and
  `manifest_derives_expected_from_candidate()`; `converter_manifest_rejections()`
  refuses such a manifest, so it never enters the graph. The match is on the
  token `candidate`, not the exact spelling `candidate_output`, so renaming the
  source (`candidate_under_test.stdout`) cannot walk around the gate. An honest
  upstream source (`derives_expected_from:normative_vector_file`) is unaffected.
- `src/lib/nogc_sync_mut/spec/evidence/counterpart/converter_graph.spl`
  — `resolve_route()` additionally refuses any chosen route containing such an
  edge, with rejection code `derived_expected_value`. This is defense in depth:
  reaching it means an edge entered the graph without passing registration.

**Verification.** The red-team scenario passes with its assertion untouched:
`test/02_integration/infra/counterpart/foundation_redteam_spec.spl`
→ `declared>=21 executed=21 passed=21 failed=0 dropped=0`, exit 0
(was 20/21, exit 1).

**Sabotage probes**, each broken → RED → reverted → GREEN:

| guard | sabotaged | restored |
|---|---|---|
| registry refusal (`converter_manifest_rejections`) | redteam 21 exec / 20 pass / **1 fail**; unit 19 / 18 / **1** | 21/21/0 and 19/19/0 |
| route-level refusal (`resolve_route`) | unit 19 exec / 18 pass / **1 fail** | 19/19/0 |

Breaking the registry guard reproduces exactly the 20/21 F9 originally
measured, which confirms the probe reaches the reported defect and not a
neighbouring one.
