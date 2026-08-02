# SSpec Documentization Maintenance

`simple sspec-maintain` is the maintenance-level quality tool for executable
SSpec and its generated/manual documentation. It complements lint and
duplicate-check by explaining whether a scenario can produce a professional,
traceable operator manual.

## Scan and scoring

```text
simple sspec-maintain scan test/path/feature_spec.spl
simple sspec-maintain scan test/path/feature_spec.spl --format json --min-score 80
simple sspec-maintain scan test/path/feature_spec.spl --format sarif
```

The deterministic score has seven dimensions: narrative (15%), structure
(15%), oracle quality (20%), traceability (15%), evidence (15%), coverage
(10%), and maintainability (10%). Any blocker caps the effective aggregate at
49. Findings use stable `SSDOC-*` identities and content-derived fingerprints.
Existing `SPIPE001..007` identities remain owned by lint and are not redefined.
JSON and SARIF stdout are serialization-only.

## Improving with confirmation

`simple sspec-maintain improve <spec>` previews deterministic,
semantic-preserving edits. Only explicit `--apply` writes. Apply retains
rollback material, uses an atomic write, reparses, rejects stale/overlapping
edits, and is idempotent. Assertions, REQ mappings, captures, and authored
claims always require human judgment. Optional LLM suggestions are advisory
previews, excluded from scoring, and never self-apply.

## Reference specification to modern SSpec

`simple sspec-maintain scaffold reference.md --output feature_spec.spl` records
the reference SHA-256 and preserves explicit REQ IDs. Where an oracle cannot be
derived without invention, it emits:

```simple
fail("TODO: replace generated placeholder with an executable assertion")
```

Never turn ambiguity into a skip, tautology, or fabricated expected value. Use
literal `step("...")` calls; bare `@step "..."` is invalid current syntax.

## Professional documentization

`simple sspec-maintain documentize <spec> --output <manual.md>` supplies a
scorecard and provenance. A professional manual includes Purpose and audience,
Preconditions, Operator workflow, Scenario narratives, Scorecard, Findings and
remediation, Evidence and provenance, and Compatibility and limitations. SPipe
remains the canonical owner of the complete scenario manual.

Cache identities include source, mirror, rule, configuration, and tool hashes.
Changes to any identity invalidate the relevant entry. Performance evidence uses
warm in-process measurements and records scan counts, cache disposition, phase
timings, and RSS.

## Verification sequence

Run focused tests, lint, duplicate-check, and `sspec-maintain scan` once. Review
the manual and machine outputs, then stop when the gates pass.
