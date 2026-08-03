# SSpec Documentization Maintenance

`simple sspec-maintain` is the maintenance-level quality tool for executable
SSpec and its mirrored SPipe manual. Use it beside `simple lint` and
`simple duplicate-check`: lint checks correctness and style, duplicate-check
checks repeated implementation, and `sspec-maintain` checks whether executable
scenarios form a traceable, useful specification document.

SPipe remains the canonical parser and full-manual generator. The maintenance
tool analyzes that source/manual pair, explains quality, previews safe cleanup,
and scaffolds reviewable SSpec from a reference document. It must not invent
requirements, outcomes, evidence, or passing assertions.

LLM/MCP clients should use read-only `simple_sspec_scan` for scoring. The
conservative `simple_sspec_maintain` tool includes write-capable operations and
therefore requires mutation approval even when its selected operation is scan.

## Routine maintenance workflow

For a changed SSpec/manual pair:

1. Generate or refresh the canonical manual with `spipe-docgen` or
   `sspec-maintain documentize`.
2. Run `simple sspec-maintain scan <spec>` and inspect every score and finding.
3. Fix authored or behavioral findings manually.
4. Use `improve` only to preview safe mechanical edits.
5. Apply an exact reviewed patch explicitly, retain rollback material, then
   rerun the focused SSpec, lint, duplicate-check, and scan once.
6. Read the mirrored Markdown as an operator manual before verification.

Do not chase only the aggregate. A high average cannot compensate for a weak
oracle or a blocker.

## Scan scope and policy

The current command accepts one `*_spec.spl` file or a directory. Directory
scans walk once, include matching specs, and sort paths deterministically.

```text
simple sspec-maintain scan test/path/feature_spec.spl
simple sspec-maintain scan test/03_system/app/example --format json
simple sspec-maintain scan test/path/feature_spec.spl --min-score 80
simple sspec-maintain scan test/path/feature_spec.spl --deny-severity warning
simple sspec-maintain scan test/path/feature_spec.spl --format sarif
simple sspec-maintain scan test/path/feature_spec.spl --baseline reviewed.txt \
  --suppressions reviewed-suppressions.txt --debug-timings
```

`--min-score` and `--deny-severity` are independent failure policies. Human
output is for review. JSON and SARIF stdout must contain only the selected
serialization. An empty directory scope, unreadable source, or invalid format
is an operational failure; do not reinterpret it as a clean scan.

The tool derives the mirror by replacing `test/` with `doc/06_spec/` and `.spl`
with `.md`. A missing or stale mirror is incomplete evidence even when the
source-only score is otherwise high.

## Reading the seven scores

| Dimension | Weight | Review question |
|---|---:|---|
| Narrative clarity | 15% | Does the document state purpose, audience, and meaningful context? |
| Behavioral structure | 15% | Do scenarios and ordered steps form a readable workflow? |
| Oracle strength | 20% | Do assertions observe the promised behavior instead of tautologies or source text? |
| Requirement traceability | 15% | Does each scenario bind to a selected, stable requirement identity? |
| Evidence completeness | 15% | Are relevant actions, outcomes, captures, and environment facts visible? |
| Behavioral coverage | 10% | Are boundaries, failures, recovery, unsupported cases, and ambiguity disposition covered? |
| Maintainability | 10% | Are helpers, folding, compatibility, and limitations clear and non-duplicated? |

Scores are deterministic 0–100 values. The weighted aggregate is diagnostic;
every deduction must remain visible. Any blocker caps the aggregate at 49.
Placeholder passes, an absent real oracle, invented expected values, and
unconditional passing scaffolds are blockers regardless of other strengths.

Findings use stable `SSDOC-*` rule IDs and content-derived fingerprints.
`SPIPE001..007` remain owned by the existing lint rules and are referenced, not
renamed or duplicated.

## Baselines and suppressions

Baseline comparison classifies stable fingerprints as `new`, `unchanged`, or
`resolved`. Ratchet policy should fail newly introduced findings or configured
score regressions without forcing unrelated legacy cleanup into every change.
Whitespace or unrelated line movement should not manufacture a new identity.

A suppression is acceptable only when it names the rule ID, owner, reason, and
optional finding fingerprint. Pass the reviewed file with `--suppressions`; its
records are `RULE_ID|owner|reason|optional-fingerprint`. Blockers cannot be
suppressed. Pass a sorted fingerprint ledger with `--baseline` to classify
active findings as `new`/`unchanged` and absent prior findings as `resolved`.

## Preview and apply safety

`simple sspec-maintain improve <spec>` is preview-only. It may propose only
mechanical edits represented by EasyFix metadata.

```text
simple sspec-maintain improve test/path/feature_spec.spl
simple sspec-maintain improve test/path/feature_spec.spl --apply \
  --rollback build/test-artifacts/feature_spec.rollback
```

Only explicit `--apply` writes. Review the exact preview first. Assertion
meaning, requirement mapping, scenario outcome, capture claims, and authored
narrative require human judgment and are not safe automatic rewrites. Optional
LLM advice follows the same rule: source-evidenced, nondeterministic,
preview-only, excluded from scoring, and never self-applied.

The apply path conflict-checks EasyFix spans, rejects stale source bytes,
validates the proposed SSpec in an isolated file before replacement, writes
rollback material, and atomically replaces the source while the atomic-write
owner preserves its mode. The certain edits normalize the exact `std.spipe`
alias and unsupported bare `@step` metadata; they never insert authored prose.
Applying the same set again is a no-op. On verification failure, keep the
diagnostic and rollback path and do not call the edit accepted.

## Reference specification scaffolding

```text
simple sspec-maintain scaffold reference.md --output test/path/feature_spec.spl --preview
simple sspec-maintain scaffold reference.md --output test/path/feature_spec.spl --apply
```

The scaffold records the source path and SHA-256, preserves explicit REQ IDs,
uses `use std.spec.*`, outcome-oriented scenarios, and literal `step("...")`
calls. Every unresolved oracle must remain executable and fail fast:

```simple
fail("TODO: replace generated placeholder with an executable assertion")
```

Never convert ambiguity into `skip`, a tautology, or a fabricated value. Treat
the scaffold as traceable intake, not conformance evidence. Replace every
placeholder with a production-observing oracle and regenerate/review the manual
before marking its requirement implemented.

For full external standards, follow the lossless `spec-to-spipe` architecture
in `doc/01_research/domain/spec_to_spipe_toolchain.md`. Its compatibility name
is `spec-to-sspec`, but both names share one implementation. That pipeline adds
source snapshots, byte dispositions, semantic adapters, and conformance
ledgers; `sspec-maintain scaffold` is the bounded Markdown intake path, not a
replacement for lossless import. Both must emit the same modern SSpec shape:
authored manual facts, outcome scenarios, literal steps, stable requirement
bindings, retained evidence, and fail-fast unresolved oracles.

## Canonical documentization and manual review

```text
simple sspec-maintain documentize test/path/feature_spec.spl
simple sspec-maintain documentize test/path/feature_spec.spl --output doc/06_spec/path/feature_spec.md
```

`documentize` calls the canonical SPipe generator and appends the maintenance
scorecard/provenance section. It does not own a parallel scenario renderer.
A professional manual contains:

1. purpose, audience, scope, and freshness;
2. preconditions and assumptions;
3. primary operator workflows with ordered steps;
4. scenario narratives and requirement-to-test traceability;
5. outcomes, typed captures, environment, and provenance;
6. pending, unsupported, recovery, ambiguity, and troubleshooting guidance;
7. scorecard plus findings/remediation when requested; and
8. compatibility, limitations, source hash, and generator identity.

Review what is visible, not merely what exists in the `.spl`. Primary flows
should remain open; reusable setup can use `@inline` and `@prev`; edge, matrix,
and stress detail should be folded; internal plumbing can be skipped from the
manual while remaining executable. Executable SSpec is folded detail and must
not dominate the reader-facing flow. See
`doc/07_guide/infra/sspec_scenario_manual.md`.

## Failure policy and traceability

- A blocker or configured score/severity policy failure blocks the lane.
- A missing/stale/structurally incomplete mirror is a finding and blocks when
  the configured score/severity policy selects it for documentation acceptance.
- Machine-output contamination blocks CI consumption.
- A scaffold placeholder is expected to fail and cannot count as coverage.
- A suppression without rule, owner, reason, and bounded scope is invalid.
- An unsupported host or product feature remains visible as blocked or
  unsupported; it is not silently removed from requirement accounting.
- Every `REQ-SSDOC-*` claim must map to implementation and executable evidence.
  Source-text checks may prove synchronization, but not runtime behavior.

The system manual at
`doc/06_spec/03_system/app/testing/feature/sspec_documentization_maintenance_spec.md`
shows the library-level operator contract. Unit and integration suites remain
authoritative for CLI exits, serialization purity, directory handling, atomic
file behavior, and malformed inputs.

## LLM-assisted improvement policy

An LLM may explain a finding, suggest manual wording, or draft an exact patch.
It must cite the finding and source span, distinguish fact from inference, and
show the patch for confirmation. It cannot change the deterministic score,
approve its own semantic rewrite, invent an oracle, suppress a blocker, or
apply without the same explicit confirmation and rollback policy as any other
caller.
