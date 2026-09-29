# MC/DC Report and Exact Normal-Mode Gate

Purpose: verify exact eligible-denominator accounting and governed exclusions. Audience: coverage report operators and release reviewers.

Source: `test/03_system/compiler/mcdc_report_gate_spec.spl`  
Evidence class: executable source contract  
Current execution status: **PENDING/BLOCKED** — no admitted self-hosted compiler is available; this hand-maintained mirror is not a generated PASS receipt.

## Preconditions

The report input must bind stable decision identities, validated independence witnesses, binary identity, and deterministic merge provenance. Empty eligible denominators are invalid.

## Operator workflow

1. Run the selected assurance mode.
2. Capture the durable report receipt.
3. Compare gross, excluded, eligible, covered, and uncovered totals.
4. Inject incomplete coverage or invalid exclusion metadata.
5. Verify the normal gate fails closed.

## Scenarios

- Exact eligible coverage with fully governed exclusions is admitted.
- Below-100 coverage and empty eligible denominators are rejected.
- Unvalidated or unexplained exclusions reject the gate.
- A complete fresh reason-bearing exclusion is labeled `EXCLUDED`, never PASS.
- Blank/generic, malformed, and stale exclusions are rejected.

## Acceptance boundary

These scenarios validate production accounting and exclusion parsers. Full REQ-003/004 runtime acceptance still requires collected vectors, verifier-bound witnesses, source locations, binary identity, and merge receipts from an admitted executable.

## Traceability

REQ-003, REQ-004, REQ-005, REQ-018; NFR-008 and NFR-009.

## Executable source

The complete executable source remains in `test/03_system/compiler/mcdc_report_gate_spec.spl`.
