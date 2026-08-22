# MC/DC report and normal-mode gate

The authoritative command is `simple coverage mcdc`. It consumes the compiler's
MCDP V1 Boolean manifest, sealed 64-byte runtime vector rows, and optional
governed exclusion rows. It sorts process receipts by stable decision identity,
owner, and sequence; runs unique-cause then validated masking analysis; joins
condition exclusions; and emits one deterministic SHA-256 provenance receipt.

```text
simple coverage mcdc \
  --manifest build/test.mcdp \
  --events build/test.mcdc-events \
  --exclusions build/test.mcdc-exclusions \
  --exclusion-source test/flight_irq_spec.spl \
  --mode normal --current-epoch 1787356800
```

Normal mode exits successfully only when the eligible denominator is nonempty,
every eligible condition has a retained independence witness, every binary
exclusion matches a manifest decision and fresh capability-unavailable reason,
and every author directive passes the scenario-exclusion audit. Accepted source
directives render as `EXCLUDED`; they never render as PASS or covered. Directive
counts are audit facts and are not substituted for excluded-condition counts.

The wire rows are the ABI types in `runtime_mcdc_v1.h`. V1 remains compatible;
new complete reports use the additive V2 surface:

- events: `SimpleMcdcVectorV1` (64 bytes);
- exclusions: `SimpleMcdcExclusionV1` (376 bytes), sorted by source digest then
  decision ID, with one condition mask per decision;
- report: `SimpleMcdcReportV1` (152 bytes).
- source locations: `SimpleMcdcSourceLocationV2` (32 bytes), exact manifest
  order, with stable file digest, line, and column;
- decision report: `SimpleMcdcDecisionReportV2` (208 bytes);
- complete report: `SimpleMcdcReportV2` (256 bytes).

`rt_mcdc_report_mcdp_v2` requires the independently measured lowercase SHA-256
of the executable binary (the manifest identity is not mislabeled as binary
identity) and emits gross/eligible/excluded/covered/uncovered totals
for both decisions and conditions, the exact witnessed-pair count, report mode,
binary identity, explicit source spans, and process provenance. All output and
workspace storage is caller-owned. It performs no heap allocation.

For cross-process coverage, concatenate complete per-process decision rows and
sort once by `(source_digest, decision_id, process_id, process_sequence)`.
`rt_mcdc_merge_reports_v2` then merges the rows in one deterministic O(N) pass.
Every decision must contain the same ordered process set. Duplicate process
contributions, omitted rows, mixed identities/modes/locations/exclusions, and
changed rows whose digest was not updated fail closed. Output is a fixed
caller-owned decision array; insufficient capacity also fails closed.

Every workspace is allocated before the allocation-free report boundary. The
defaults cap events at 65,536 rows (4 MiB), manifests at 64 KiB, programs at
128 KiB, Boolean tokens at 512 KiB, and witnesses at 3.5 MiB. Use the explicit
`--max-*` flags to reduce mission-specific memory or admit a larger known
manifest; hard ceilings remain enforced. Capacity exhaustion, malformed rows,
proof-budget exhaustion, stale exclusions, an empty denominator, and incomplete
normal-mode coverage all fail closed with a nonzero exit.

Normal, Alpha, and Beta production reports all enforce exact eligible MC/DC.
Diagnostic display may render warnings, but it does not invoke either
production report gate and cannot be promoted.

The provenance digest binds the compiler manifest identity, report mode and
freshness epoch, canonical owner/sequence event order, accepted binary
exclusions, and selected masking witnesses. It is stable under input-event
permutation and changes when evidence or governance inputs change.

Focused native evidence lives in
`src/runtime/test/runtime_mcdc_manifest_bridge_selfcheck.c`; it exercises PASS,
deliberate-red incomplete coverage, alpha reporting, fresh/stale exclusions,
empty-denominator rejection, permutation-stable provenance, allocation count,
runtime, and fixed workspace size. The Simple integration spec joins the
author-facing directive audit to the exact normal gate.
