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

The wire rows are the ABI types in `runtime_mcdc_v1.h`:

- events: `SimpleMcdcVectorV1` (64 bytes);
- exclusions: `SimpleMcdcExclusionV1` (184 bytes), sorted by source digest then
  decision ID, with one condition mask per decision;
- report: `SimpleMcdcReportV1` (152 bytes).

Every workspace is allocated before the allocation-free report boundary. The
defaults cap events at 65,536 rows (4 MiB), manifests at 64 KiB, programs at
128 KiB, Boolean tokens at 512 KiB, and witnesses at 3.5 MiB. Use the explicit
`--max-*` flags to reduce mission-specific memory or admit a larger known
manifest; hard ceilings remain enforced. Capacity exhaustion, malformed rows,
proof-budget exhaustion, stale exclusions, an empty denominator, and incomplete
normal-mode coverage all fail closed with a nonzero exit.

Alpha and Beta are migration/reporting modes: incomplete evidence renders
`report=WARN gate=NOT_ENFORCED` and never renders PASS. Normal is the only mode
that renders `gate=PASS`, after both evidence and exclusion audit succeed.

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
