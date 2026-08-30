<!-- codex-architecture -->
# Evidence Showcase Architecture — TLDR

## Purpose

Bind every critical root `EVIDENCE_SHOWCASE.md` claim to modern SSpec, a
generated manual, a verified receipt/manifest, and retained artifacts or an
explicit blocker.

## Decision

Reuse current owners:

```text
existing producer/artifact
  -> SSpec runner writes one ScenarioEvidenceManifest
  -> focused docgen renders the manual
  -> showcase generation resolves curated critical rows
```

- Preserve `ScenarioEvidenceArtifact` and `EvidenceReceipt`.
- Add a composed, versioned `ScenarioEvidenceManifest`.
- Add typed text, motion, and protocol evidence records.
- Do not build the proposed runtime capture registry in this lane.
- Root showcase truth is generated; prose and grouping remain curated.

## Critical paths

- Contract: `src/lib/nogc_sync_mut/spec/scenario_evidence_manifest.spl`
- Typed records: `src/lib/common/spec/scenario_*_evidence.spl`
- Existing artifact/helpers:
  `src/lib/common/spec/{scenario_evidence,scenario_helpers}.spl`
- Receipt adapter: `src/lib/nogc_sync_mut/spec/evidence_receipt.spl`
- Runner persistence: canonical SSpec runner
- Rendering:
  `src/app/spipe_docgen/spipe_docgen/{parser,generator,main}.spl`
- Inventory: `config/evidence_showcase.sdn`
- Entry points: `EVIDENCE_SHOWCASE.md`, `README.md`, `FILE.md`

## Performance and invalidation

- No production startup or request-path work.
- Focused docgen reads one deterministic manifest.
- Showcase generation scans only the curated inventory once.
- Invalidate on schema/source/producer/target/artifact digest changes, not mtime
  alone.

## Truth boundary

Statuses are `live-pass`, `historical-pass`, `contract-only`, `blocked`,
`unsupported`, or `planned`. Missing, stale, mocked, fallback, QEMU-only, or
source-only evidence cannot be promoted beyond its proven scope.

## Next documents

- `doc/05_design/evidence_showcase.md`
- `doc/03_plan/sys_test/evidence_showcase.md`
- `doc/03_plan/agent_tasks/evidence_showcase.md`
