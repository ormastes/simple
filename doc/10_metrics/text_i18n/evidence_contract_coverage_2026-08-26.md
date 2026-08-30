# Text/i18n evidence-contract verification — 2026-08-26

The 30-owner/10-backend coverage manifest suite passes 3/3. It rejects absent
paths, duplicate IDs/paths, invalid owner classifications, incomplete backend
sets, duplicate backend IDs, optional mandatory rows, and unknown evidence
classes. This verifies manifest structure, not owner branch coverage.

The 18-row performance/memory contract suite passes 7/7. It validates timing,
provenance, allocation, transient/retained/RSS/catalog/atlas/VRAM fields,
device-origin evidence, result identity, matched-baseline regressions, and the
new whole-matrix rule. The matrix rejects missing, duplicate, unknown, and
invalid receipts and accepts exactly one valid receipt per required row.

These tests use synthetic receipts and therefore prove only the fail-closed
contract. No synthetic value is an admissible throughput, allocation, RSS, or
GPU measurement. Release remains open until real receipts pass the same matrix
check on controlled native hosts.
