# MCI-v2 Unified Tooling Producer

`scripts/check/check-mci-v2-tooling-admission.shs` is the sole producer for the
aggregate `tooling` row. It owns one exact, ordered 17-row child manifest:
compiler, library, MCP, and LSP checks; bootstrap essential, portability, and
seed/native parity; lint, duplication, and whole tests; direct-environment
working and staged guards; runtime-contract and current-artifact execution; and
warm CLI, MCP, and LSP latency/RSS evidence. Missing, duplicate, unexpected,
skipped, malformed, failed, timed-out, oversized, or hash-invalid rows block the
whole manifest. No child can become a second top-level aggregate receipt.
Each lowercase row binds command and fixture hashes, separate stdout/stderr
hashes and byte counts (16 MiB maximum per stream), start/end/duration, exit and
timeout state, and an explicit per-row scan policy. The 17 owned commands do not
publish a common enumeration counter, so each row records
`scan_policy=<id>|not-applicable|command-contract-v1` rather than fabricating a
scan count. MCP and LSP warm measurements are distinct commands and distinct
rows.

`--evidence` is always the aggregate evidence root (for example,
`build/evidence/mci-v2`), never a `tooling/` child directory.

Live mode requires a clean repository whose SHA-256 of Git's stable recursive
`HEAD` tree listing equals `--source-hash`, plus a regular executable resolved beneath
`bin/release/*/simple`. Its digest must match the adjacent admission sidecar and
its identity must not identify a Rust/bootstrap seed. Every command and bounded
raw log is hashed. Warm CLI, MCP, and LSP startup/request samples are normalized
into three canonical raw sample members. The producer recomputes sample count,
p50, p95, p99, and maximum RSS from those members during admission; each warm
ID requires an explicit p95/RSS baseline and both dimensions must stay within
5%. All 17 real commands must pass with zero skips before the producer packages
the manifest and every raw stream into one deterministic,
self-contained `tooling-generation-v1.tar`, then uses the repository secure
no-follow, fsyncing, atomic-no-replace publisher to write it and
`receipts/tooling.unsigned.template`.
Live warm commands receive those baselines through the operator-supplied
`MCI_TOOLING_WARM_CLI_BASELINE_*`, `MCI_TOOLING_WARM_MCP_BASELINE_*`, and
`MCI_TOOLING_WARM_LSP_BASELINE_*` variables; an absent or zero baseline blocks.

The exact aggregate-root layout is `receipts/tooling.unsigned.template` and
`artifacts/tooling-generation-v1.tar`; this matches the plan and aggregate and
adds no unbound marker. Both paths are collision-preflighted. The exact lowercase
canonical `mci-lane-receipt-v1` unsigned template publishes first and is never
admissible; the fully built, self-contained, hash-bound tar publishes last.
The bounded runner continuously drains both process streams, records total and
retained byte counts, and blocks the row if even one byte is discarded beyond
the 16 MiB retention boundary.

The template is deliberately unsigned. An external key custodian replaces the
lowercase attestation, key-ID, and receipt-hash placeholders, canonicalizes in
the aggregate field order, creates `signatures/tooling.sig`, and publishes
`receipts/tooling.receipt` only after independently verifying the final tar hash.
Signing transforms the root `receipts/tooling.unsigned.template` in place into
root `receipts/tooling.receipt` plus `signatures/tooling.sig`; the signer does
not move or rename `artifacts/tooling-generation-v1.tar`.
This producer never accepts or handles a private key and never claims that its
template is aggregate-admissible.
Use the canonical external signing procedure in
[`mci_v2_lane_signer.md`](mci_v2_lane_signer.md); producer-specific ad hoc
receipt rewriting is not supported.

Controlled fixture mode requires `MCI_TOOLING_CONTROLLED_FIXTURE=1` and
`--fixture-manifest`. It checks the schema, identities, exact row set, bounded
metadata, status vocabulary, and fail-closed behavior only. Its report always
says `contract-only` and `blocked`, and it removes both the signed-receipt name
and unsigned live template. Run its focused contract with:

The aggregate and external signer revalidate exact child IDs, command budgets,
scan-policy rows, warm metric vocabulary, baseline rows, raw member paths, and
raw SHA-256 bindings; row cardinality alone is not admission. The negative
contract matrix rejects missing, duplicate, or unexpected rows,
uppercase/skip-like status, bad hashes or paths, unavailable commands, nonzero
exits, timeouts, overflow metadata, regressions above 5%, unauthorized fixtures,
collisions, and incomplete transaction state. A failed child publishes no
generation, receipt template, or completion marker.

```sh
sh test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs
```
