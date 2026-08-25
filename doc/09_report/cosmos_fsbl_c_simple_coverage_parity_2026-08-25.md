# Cosmos FSBL C / Pure-Simple coverage parity — 2026-08-25

## Current status

**Evidence pending.** The parity infrastructure is implemented, but this update
was intentionally not executed or verified. It does not contain or imply a new
PASS receipt. The authoritative result becomes available only when the producer
finishes and the independent structural checker accepts its retained receipt.

The earlier development run reported 14/14 input-reachable C arcs and seven
passing semantic vectors, but its raw artifacts were not retained and its
Pure-Simple run used a Rust bootstrap seed. Those observations are historical
diagnostics only and are not admissible coverage evidence.

## Shared semantic input

`test/fixtures/os/cosmos/fsbl_handoff_vectors.tsv` is the single canonical
decimal TSV consumed by both:

- `test/02_integration/os/cosmos/cosmos_hal_mmio_test.c`
- `test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl`

Its seven rows contain one all-good handoff and six rows that independently
make SLCR lock, ARM clock, DDR clock, PS primary reset, A9 CPU0 reset, or
DEVCFG PCFG_DONE invalid. The final column is the Boolean expected result.
There are no copied language-specific vector tables.

The C and Pure-Simple decision cores evaluate the same six predicates as
ordered scalar fail-closed guards. This retains the original short-circuit
order while making each condition outcome directly attributable. Both hot
paths remain O(1), use scalar register values, perform no allocation or
aggregate copy, and add no production instrumentation.

## Producing and checking evidence

From the repository root, with a current provenance-admitted full Stage-4
Pure-Simple CLI:

```sh
SIMPLE_BINARY=/absolute/path/to/stage4/simple \
  sh scripts/check/produce-cosmos-fsbl-fail-closed-coverage.shs
sh scripts/check/check-cosmos-fsbl-fail-closed-coverage-receipt.shs
```

The producer measures the six C guards with GCC/gcov, runs the existing SSpec
with Simple decision/condition coverage enabled, and writes artifacts below
`build/evidence/cosmos-fsbl-fail-closed/`. It refuses a missing CLI, missing
coverage output, invalid Stage-4 provenance, and any Rust bootstrap path.

The checker independently recomputes the helper-bounded C arcs and parses the
SDN decision and condition sections. It requires exactly six uniquely keyed
decision rows and six uniquely keyed condition rows on the exact core owner and
guard lines, with both outcomes nonzero and no unexpected core row. It also
validates the canonical decimal TSV, all artifact digests, C harness and Simple
spec identities, the forced profile and Zynq register headers, producer
identity, exact compiler flags/tool/version, and the live Stage-4
binary/provenance binding. Both retained run logs are digest-bound and the
checker independently requires their exact C and Simple PASS verdicts. It fails
closed if evidence is missing, stale, malformed, duplicated, or moved.

## Claim boundary

An accepted receipt proves host-executable decision parity and full outcomes
for the six scalar fail-closed guards. It does not prove ARM32 relocatable
Pure-Simple linkage, physical BootROM/FSBL handoff, clocks, DDR, resets, or PL
hardware. `doc/08_tracking/bug/pure_simple_arm32_emit_object_ignored_2026-08-24.md`
remains the firmware-linkage blocker.
