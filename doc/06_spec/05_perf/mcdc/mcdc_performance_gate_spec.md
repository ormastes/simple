# MC/DC performance and allocation evidence gate

Run `sh scripts/check/check-mcdc-performance-gate.shs` with the six required
binary environment variables documented in the script. The five fixture
binaries must be built from the same source and compiler invocation, changing
only the MC/DC policy. The gate does not build fixtures, infer allocation
counts, or substitute missing evidence.

It retains binary/compiler SHA-256 identities, ELF section inventories, exact
static-off `.text` equivalence, at least 30 raw samples per mode, nearest-rank
median/p95, peak RSS, allocation receipts for every warmup and sample, fixture
oracle hashes, capacity, mapped-pack, overflow, and evidence-loss fields.
Measured samples run as paired, deterministically rotated five-mode rounds so
each mode occupies each order position evenly without an unrecorded random
seed. Static-off equivalence compares raw `.text` bytes and normalized ELF
section names/sizes against the uninstrumented control.

Missing prerequisites exit 2 (`ERROR nothing-checked`). A measured contract or
budget breach exits 1 (`FAIL`). Only complete evidence satisfying NFR-001
through NFR-006 and NFR-009 exits 0 (`PASS`). No measurement has been retained
by this document; each run writes its own evidence directory.

The focused harness is `sh scripts/check/test-mcdc-performance-gate.shs`.
It uses a deterministic test-only timing wrapper to validate verdict and
retention logic without presenting scheduler-noise samples as performance
evidence. Production runs default to `/usr/bin/time`; evidence produced by the
self-check is temporary and is deleted on exit.
