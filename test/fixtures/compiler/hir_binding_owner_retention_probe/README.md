# Mutable alias owner retention

UNEXECUTED native regression for the shared unannotated val/var declaration mechanism. Uses the real imported provider from fixture commit a681ad90cd37cce2811e7245ca85d09cf586a72a; no consumer type annotation masks inference. Expected stdout: `1\n1\n0\n`, exit 0. Build with the newly pinned combined pure-Simple producer, LLVM object route and recorded runtime/entry authority; no old-producer rerun is requested. This fixture declares no mutable module globals.

Existing immutable alias and typed foreach baseline receipts are in `/dev/shm/simple-or-variant-probe-20261010/results2/summary.json`. The direct array-literal foreach gap is separately unresolved by the statements-only repair.
