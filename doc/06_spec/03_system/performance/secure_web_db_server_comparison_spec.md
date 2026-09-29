# Secure server incumbent comparison

**Status:** PARTIAL/RED — executable admission-policy scenarios prove request
parsing/control-plane work, small batches, and stale generations remain on CPU,
while only an eligible coarse batch reaches the GPU-candidate decision. These
are policy checks, not physical acceleration evidence. The unavailable-device
case also asserts the exact CPU selection reason and mutually exclusive
GPU/fallback counters before the physical benchmark oracle fails closed.
Preregistered native
benchmark and physical-device receipts are not yet available.

The unresolved release benchmark requires at least 30 paired ABBA samples for
matched Simple/nginx HTTP and SSR workloads, Simple/PostgreSQL database
workloads, Simple/OpenSSH operations, and scalar/SIMD/GPU cryptography. Linux
and SimpleOS results must remain separate. Each accepted receipt must record
versions, configuration, artifact hashes, throughput, median/p95/p99,
errors/retries, CPU, and max RSS. No such end-to-end receipt is accepted by this
manual yet. Missing incumbents, client bottlenecks, unsupported features, or
nonphysical GPU evidence are hard failures.

**Executable SPipe:** `test/03_system/performance/secure_web_db_server_comparison_spec.spl`
