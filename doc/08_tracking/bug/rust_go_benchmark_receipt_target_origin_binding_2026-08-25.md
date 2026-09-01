# Rust/Go benchmark receipt target and origin binding gap

Status: VALIDATOR FIXED; producer evidence remains TODO. The
`rust-go-benchmark-parity` ledger row remains TODO.

The lane-specific numeric oracle now validates a Linux ELF executable/shared-
object header, binds class/endianness/machine to the declared environment,
requires distinct Simple/Rust/Go blobs, recomputes all retained statistics,
and verifies the canonical live Stage 4 compiler chain. This closes fabricated
or mismatched executable-header evidence but does not complete artifact origin.

The signed target is now fail-closed before large artifact loading:
`target_kind` must be `native-host`, `target_id` must equal the benchmark
environment's `host_id`, and that environment binds Linux architecture to all
three ELF headers.

The closed build-origin receipt now binds each committed source hash, fixed
recipe ID and literal argv, retained compiler blob, nonempty version capture,
output hash, and zero exit status. The toolchain identity is derived from the
three compiler and three version hashes. Import recomputes every identity and
the source/output/environment relationships without rebuilding timed artifacts.

This proves closed, independently reviewed producer-origin binding, not
cryptographic compiler-to-output causality. The independent reviewer attests
that the fixed recipes ran; stronger causality would require compiler-signed
outputs or replaying builds, which is intentionally outside benchmark import.
Real benchmark samples and a production receipt are still required before any
TODO-to-PASS promotion.
