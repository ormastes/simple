# Descriptor-only byte endpoint boundary

Executable: `test/01_unit/lib/io/piped_byte_endpoint_v1_spec.spl`.
Status: **NOT_RUN**, three authored cases.

The cases assert exact generation-plus-binding equality, refusal of malformed
identity values, and owner retention on invalid close without fabricated EOF.
They do not create a descriptor or qualify native transfer, stale close after FD
reuse, cross-UID authorization, process termination, or Host resource release.
Those require the separate actual SCM/pipe-owner and application scenarios.
