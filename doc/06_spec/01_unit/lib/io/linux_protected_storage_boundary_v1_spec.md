# Protected Linux storage boundary regressions

Source: `test/01_unit/lib/io/linux_protected_storage_boundary_v1_spec.spl`.
Status: AUTHORED_NOT_RUN. No compiler/native execution or branch coverage measurement.

1. Production fixed-relative grammar accepts the actual selector, ready, WAL and reservation artifact roles.
2. Traversal, empty components, alternate separators, NUL, component/depth overflow refuse; the exact240-byte component bound remains accepted.
3. Protected backend helpers reject explicit LegacyPath before filesystem access, for read, no-replace publish and compare-replace.
4. Linux currentness rejects an invalid DATA-only sentinel journal lacking a real protected capability before I/O. No fabricated native descriptor is used and no success authority is synthesized.

These are production-boundary assertions, not native retention, signature, entropy, service-liveness or authentication evidence.
