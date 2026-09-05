# SOSIX Open-File-Description I/O Sequencer Specification

The executable specification is
`test/01_unit/os/sosix/open_file_description_sequencer_spec.spl`.

It proves that one open-file description serializes offset-changing I/O,
canonical `FS_READ_AT`/`FS_WRITE_AT` identifiers are used for backend work,
and any reported full or partial progress advances the shared offset by exactly
the transferred byte count. This includes a terminal error after partial
progress: POSIX returns the positive count while the typed receipt retains the
error. Explicit `read_at` and `write_at` leave the shared offset unchanged. A
failure with zero progress preserves the offset.

Tickets contain both the canonical operation identity and a monotonically
increasing per-description sequence. Stale and out-of-order completions are
rejected without consuming the live reservation.

Append does not inspect or predict EOF. Its ticket is marked
`backend_atomic_append`; commit succeeds only when the backend reports the
actual offset selected by its atomic append operation, after which the shared
offset becomes that position plus the transferred byte count.
