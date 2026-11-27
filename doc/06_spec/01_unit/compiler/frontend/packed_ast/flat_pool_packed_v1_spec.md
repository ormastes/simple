# Packed flat-pool encoder format and ownership

Authored manual; generated documentation and native SSpec execution pending.

The executable specification checks exact pool-line round trips, deterministic
packed bytes, header/section alignment and ordering, deduplicated strings,
identity/digest admission and tamper rejection. The growing-encode case reuses
caller-owned trace/digest/value inputs across two 256-element encodes and checks
that they remain intact. Mutable private output buffers must not mutate these
public inputs or change format bytes.

Nine cases passed with the explicitly enabled Rust seed diagnostic. The separate
native owned-buffer fixture checks golden little-endian bytes and supports LLDB
allocation-count comparison; it does not qualify the full native encoder.
Evidence: `doc/08_tracking/bug/packed_encoder_repeated_buffer_copy_2026_10_30.md`.
