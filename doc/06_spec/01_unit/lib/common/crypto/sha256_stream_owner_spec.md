# SHA-256 streaming mutable owner

Source: `test/01_unit/lib/common/crypto/sha256_stream_owner_spec.spl`.
Manual intent, 2026-10-04. Native execution and generated docgen: **UNRUN**.

- Preserve original counters and known hashes at seven padding boundaries with
  whole, irregular and byte updates.
- Finalize once, reject later updates without mutation, and reset to the IV.
- Reject over-limit lengths before touching owner buffers.
- Wipe and disable the original owner until explicit reset, then hash abc.

Required execution after runtime admission:
`<runtime> test test/01_unit/lib/common/crypto/sha256_stream_owner_spec.spl --native`.
Generate the canonical manual with
`<runtime> spipe-docgen test/01_unit/lib/common/crypto/sha256_stream_owner_spec.spl --output doc/06_spec --no-index`.
Docgen must report zero stubs. This hand-authored manual is not generated evidence.
