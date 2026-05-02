<!-- codex-impl -->
# World Units and Newunit Agent Tasks

1. Parser/runtime owner: keep `newunit` mapped to standalone nominal wrapper declarations and reject measurement-family forms.
2. Catalog owner: expand `world_units_v1.sdn` from authoritative importers while preserving local committed normalized data.
3. SFFI owner: ensure custom primitive registry resolution is shared by lint, layout, bitfield, and FFI generation paths.
4. Migration owner: convert public raw primitives to `newunit`, measurement `unit`, enum, Option, or Result types and leave reason-coded allowlist entries only at ABI boundaries.
5. Verification owner: run focused parser/SFFI/lint tests, full test/lint/check, and compiler/tooling smoke checks.
