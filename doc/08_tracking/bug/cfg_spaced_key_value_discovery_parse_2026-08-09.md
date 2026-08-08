# Spaced `@cfg` key/value fails before preprocessing

- Status: OPEN
- Found: 2026-08-09 ARM64 SimpleOS Engine2D entry-closure build

The deployed self-hosted compiler rejects `@cfg(os = "simpleos")` during discovery with `expected RParen, found Assign`, although the preprocessor contains explicit support for reassembling spaced key/value conditions. The supported quoted form `@cfg("os=simpleos")` is used for the ARM64 adapter seam. The parser/discovery path should admit the documented spaced form and reach the existing preprocessor logic; add interpreter and native discovery coverage before changing call sites back.
