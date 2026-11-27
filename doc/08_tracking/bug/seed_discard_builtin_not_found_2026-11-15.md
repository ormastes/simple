# Seed rejects `discard` (function discard not found)

Status: open
Found: 2026-11-15, REV-01 (PR #9449)

## Symptom
On the Rust seed (`seed-attr2/simple.exe`), a spec statement `discard <expr>`
fails with `function discard not found`.

## Workaround (tagged)
`test/01_unit/lib/scv/rev01_pinned_revision_lease_spec.spl` uses
`val _ignored = <expr>` instead of `discard <expr>`. Revert to `discard` once
the seed supports it.

## Fix
Make the seed accept `discard` with the same semantics as pure Simple, or
remove `discard` from the language guide if it is not meant to be supported.
