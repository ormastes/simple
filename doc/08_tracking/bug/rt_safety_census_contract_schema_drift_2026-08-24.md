# rt-safety census read stale SFFI inventory columns

**Status:** fixed in the current SFFI hardening worktree
**Severity:** high for audit accuracy; no runtime impact

## Defect

`sffi-contract-inventory.shs` gained provider-language and cryptographic-
admission columns, but `rt-safety-census.shs` continued reading the former
numeric positions. A current-tree run consequently reported zero unsafe-tagged
rows and placed every declaration in the `unknown` scope despite known
`@unsafe(... ffi ...)` annotations and owned source paths.

## Fix

All joins, summaries, family rows, scope rows, and the census contract now use
the current 11-column inventory schema plus the three appended verification
columns. The consumer first compares the exact header and fails closed on any
future schema drift. The rt-time integration test now invokes the census
contract after generation.

## Evidence

Before the fix, the integration reported `unsafe_tagged_rows=0` and
`scope=unknown` for all 12,123 rows. After the fix, the same fixture passes and
reports 911 unsafe-tagged rows, 10,946 untouched rows, and the complete
production/bootstrap/test partition. Runtime/provider evidence remains zero
for the general tree; the separately reverified fixture admits three clock
symbols. Final run: 25.27 s, 75,308 KiB peak RSS.

The fix changes audit scripts and tests only. It adds no runtime call-path work.
