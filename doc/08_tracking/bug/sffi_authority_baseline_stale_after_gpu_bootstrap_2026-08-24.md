# SFFI authority baseline stale after GPU/bootstrap sync

**Date:** 2026-08-24  
**Status:** OPEN — committed baseline provenance mismatch

## Evidence

One current-tree run of:

```text
scripts/audit/sffi-call-authority-census.shs --summary /tmp/sffi-dynamic-summary.tsv
```

reported:

```text
19504 missing
1712 lexical_unsafe
508 function_unsafe
SFFI call authority census: FAIL (19504 > 19503 raw call sites lack explicit FFI authority)
```

The committed ratchet remains `19503`. Initial triage incorrectly attributed
the delta to a new SSpec `rt_file_read_text` call. That was not sufficient
evidence: the source census recognizes `fn`/`me` bodies, not SSpec `it` bodies.

The loader registry did contain an unscoped counted call in
`_authority_copy_text_bounded`; that declaration and conversion are now tagged
and scoped. A post-fix retained row-level census still reports 19,504 missing.
Intersecting every missing row with paths changed since the last baseline
commit (`454226301f5`) produces zero rows. Therefore neither the Stage-4 SSpec
nor the loader registry can explain the remaining +1: the committed `19503`
ratchet does not describe the committed tree population used by the current
scanner.

## Required resolution

Reconstruct the exact tree and scanner identity used to write the `19503`
ratchet, retain its call-site table, and compare that table with the current
retained rows. Close only when the differing row is identified and either
scoped or explicitly reviewed. Do not increase the baseline merely to make the
gate green.

The Stage-4 wiring spec's direct runtime reads remain separate uncounted debt
and should migrate to the canonical file facade independently.
