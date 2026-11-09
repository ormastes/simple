# SFFI authority baseline stale after GPU/bootstrap sync
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Resolution 2026-11-09 (p3-subj6 lane, worktree of origin/release/1.0.0)

Root cause of the "stale baseline" proven: snapshot commit `4edef8fab8e` ("feat:
snapshot current development state", the GPU/bootstrap sync) rewrote
`scripts/audit/sffi-call-authority-census.shs` back to a pre-2026-08-24 variant,
dropping three scanner capabilities (prose masking of strings/docstrings,
wildcard `use ...sffi...*` inventory, multiline-signature body scanning) and
deleting `scripts/audit/baselines/sffi-call-authority-v1.tsv`, while leaving the
selftest that encodes the mature behavior. Measured on this tree: the selftest
died at `cp: cannot stat ... sffi-call-authority-v1.tsv`; past that, the
regressed scanner counted docstring/string mentions as raw calls and silently
skipped multiline-header bodies.

Fix: restored the scanner, selftest, and baseline from `4edef8fab8e^` (the last
mature state; identical lineage, no behavior invented). Executed evidence:

- `sh scripts/audit/sffi-call-authority-census-selftest.shs` -> `sffi call authority census selftest: PASS` (was: ERROR, cp failure / assertion mismatch).
- `sh scripts/audit/sffi-call-authority-census.shs` -> PASS, `missing_authority_call_sites=15489` against the committed ratchet 19412. The baseline was NOT increased; the differing rows were identified instead:
  - 54 rows the regressed scanner emitted are prose/multiline-header artifacts (e.g. `src/app/office/interactive.spl` `rt_terminal_enable_raw_mode` at 467/569) — reviewed, correctly absent under the mature scanner.
  - 625 rows only the mature scanner emits are real wildcard-SFFI-import call sites (top: `src/lib/nogc_sync_mut/spec/evidence/counterpart/host_vulkan_lavapipe_provider.spl` 66, `src/lib/nogc_async_mut/cuda/mod.spl` 62, `src/os/tls13/_Tls13/handshake.spl` 52) — reviewed, correctly present.

This also explains the original +1 (19503 vs 19504): the two measurements came
from different scanner identities across the sync, not from a new unscoped call
site. No Simple source was scoped or changed; only the audit script and its
deleted baseline were restored.
