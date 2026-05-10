# W-CT Audit · Done Note

**Wave:** 5
**Date:** 2026-04-26
**Auditor:** W-CT (Claude Opus, 1M ctx)
**Repo HEAD:** `d43e8c5c507df5c6e21222f627d89689b667dc5d`

## Status: COMPLETE

## Deliverables

| Artifact | Path |
|---|---|
| Audit report | `.sstack/crypto-pure-simple-port/research/w_ct_audit.md` |
| Bug 1 (P2 hardening) | `doc/08_tracking/bug/bug_ct_1_base64_compare_inner_branch_2026-04-26.md` |
| Bug 2 (P2 hardening) | `doc/08_tracking/bug/bug_ct_2_compare_hex_hashes_case_fold_branch_2026-04-26.md` |
| Bug 3 (P2 hardening) | `doc/08_tracking/bug/bug_ct_3_rt_runtime_externs_ct_review_2026-04-26.md` |
| Regression spec (CT compare) | `test/unit/lib/common/crypto/constant_time_compare_spec.spl` |
| Regression spec template (cond_swap) | `test/unit/lib/common/crypto/constant_time_cond_swap_spec.spl` |
| Done note | `.sstack/crypto-pure-simple-port/impl/w_ct_audit_done.md` |
| Worktree branch | `worktree-w-ct-audit` |

## Summary

- **23 sites** audited across `src/lib/common/crypto/`,
  `src/os/apps/sshd/`, `src/lib/nogc_sync_mut/tls/`, `src/app/ui.web/`,
  and shadow CT impls in `base64`, `scrypt`, `secure_random`, `signature`,
  `jwt`.
- **0 LEAK** confirmed.
- **19 SAFE**, **4 CONCERN** (3 logged as bugs).
- B6 `rt_black_box` / `black_box(x)` intrinsic confirmed wired but
  intentionally not yet applied — reserved for §3 (ML-KEM rejection
  sampling) and §5.4 (Curve25519 cond_swap), both not yet implemented.
- `cond_swap` / `cond_select` do not yet exist; template regression spec
  left for when §5.4 lands.

## advisor() interactions

- 1 call after data gathering. Advisor sharpened classification rules:
  - canonical `constant_time.spl` is a thin extern shim by design (don't
    file "black_box not used" as a bug);
  - leaky-shape sites without secret-data callers are CONCERN, not LEAK;
  - SSH MAC verify path was missing from data — added grep, found AEAD
    tag check is in runtime extern (not Simple-side).
  All advice followed.

## Source code modifications

**None.** Per task contract, source patches require advisor approval and
are out of scope for the W-CT audit. Bug files capture fix sketches.
