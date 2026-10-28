# Pinned Phase 2 lowers octal permission modes incorrectly

- Canonical ID: `phase2_octal_permission_mode_lowering_2026_10_27`
- Status: open; an active source workaround is not a compiler/provider fix.
- Owner: DevHub completion / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: existing P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`; no compiler rebuild.
- Source: `src/lib/common/oauth_token_cache.spl`.
- Regression: `test/fixtures/devhub/native_outlook_token_cache/main.spl`.

Pinned P2 octal-mode source produced read-only final and staging files. The staging file contained the correct replacement token and expiry, so this failure was not a cache parser failure. Decimal 384 is exactly mode0600 and decimal448 is mode0700.

## Evidence

Cache unchanged regression compiled and ran exit0 after decimal-mode workaround; artifact e285b95b2f4250817eec5555aee4d67fea0f1f299d2d3d3568381ae8f9b044fd. Earlier actual filesystem inspection observed both files readonly. The exact compiler lowering cause is not yet isolated.

## Removal condition

Remove the source workaround only after the deployed producer proves octal and decimal OS modes identical in actual create, replace and permission checks; require credential and OAuth cache regressions. Do not close this underlying compiler bug from workaround success.

The standard SSpec suite, all runtime-family combinations and any claim not explicitly tied to an actual artifact remain unqualified. Record the workaround commit in the canonical BugDatabase investigation log after integration; never retire it from a source-only review.
