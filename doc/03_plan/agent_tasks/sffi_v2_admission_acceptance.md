# Agent tasks: SFFI v2 admission acceptance

**Status:** `developing` — acceptance tests first  
**Merge owner:** `/root`  
**Final reviewer:** highest-capability Codex reviewer

## Frozen shared contract

Categories, runner names, and manual-step/checker names are frozen in
`doc/05_design/sffi_v2_admission_acceptance.md`. Every lane keeps source-only
evidence separate from artifact admission and makes no hot-path change.

| Lane | Scope | Sidecar | Status |
|---|---|---|---|
| A1 | modern SSpec acceptance fixture/scenario scaffold | N/A | reworked; uses A2 owner |
| A2 | fixture manifest/trust/receipt matrix and runner seam | N/A | structured fixture commit ready |
| A3 | loader/inventory typed-result handoff and no-hot-path gate | N/A | blocked: no immutable handle hash/load primitive |
| A4 | direct `rt_*` backlog prioritization + exact autofix contract tests | N/A | developing |

Each lane works in a separate worktree, commits only owned files, does not
push, and returns a failing blocker rather than a fabricated PASS. A1 starts
the executable `@tag("developing")` SSpec before any implementation promotion.

## A3 identity/admission blocker (2026-08-27)

The current `provider_admit_dynamic_v1` hashes bytes read by pathname and then
opens that pathname separately. A second pathname read after opening would not
bind the loaded image: an A→B→A replacement can still make both reads agree
while the loader retains B. `DynLibKind` exposes no immutable opened-file
handle, handle hash, or same-handle load operation on this platform.

Accordingly A3 makes **no** loader admission/security promotion and leaves
close-failure ownership untouched: `provider_session_close_v1` keeps the
session open if `dynlib_close` fails. The diagnostic
`scripts/audit/sffi-provider-loader-identity-blocker.shs` confirms the
pathname-only blocker and that cached session query/invoke bodies do not repeat
loader-admission reads, hashing, open, or symbol lookup. It is not an artifact
identity proof, a provider signature check, an allocation-free marshalling
claim, or an NFR-SFFI-ACC-001 PASS.

Unblock only by adding a platform-owned immutable handle capability with exact
hash-on-that-handle and load-from-that-same-handle semantics, plus explicit
close-failure ownership/result handling and runtime tamper fixtures. The
acceptance runner/inventory must then consume that typed result; it must not
infer it from a pathname digest or a source-only ledger.

## A1 acceptance fixture IDs

The only supported fixture IDs are exactly `admitted`, `unsigned`,
`artifact-mismatch`, `untrusted-signer`, `abi-mismatch`, `stale-receipt`, and
`null-contract`. The A2 runner returns `Ok` only for that exact canonical
category and its summary is that category unchanged, never prose. Any
unsupported fixture returns `Err("SFFI admission fixture is blocked ...")`; the
developing SSpec then fails rather than accepting it. Rust seed discovery sees
`# @tag developing`; the language-level `@tag(...)` attribute and colon form
are not discovery metadata.
