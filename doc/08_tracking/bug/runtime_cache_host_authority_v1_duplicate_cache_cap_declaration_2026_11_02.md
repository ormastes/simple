# Duplicate `cache_cap` declaration blocks POSIX runtime compilation

Status: FIXED (P1) — the duplicate declaration is removed and the focused runtime-link completeness gate passes. Broader runtime behavior is not qualified.

## Failure

The runtime-link completeness check failed to compile
`src/runtime/runtime_cache_host_authority_v1.c`: `struct cache_cap` was defined
twice in the POSIX translation unit. The second definition at line 457 was
reported as a redefinition; the first was at line 450. This blocked compilation
of the runtime provider and therefore its link-completeness check.

The failure was captured in PR #5963's fast-gate run
[41447989043](https://github.com/ormastes/simple/actions/runs/41447989043/job/125285782359).

## Repair and evidence

Commit `c9078245fa1926391ee8a2fd48a56c8c87cbaa6b` removes the redundant
one-line declaration and retains the complete structure with reference count,
closed state, and per-capability mutex. The fix was merged by PR #5964 at
`282f8b82e901d230404a50f7353c35e4defac035`.

After that fix, the PR #5964 fast-gate result records
`local-runtime-link-completeness: pass`; see
[run 41448765768](https://github.com/ormastes/simple/actions/runs/41448765768/job/125288407655).
That workflow run still failed `local-sdn-crc32-sealed` because the bug database
on the source-fix PR head had a stale checksum; this record does not claim the
workflow as a whole passed. This tracking PR reseals the canonical database.

The repair is limited to removing the duplicate declaration. No Windows branch
was changed, and no broader runtime execution or platform qualification is
claimed.
