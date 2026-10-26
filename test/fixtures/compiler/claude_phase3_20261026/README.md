# Preserved local Phase 3 diagnostics

These eleven sources preserve the remaining local diagnostic fixtures found
during the 2026-10-26 Claude worktree migration. `manifest.json` records their
original paths and SHA-256 values; every copied source matched its origin.
Git normalizes source line endings to LF, so the manifest distinguishes
`origin_sha256` from `repository_lf_sha256`. No source tokens were changed.
The original worktrees and files remain intact.

`src/app/enum_repro/` contains eight sources from `wt-enumid`. Keeping the
`src/app` layout preserves their `app.enum_repro` imports. Supply this fixture's
`src` directory as an additional source root when investigating them. The
`fe_main`, `hc_main`, and `mcl_main` entries deliberately exercise different
compiler closures. In particular, `hc_main` uses a nil argument as a diagnostic;
it is not a passing runtime regression test. Do not include these entries in
the production application inventory.

`optional_payload_owner/` contains the three bare, qualified, and unwrapped
controls from `wt-s2new`. These are investigation inputs, not the actual-owner
regressions qualified in PR #4850.

No compilation, successful runtime result, SPipe admission, or Phase 3
completion is claimed by this preservation change.

## Migration disposition

- Child argument correction: already merged in PR #4814.
- Enum owner work at `wt-enumid` HEAD: already merged in PR #4843.
- Claude's local per-file default flip: migrated into shared release source
  in PR #4865; immutable old compiler binaries retain their compiled default.
- The remaining eleven untracked diagnostic sources: preserved here.
- `wt-rel3-new`'s uncommitted preflight edit lowered `MIN_FREE_GB` from 20 to
  8. Preserve that local operational choice by setting `MIN_FREE_GB=8` explicitly
  for a deliberate diagnostic invocation; the shared default remains 20.
  The exact local patch is retained alongside this README for provenance.
- Missing submodules and flattened Windows symlinks are checkout state, not
  unpublished product changes. The audit preserved them in their source trees.

Phase 3 native completion, Hello World, Phase 3 self-build, default-lane overlap,
and full generic-cache invalidation acceptance remain separate pending gates.
