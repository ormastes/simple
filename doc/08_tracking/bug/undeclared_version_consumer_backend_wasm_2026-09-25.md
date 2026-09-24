# Undeclared version consumer: src/plugins/backend_wasm/simple.sdn pins 1.0.0-rc.1 on main

Date: 2026-09-25
Severity: process (release-blocking for the next version bump)

## Finding

`src/plugins/backend_wasm/simple.sdn` line 3 carries
`version: 1.0.0-rc.1` while the version authority (`release/version.sdn`)
on untouched `main` was `1.0.0-beta.14` (channel beta). The file is NOT in
the authoritative projection list (`src/app/release/version_authority.spl`,
`_required_projection_paths()`, 17 paths).

`check_repository_version(root)` fails closed on any *undeclared* version
consumer it discovers (it greps the tree for the authority semver), so
`main` was already version-red before the 2026-09-25 rc1 work — the same
shape as the "1.0.1-beta.1 found the version authority already red" incident
recorded in the release skill history.

The stale value is a leftover from the abandoned 2026-09
`work/release-1.0.0-rc1` session (its worktree `/home/yoon/release-wt` still
exists, 4566 commits behind main — do not reuse it).

## Current state after the fresh rc1 bump (work/release/rc1)

The 2026-09-25 `work/release/rc1` bump moves the authority to `1.0.0-rc.1`,
so the undeclared consumer's VALUE now agrees with the authority by
accident. If discovery flags undeclared consumers by presence of the semver
string, `simple release version-check` may still fail on it; the candidate
workflow's version-check job (`.github/workflows/candidate.yml`) is the
first place this will surface definitively.

## Recommended resolution (choose one, then close this bug)

1. If the field is the plugin's own version (not a product projection):
   decouple it from the product semver (e.g. `version: 1` plugin schema
   version) so it stops matching the authority-string grep.
2. If it is a product projection: add it to `_required_projection_paths()`
   and to the projection table in the SPipe release skill + guide.
3. If nothing consumes the field: delete it.

Until one of these lands, every future version bump risks a red
version-check on an untouched tree.
