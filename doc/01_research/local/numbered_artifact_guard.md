<!-- codex-research -->
# Numbered Artifact Guard - Local Research

## Problem

LLM agents sometimes avoid updating an existing file by creating a numbered copy
such as `foo_1.spl`, `foo_2.spl`, `foo_part1.md`, `foo_v2.md`, `foo_ver1.md`,
or `foo_version1.md`. The same smell appears when docs are split into numbered
artifacts instead of meaningful documents.

## Local Scan

The repo contains many historical numeric names. A broad tracked-file scan first
reported 539 paths, but most were legitimate source shards or imported
TRACE32/CMM report filenames. The guard now excludes those classes and the
remaining doc artifacts were renamed to semantic filenames, so
`sh scripts/audit/numbered-artifact-guard.shs --all` passes.

Representative classes found:

- Existing test shards: `test/unit/compiler/complete/driver_1_complete_spec.spl`
- Existing deep coverage shards: `test/unit/compiler/deep/module_resolver_1_spec.spl`
- Historical docs with part/version names, since renamed to semantic filenames
- Legitimate architecture names: `x86_64`, `rv64`, `i8086`

## Decision

Prevent new suspicious numbered artifacts at commit/check time while avoiding
false positives for intentional source shards and imported report names. The
guard scans staged added/renamed paths by default, supports `--working` for
uncommitted added/untracked paths, supports `--changed-from <ref>` for CI/build
checks, and supports `--all` for local research.

## Implemented Guard

- Script: `scripts/audit/numbered-artifact-guard.shs`
- Repo hygiene integration: `scripts/check/check-repo-hygiene.shs`
- Default check: staged added/renamed paths
- Working-copy check: added/untracked/renamed paths before staging
- CI/build check: added/renamed paths from `origin/main` merge-base to `HEAD`
  when `origin/main` exists, or from `NUMBERED_ARTIFACT_BASE_REF` when set
- Research check: `sh scripts/audit/numbered-artifact-guard.shs --all`

Blocked patterns:

- `name_1`, `name-1`
- `name_v1`, `name-v1`
- `name_ver1`, `name-version1`
- `name_part1`, `name-part1`, `part1`

Allowed examples:

- Dates such as `thing_2026-05-30.md`
- Semantic release/version artifacts such as `RELEASE_0.6.0_SUMMARY.md`
- Architecture/platform names such as `x86_64`, `rv64`, `i8086`
- Existing source implementation shards such as `parser_primary_part1.spl`
- Imported report files under `doc/09_report/misc/`
