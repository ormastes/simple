# Local Research: SSPEC Traceability and Folder Reorganization

**Date:** 2026-05-28
**Status:** Active

## Findings

- `doc/06_spec/` currently mixes generated markdown, legacy markdown, SDN data,
  grammar artifacts, and generated indexes. Root-level generated files such as
  `doc/06_spec/feature/usage/math_blocks_spec.md` make traceability ambiguous when the
  executable source is nested under `test/feature/usage/`.
- `test/README.md` already defines broad test categories, but it did not state a
  mirror rule between executable tests and generated manual/spec docs.
- `spipe-docgen` generated scenario bodies from `describe` / `it` structure, but
  before this reorg slice it wrote docs as `{output_dir}/{stem}.md`.
- Verification and system-test skills still referenced the older
  `doc/06_spec/app/<app_name>/feature/...` pattern, which conflicts with a
  tree-based traceability model.

## Decision

Use the executable test path as the canonical generated spec-doc path:

`test/<kind>/<domain>/<feature>_spec.spl` ->
`doc/06_spec/<kind>/<domain>/<feature>_spec.md`

This keeps requirement, research, design/architecture, generated spec/manual,
plan, implementation, guide, and executable test links checkable by path and
feature slug. Legacy root-level docs can be migrated incrementally.

## Local Changes Driven By This Research

- `spipe-docgen` now derives nested output paths from source spec paths.
- Generated indexes now link to the nested relative output path.
- `doc/06_spec/README.md` documents the canonical layout and quality rules.
- `test/README.md`, `$system_test`, `$design`, `$impl`, and `$verify` now state
  the same mirrored layout and traceability expectations.

## Remaining Work

- Migrate legacy root-level `doc/06_spec/*.md` files into the mirrored layout
  once each source spec/test path is identified.
- Add a traceability check that fails when generated docs and executable specs
  diverge.
- Extend docgen invocation routing so normal test/doc runs refresh the mirrored
  output tree rather than legacy flat output.
