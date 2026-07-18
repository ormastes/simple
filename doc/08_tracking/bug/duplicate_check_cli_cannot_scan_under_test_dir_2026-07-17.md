# duplicate-check CLI cannot scan any path under a `test/` directory (no exclude override)

- **Date:** 2026-07-17
- **Area:** `src/compiler/90.tools/duplicate_check/config.spl` (`default_config`),
  `src/compiler/90.tools/duplicate_check/main.spl` (`parse_args`),
  `src/compiler/90.tools/duplicate_check/detector_files.spl`
  (`matches_detector_exclude`).
- **Severity:** low (usability gap, not a detection-correctness bug).
- **Status:** open — recorded per repo rule against silently working around
  gaps; found while building CLI contract tests for `duplicate-check`
  (task: worker_O_dup_sanity).

## Symptom

`default_config()`'s `exclude_patterns` includes `"test/"` (to keep normal
`src/`-rooted scans from also walking the test suite). This pattern matches
via `path.starts_with("test/")` / `path.contains("/test/")`, so it excludes
**any** file whose path contains a `test/` segment anywhere — including when
the user explicitly points `duplicate-check` at a path under `test/` as the
scan root (e.g. `duplicate-check test/fixtures/duplication/dup_pair`), which
silently yields "0 files" / no findings rather than scanning what was asked
for.

`--exclude PATTERN` on the CLI (`main.spl`, `parse_args`) is additive only
(`config.exclude_patterns.push(...)`); there is no CLI flag to clear or
override the built-in default exclude list. The only way to scan under
`test/` is to call `collect_files`/`find_duplicates*` directly from Simple
code with `config.exclude_patterns = []` (as the existing
`test/01_unit/app/duplicate_check_spec.spl` unit spec already does), or to
supply a project-level `.duplicate_check` SDN config file with an explicit
`exclude = "..."` key (`parse_config_file` replaces the list wholesale) —
neither is available as a plain CLI invocation.

Practical consequence: a user cannot run `simple duplicate-check` against
their own test suite (a legitimate use case — finding copy-pasted test
boilerplate) without editing a config file first.

## Not fixed here

Scope for this task was the `duplicate-check` detection/scoring logic and
its CLI *contract* (via `src/app/cli/duplicate_check.spl` /
`test/**`), not `main.spl`'s argument surface. Per repo rule ("when a
workaround would be needed, fix it or record it"), recording this instead of
adding an ad hoc flag. The system contract spec for this task
(`test/03_system/app/cli/duplicate_check_contract_spec.spl`) works around it
by copying the fixtures to a scratch directory outside any `test/` segment
before invoking the CLI, mirroring the existing pattern in
`test/03_system/infrastructure/app_io_mod_source_run_spec.spl`.

## Suggested fix (not implemented)

Add a `--no-default-excludes` (or `--exclude-reset`) flag to `main.spl`'s
`parse_args` that clears `config.exclude_patterns` before applying
`--exclude` additions from the command line — analogous to `--no-ignore` in
common file-search tools. Small, backward compatible, does not change
default behavior.

## Resolution (2026-07-17)

FIXED (haiku fix lane F4, opus-reviewed APPROVE, static verification only — tool unreachable by working harness): --no-default-excludes flag added to parse_args + help text; exact-match arm, no prefix shadowing of --exclude=.
