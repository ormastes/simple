# duplicate-check CLI cannot scan any path under a `test/` directory (no exclude override)

- **Date:** 2026-07-17
- **Area:** `src/compiler/90.tools/duplicate_check/config.spl` (`default_config`),
  `src/compiler/90.tools/duplicate_check/main.spl` (`parse_args`),
  `src/compiler/90.tools/duplicate_check/detector_files.spl`
  (`matches_detector_exclude`).
- **Severity:** low (usability gap, not a detection-correctness bug).
- **Status:** fixed in source; production CLI verification awaits an admitted
  Stage 4 artifact.

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

## Resolution (2026-07-17)

`--no-default-excludes` now clears the default patterns before later
`--exclude` additions. Parsing uses an exact-match arm, so it cannot be
shadowed by the `--exclude=` prefix. Production verification still awaits an
admitted Stage 4 CLI.
