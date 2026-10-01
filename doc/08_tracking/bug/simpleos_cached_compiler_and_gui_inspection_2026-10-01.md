# Cached compiler override and unrepresented GUI inspection

Status: source fixes and regression scenarios authored; execution/docgen
TEST_BLOCKED. Base: `4cd46825d5214d5340b6c3075ed2faef338bc330`.

After a successful `build_os_with_backend`, the old process-local cache keyed
only entry/output/backend/target and returned before resolving the current
compiler. Changing `SIMPLE_BINARY` to a missing or inadmissible compiler could
therefore return success for the old target. The same shortcut did not consult
current source inputs or options. The fix removes this redundant cache and
keeps the canonical persistent-cache check after current compiler admission.
Its live regression warms an actual build and changes the explicit identity
in the same process; it does not fabricate a cache stamp or kernel.

`os run --debug-gui --show-plan` and `--print-command` previously discarded
the GUI mode during inspection and rendered the ordinary sealed shape.
The option owner now refuses that unsupported projection explicitly before
build or host probing. Normal inspection and execution-only GUI behavior
remain supported according to their existing paths. Pure and actual-CLI
negative matrices cover the default and four represented named routes.

The detailed gate inventory and actual runner-absence evidence are in
`doc/03_plan/sys_test/simpleos_sealed_cli_followup_2026-10-01.md`.
