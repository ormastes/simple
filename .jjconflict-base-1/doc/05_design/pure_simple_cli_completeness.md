# Pure-Simple CLI completeness design

`_cli_driver_binary` rejects the canonical argv-0 executable. When no external
driver remains, `cli_run_code` writes a temporary `fn main()` module through the
existing compatible writer and calls `interpret_file`. Both filesystem variants
map `rt_dir_walk` results without a bare extern alias. Source-contract tests
cover each boundary; the rebuilt candidate supplies runtime evidence.

Interpreter test execution wraps the preprocessed spec with the shared
`print_summary`, executed-count, and exit-code checks. The canonical runner and
font evidence runner use the same wrapper so red and empty specs fail closed.
