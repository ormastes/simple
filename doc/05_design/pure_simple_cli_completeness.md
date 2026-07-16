# Pure-Simple CLI completeness design

`_cli_driver_binary` rejects the canonical argv-0 executable. When no external
driver remains, `cli_run_code` writes a temporary `fn main()` module through the
existing compatible writer and calls `interpret_file`. Both filesystem variants
map `rt_dir_walk` results without a bare extern alias. Source-contract tests
cover each boundary; the rebuilt candidate supplies runtime evidence.
