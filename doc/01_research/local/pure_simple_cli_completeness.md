<!-- codex-research -->
# Pure-Simple CLI completeness: local research

The full CLI links and dispatches through `app.io.cli_ops` and
`app.io._CliCommands.run_commands`. Three independent faults blocked admission:

- `rt_cli_current_exe_path` returned the Rust runtime string layout while the
  compiled CLI used legacy `STR1`; equal executable paths compared unequal and
  recursively spawned the candidate.
- The no-driver `-c` path called the incompatible four-argument
  `rt_file_write_text`; the repository already provides the compatible
  delete-plus-`rt_file_write_text_at` `file_write` wrapper.
- Both `fs.spl` variants declared bare `walk_dir`. Suffix aliasing linked it to
  `src.infra.walk_dir`, whose `Result<[text], IoError>` ABI is incompatible with
  `[DirEntry]`. The runtime already exports `rt_dir_walk`.

Selected implementation: reuse scalar argv identity, `file_write`, and
`rt_dir_walk`; add no new abstraction or runtime API.
