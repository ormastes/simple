# stdlib gap: no symlink/readlink/chmod APIs forces shell delegation

Date: 2026-09-24
Status: open
Found during: SPipe plugin Simple-language migration (doc/03_plan/spipe_plugin_simple_migration.md)

## Problem

The Simple standard library can DETECT symlinks (`is_symlink`,
src/lib/nogc_sync_mut/fs.spl:196,654-659) but cannot create, read, or
remove them, and has no chmod:

| Operation | Node.js | Simple stdlib | Workaround used |
|---|---|---|---|
| create symlink | `fs.symlinkSync` | NONE | `shell_bool("ln -s ...")` / `cmd /c mklink /J` |
| read symlink | `fs.readlinkSync` | NONE | `shell_output("readlink ...")` |
| remove link | `fs.unlinkSync` | `file_delete`? (untested on links) | shell |
| chmod +x | `fs.chmodSync` | NONE | `shell_bool("chmod +x ...")` (POSIX only) |

The SPipe Simple port (`src/spipe_cli/core.spl` in the Spipe repo) needs all
four for `doc-link`, `doctor` link-kind checks, and
`fine-tune-scaffold-training` (chmod +x on generated train scripts).

## Why shell delegation is a poor long-term answer

- Spawns a process per call (slow in hot paths; doctor does 9+ checks).
- Windows `mklink /J` creates junctions, not symlinks — `doctor`'s
  link-kind verification degrades to best-effort on Windows (untested:
  no Windows host available during the migration).
- Quote/space handling in shell strings is an injection footgun.
- Violates the AGENTS.md rule that app code should use stdlib facades, not
  ad-hoc process spawns.

## Proposal

Add runtime externs + stdlib wrappers, mirroring the `rt_file_*` family:

- `rt_symlink(target, linkpath) -> i32` (0 ok)
- `rt_readlink(path) -> text` (or Optional(text))
- `rt_chmod(path, mode) -> i32`
- `rt_unlink(path) -> i32` (if `file_delete` does not already cover links)

stdlib additions in `src/lib/nogc_sync_mut/fs.spl` (or `std.io_runtime`):
`symlink_create`, `symlink_read`, `file_chmod`, plus `is_junction` or a
`link_kind(path) -> enum(none, file, dir, symlink, junction)` so Windows
parity is explicit rather than guessed.

## Evidence / repro

Any attempt to compile a call to a non-existent `symlink_create` fails at
compile; the gap is visible by inspection of fs.spl (only `is_symlink`
exists). The SPipe port's `core.spl` shell-delegation helpers are the
standing workaround to be replaced.

## Acceptance

- `symlink_create`/`symlink_read`/`file_chmod` callable from
  `nogc_async_mut` app code on POSIX and Windows.
- SPipe `core.spl` switched off shell delegation, parity spec
  `test/spipe_cli_parity_spec.spl` still 15/15.
- Windows: junction creation no longer requires `cmd /c mklink`.
