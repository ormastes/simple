# Shell string-command APIs: ~209 call sites should move to argv

**Status:** OPEN
**Severity:** Medium (injection-prone sink, no known exploit)
**Filed:** 2026-11-17 (type-hardening sweep, owner policy 2026-11-16)

`process_run(cmd: text, args: [text])` and `process_run_bounded*` already take
argv arrays. The string-command shell APIs still take one `text` that a shell
parses: `shell()` (`src/lib/nogc_sync_mut/io/process_ops.spl`), `shell_output`
and `file_shell_run` (`src/lib/nogc_sync_mut/io/file_shell.spl`, run as
`sh -c`), `shell_cmd` (`src/lib/nogc_async_mut/mcp/main_lazy_json.spl`),
`shell_eval` (`env/config.spl`, both layers).

Measured 2026-11-17: `git grep -n "shell_output(\|shell_cmd(" -- src` = 209
lines; 7 further `process_run("sh", ["-c", ...])` sites under `src/lib`.

## Work
1. Census the call sites; classify each as (a) fixed literal command, (b)
   interpolates caller data, (c) genuinely needs shell features (pipes/globs).
2. Migrate (b) first to `process_run(cmd, [args])`; (a) can follow.
3. Keep (c) on `shell()` with a documented exception per site.
4. Ratchet: add a baseline gate that fails on NEW `shell_output`/`shell_cmd`
   call sites (same pattern as `check-no-direct-rt.shs`).

Do not do this as one PR; split per directory.
