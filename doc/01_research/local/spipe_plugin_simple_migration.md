# Local Research: SPipe Plugin Simple-Language Migration

Date: 2026-09-24. Scope: inventory of the Node implementation in the SPipe
submodule (`.spipe/spipe`) and the Simple-language counterparts/patterns in
the host repo that the migration must match.

## Git state of the submodule

- Submodule gitdir: `.git/modules/.spipe/spipe`; HEAD file records
  `155d58a4898750bf9e20f8f1d656ad8185111687`, detached (matches remote branch
  `work/spipe-root-hook-docgen`, commit "feat(setup): install root manifest
  hook for workspace hosts" per task brief).
- `packed-refs` lists only `refs/remotes/origin/main = 6e1d8db`; no local
  branches (`refs/heads` empty). HEAD (155d58a) is not origin/main — the
  migration branch must be created from `origin/main` and the relationship of
  155d58a to main resolved with `git merge-base` before pushing.
- OUT OF SCOPE / DO NOT TOUCH: uncommitted local modification in
  `.spipe/spipe/doc/00_llm_process/spipe/skill.md` (adds
  `### Trap: {...} in a step() string is INTERPOLATION...` at line 370).
  Another agent's in-flight work; the migration branch must not include it.

## Node surface inventory

### CLI — `cli/spipe.js` (1637 lines, ESM, zero dependencies)

`moduleRoot` derived from `import.meta.url` (line 6); arg dispatch is one
switch over `process.argv.slice(2)` (lines 1495-1637). Node APIs used:
`node:fs` (incl. `symlinkSync`, `readlinkSync`, `chmodSync`, `lstatSync`,
`appendFileSync`), `node:path`, `process.exitCode`.

Core commands:
| Command | Lines | Purpose |
|---|---|---|
| `info` | 121-127 | print module root + surface paths |
| `experts` | 129-139 | list project/domain/tool expert dirs |
| `link-plan` | 141-147 | planned host doc links (6 surfaces) |
| `doc-root` | 157-159 | read `.spipe/config.sdn` `host_process_doc` |
| `doc-link` | 161-194 | create/update host `.spipe/doc` symlink |
| `doctor` | 196-258 | verify module sources + 9 host link invariants |
| `skill` / `fine-tune-guide` / `fine-tune-model-guide` / `fine-tune-template` | 260-284 | print bundled docs |

Fine-tune family (lines 286-1493, ~30 commands, the bulk of the file):
`fine-tune-init` (292), `new-attempt` (326), `record-data` (358),
`record-data-check` (390), `data-plan` (410), `record-model` (434),
`record-model-research` (457), `record/scaffold-model-arch` (478/530),
`record-method` (545), `model-method-options` (574), `select-model-method`
(592), `record/scaffold-training` (609/652, chmod +x the scaffold),
`record-eval` (689), `record-decision` (708), `record-verify-loop` (737),
`record-process` (754), `scaffold-process-docs` (782, writes 4 doc
scaffolds), `record-requirements` (881) + `options` (949) +
`select-requirements` (979, deletes options files after selection),
`record-app` (1020), `record-retune` (1038), `create-retry` (1057),
`app-handoff` (1090), `status` (1128), `doctor` (1174), `ready` (1259),
`next` (1320), `report` (1373), `verify` (1419, required-field check on an
attempt `.sdn`, exit 0/1/2). All are host-CWD-relative file appends/writes of
`.sdn` registries under `.spipe/llm-finetune-process/` plus SDN quoting
helpers (318-324) and option-markdown parsing (906-947).

### MCP server — `mcp/server.js` (187 lines)

Newline-delimited JSON-RPC 2.0 over stdio (line-buffered stdin loop,
173-187; one JSON object per line, no Content-Length framing). Tools
(22-59): `spipe_info`, `spipe_experts`, `spipe_read_doc` (path allowlist,
61-79), `spipe_fine_tune_guide`, `spipe_fine_tune_model_guide`,
`spipe_fine_tune_template`. Resources: single `spipe://skill` (158-168).
`initialize` answers protocolVersion `2024-11-05` (128-134); errors use
code `-32000`.

### Packaging

- `package.json`: `bin.spipe = cli/spipe.js`, `bin.spipe-mcp = mcp/server.js`;
  `files` = README, cli/, mcp/, plugin/, scripts/, doc/, .claude/, .codex/,
  .gemini/. `check` script = `node --check` on both entrypoints.
- `plugin/manifest.sdn:1-9`: name/version/description + `cli`, `mcp`,
  `setup.unix` (sh), `setup.windows` (ps1) pointers.
- `plugin/.codex-plugin/plugin.json:18-23`: `mcpServers.spipe` =
  `{command: "node", args: ["mcp/server.js"]}` — this is the line the
  migration re-points at the Simple server.
- `scripts/setup-spipe-links.sh` (221 lines, POSIX): symlinks 6
  `doc/00_llm_process/*` surfaces into the host doc root (default
  `doc/llm_process`, override via `.spipe/config.sdn` `host_process_doc`,
  `--doc-root`, or `SPIPE_DOC_ROOT`); `setup-spipe-links.ps1` creates Windows
  junctions. These stay as-is (setup runs on the host, not in-process).
- `scripts/build.sh` (276 lines): required-paths gate (7-33), `node --check`
  (48-49), host gitlink checks for `examples/spipe` and `.spipe/spipe`
  (50-54), package.json bin shape check (55), MCP tools/list + tools/call
  smoke via pipes (56-57), CLI smoke greps (58-69), and a full fine-tune
  lifecycle exercise in `mktemp` host dirs (71-274) ending
  `spipe_build_status=pass`. This is the executable spec the Simple port must
  keep passing.
- No `test/` directory exists in the SPipe repo.

## Host Simple counterparts

- `src/app/mcp/main.spl` — production Simple MCP server (framed + JSONL
  stdio; `extern stdin_read_char/print_raw`; module split: tool_table,
  main_dispatch, main_lazy_*). Its POSIX wrapper `bin/simple_mcp_server`
  (359 lines) and `bin/simple_mcp_server.cmd` (108 lines) are the packaging
  model: probe-admitted native exe (`build/bootstrap/mcp-package/` or
  `bin/release/<triple>/`), else source-mode fallback
  `simple run src/app/mcp/main.spl` with `SIMPLE_LIB=<host>/src`.
- `std.mcp_sdk` (`src/lib/nogc_sync_mut/mcp_sdk/`): `core/json`,
  `core/jsonrpc`, `core/types`, `server/{app,builder,registry,router,state,
  pagination,method_detect}`, `transport/{stdio,transport}`.
  `server/app.spl` is a declarative facade (`mcp_server_init`,
  `mcp_server_tool`, `mcp_serve`), protocolVersion 2025-06-18 — the SPipe
  MCP port should be built on it. NOTE `src/app/mcp/main.spl:32-36`: the
  full server deliberately avoids std.mcp_sdk due to a co-compiled symbol
  collision; a fresh, small spipe server has no such constraint.
- `std.io_runtime` (`src/lib/io_runtime.spl:8-19`): shell/shell_output,
  file_read/write/append, dir_create_all/list/walk/exists, env_get/set,
  cwd/home, process_run(_bounded/_timeout)/spawn_async, get_args/cli_arg_at,
  exit, host_os/host_arch — covers every CLI need except below.
- `std.process` (`src/lib/process.spl`) → `process_run(cmd, [args])`.
- Existing SPipe-adjacent Simple apps in host: `src/app/spipe_docgen/`
  (doc generator for SPipe specs), `src/app/sspec_maintain/source_facts.spl`.
- Native build path (AGENTS.md + `scripts/bootstrap/bootstrap-phase-
  verification.shs:473-497`):
  `bin/simple native-build --source src/compiler --source src/app
   --source src/lib --entry-closure --entry <main.spl> --strip
   --output build/bootstrap/mcp-package/<name>`; Windows triple
  `x86_64-pc-windows-msvc` (`bin/release/x86_64-pc-windows-msvc/`).
- Host SPipe tests today: `test/01_unit/app/sspec_maintain/*_spec.spl`,
  `test/01_unit/app/spipe_docgen/docgen_end_to_end_spec.spl`,
  `test/03_system/app/spipe/feature/*.spl` (BDD: `describe`/`it`/`step`,
  `use std.spec.*`, run via `bin/simple test <spec> --mode=interpreter`).
- Host gitlink guard: `scripts/check/check-spipe-submodule-gitlinks.shs`
  (+ `.ps1`).

## Capability matrix and gaps (Node API → Simple stdlib)

| Node API | Simple | Status |
|---|---|---|
| argv parsing | `get_args` / `cli_arg_at` | OK |
| stdout/stderr print | `print` / `stderr_write` | OK |
| read/write/append files | `file_read`/`file_write`/`file_append_text` | OK |
| mkdir recursive, readdir | `dir_create_all`, `dir_list` | OK |
| exit codes | `exit(code)` | OK |
| process cwd/env | `cwd`, `env_get` | OK |
| JSON parse/emit (MCP) | `std.mcp_sdk.core.json`, `std.js.builtins.json` | OK |
| SDN value quoting | string ops (port `quoteSdn`) | OK, port needed |
| symlink/readlink/unlink | NONE — only `is_symlink` detection (`src/lib/nogc_sync_mut/fs.spl:196,654-659`) | GAP |
| chmod +x | NONE | GAP |

Gap options: (a) add `rt_symlink/rt_readlink/rt_chmod` externs to the host
runtime (heavy: compiler/runtime change); (b) implement via `shell_bool`
(`ln -s`, `readlink`, `chmod`) with a Windows branch (`cmd /c mklink /J`) —
pragmatic, no runtime change; (c) leave `doc-link`/link surgery to the
existing setup scripts. Recommend (b) with (a) filed as a bug.

## Risks

1. Stdlib symlink/chmod gap (above) blocks byte-parity for `doc-link`,
   `doctor` link checks, and `fine-tune-scaffold-training` chmod.
2. `std.mcp_sdk` lives in the HOST repo — the migrated plugin only runs on a
   Simple runtime, never standalone Node. Acceptable per migration goal but
   changes the package's install requirements (document in README).
3. Submodule HEAD (155d58a) is not origin/main (6e1d8db); branch base and
   PR diff must be chosen deliberately.
4. Dirty `skill.md` in the submodule working tree must not be swept into the
   migration commits.
