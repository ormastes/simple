# spipe plugin: manifest paths resolve from the parent dir, and two version numbers disagree

**Status:** OPEN (minor)
**Filed:** 2026-09-05
**Scope:** `examples/05_stdlib/spipe/plugin/`

Filed as a record rather than fixed because both items need an owner decision,
not a mechanical edit. Everything else about the spipe surface is healthy — see
"What is green" at the bottom, which is the more important half of this record.

## 1. Manifest path tokens do not resolve relative to the manifest

`examples/05_stdlib/spipe/plugin/manifest.sdn` names `cli/spipe.js`,
`mcp/server.js`, `scripts/setup-spipe-links.shs` and
`scripts/setup-spipe-links.ps1`. `.codex-plugin/plugin.json` in the same
directory names `mcpServers.spipe.args = ["mcp/server.js"]`.

Every one of those paths exists relative to
`/home/yoon/dev/simple/examples/05_stdlib/spipe/` — the manifest's **parent** —
and **none** exists relative to
`/home/yoon/dev/simple/examples/05_stdlib/spipe/plugin/`, where the manifest
actually lives. There is no `.../spipe/plugin/mcp/server.js`.

Whether this is a defect depends on the consumer's cwd convention, which was not
established. If a plugin host resolves manifest paths relative to the manifest
(the usual convention) every one of these is dangling. If it resolves them
relative to a declared plugin root one level up, they are all fine. Someone who
knows the loader should confirm which, and if it is the former, either move the
manifest up or make the paths `../`-relative.

Note this is currently latent: `.mcp.json` and `~/.codex/config.toml` both point
at `examples/05_stdlib/spipe/mcp/server.js` directly, bypassing the manifest, so
the working configuration never exercises these tokens.

## 2. Version drift

| file | version |
|---|---|
| `plugin/manifest.sdn:3` | `0.1.0` |
| `plugin/.codex-plugin/plugin.json:3` | `0.2.0` |

The running MCP server reports `serverInfo.version = "0.1.0"`, agreeing with the
manifest. Which is authoritative was not determined, so neither was changed.

## 3. `check-mcp-wrapper-contract.shs` never exercises the host triple

The guard passes (`t32_wrapper_native_contract=pass wrappers=2`, rc 0), but its
fixtures are synthetic `$TMPDIR` trees with the triple hardcoded to
`x86_64-unknown-linux-gnu` (script lines ~95-204). On this aarch64 host its
green verdict therefore says nothing about the real
`bin/simple_mcp_server` wrapper or the real
`bin/release/aarch64-unknown-linux-gnu/` layout. Not a false PASS — the guard is
a self-test and passes as one — but it should not be read as coverage of the
host wiring.

## What is green (verified 2026-09-05, do not re-litigate)

- **spipe MCP server** (`node examples/05_stdlib/spipe/mcp/server.js`), driven as
  a real newline-delimited-JSON stdio session (it uses no `Content-Length`
  framing): `initialize` returns `serverInfo {"name":"spipe","version":"0.1.0"}`,
  protocol `2024-11-05`; `tools/list` returns **6** tools — `spipe_info`,
  `spipe_experts`, `spipe_read_doc`, `spipe_fine_tune_guide`,
  `spipe_fine_tune_model_guide`, `spipe_fine_tune_template`. Both
  `spipe_info` (285 chars of `text` content) and `spipe_experts` (75 chars)
  returned `result` with no `isError`. stderr empty, rc 0.
- `node .spipe/spipe_project/cli/spipe.js doctor .` -> `spipe_doctor=pass`.
- `check-spipe-submodule-gitlinks.shs --check` -> rc 0,
  `STATUS: PASS spipe-submodule-gitlinks`.
- `check-mcp-wrapper-contract.shs` -> rc 0 (with the caveat in §3).
- No dangling symlinks anywhere under `plugin/`; all three
  `skills/{release,software-release,sync}/SKILL.md` exist with non-empty
  `name` + `description` frontmatter.

## Separately observed: harness could not spawn `simple-mcp`

This session's MCP client reported `ENOENT: posix_spawn 'bin/simple_mcp_server'`
even though `/home/yoon/dev/simple/bin/simple_mcp_server` existed (7,367 bytes,
mtime 2026-09-04) before the session began. `.mcp.json` gives that command as
the **relative** path `bin/simple_mcp_server` with `"cwd": "."`; a relative
command containing a slash is resolved against the spawner's cwd, so the client
apparently did not spawn from the repo root. The shebang hypothesis was checked and eliminated: `head -1 bin/simple_mcp_server` is `#!/bin/sh` and the file is executable, so a missing interpreter is not the cause. `~/.codex/config.toml` uses the
absolute form and is unaffected. Making `.mcp.json`'s commands absolute — or
confirming the host honours `cwd` for `command` as well as for the child — would
remove the ambiguity.

Not a defect in the wrapper itself: with the native artifacts still building,
`bin/release/aarch64-unknown-linux-gnu/simple_mcp_server` does not exist yet, so
the wrapper would in any case exit 127 with
`error: native simple_mcp_server not found` (`bin/simple_mcp_server:170-176`).
That is the designed behaviour while the build is in flight.
