# bootstrap pinned-archive extraction fails on Windows (symlink checkout)

Date: 2026-11-11
Status: open, workaround in use (`SIMPLE_BOOTSTRAP_LIVE_TREE=1`)
Owner: unassigned

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh ...` (default pinned-archive
lane) aborts before any stage with:

```
tar: .codex/commands/dev.md: Cannot create symlink to '../skills/dev/SKILL.md': No such file or directory
tar: bin/bb: Cannot create symlink to '../tools/bb-cli/bin/bb': No such file or directory
tar: bin/bug: Cannot create symlink to '../tools/bug-cli/bin/bug': No such file or directory
tar: bin/jira: Cannot create symlink to '../tools/jira-cli/bin/jira': No such file or directory
tar: doc/00_llm_process/domain_expert: Cannot create symlink to '../../.spipe/spipe/doc/00_llm_process/domain_expert': No such file or directory
tar: Exiting with failure status due to previous errors
ERROR — git archive extraction failed
bootstrap-pinned-archive-error: could not materialise source snapshot; set SIMPLE_BOOTSTRAP_LIVE_TREE=1 to build the live tree
```

## Root cause

The tree tracks symlinks (`.codex/commands/*`, `bin/bb`, `bin/bug`, `bin/jira`,
`doc/00_llm_process/*` into the `.spipe/spipe` submodule). The default bootstrap
lane materialises HEAD via `git archive` + tar extraction
(`scripts/bootstrap/bootstrap-pin-archive.shs`). Two facts break that on this
Windows checkout:

1. `core.symlinks=false` (Git Bash default without developer mode/admin):
   MSYS tar cannot create symlinks, so every symlink entry errors.
2. Several symlinks dangle by design: they point into `.spipe/spipe/...`, and
   `git archive` never contains submodule content, so the targets cannot exist
   in the snapshot even with `MSYS=winsymlinks`.

POSIX hosts are unaffected (tar creates the dangling symlinks fine). Windows CI
lanes would hit this if/when they run the pinned-archive default.

## Workaround in use

`SIMPLE_BOOTSTRAP_LIVE_TREE=1 sh scripts/bootstrap/bootstrap-from-scratch.sh ...`
builds the live working copy instead of the snapshot. The lane was resumed with
this flag for the 2026-11-11 stage2 run. Risk: uncommitted working-tree edits
become build inputs; acceptable there because the compiler closure
(src/compiler, src/lib, src/app) had no uncommitted edits at run start.

## Candidate fixes

- `bootstrap-pin-archive.shs`: extract with a tar variant/flags that tolerate
  Windows symlink creation failure (e.g. extract as regular files with a
  post-pass that drops known dangling links), or materialise submodule content
  first so intra-submodule links resolve.
- Decide policy for `bin/bb`-style symlinks under `core.symlinks=false`:
  materialised text stubs cannot be exec'd, so wrappers/scripts must keep
  resolving the target path themselves.

## Evidence

- Run log 2026-11-11 (task bash-dwqxqw6k): extraction failure transcript above.
- `git config core.symlinks` = `false`; `file bin/bb` = ASCII text stub.

## Related startup blocker on large/dirty checkouts: bound.entries

With `SIMPLE_BOOTSTRAP_LIVE_TREE=1` on the main shared checkout (375+ dated
dirs under `build/`, `src/compiler_rust/target`, `.simple/storage`), the lane
aborts even earlier — at startup, in the Stage3MaterializedConsumer audit
(`scripts/check/lib/bootstrap-stage3/authority.shs`):

```
stage3-materialized-consumer: Exception calling "Run" with "0" argument(s):
  "bound.entries count=400001 max=400000"
error: Windows materialization receipt is invalid: .../windows-materialized-links.<pid>.env
VERDICT — ABORTED: stage=starting exit=1
```

`MaxEntries = 400000` (env `BOOTSTRAP_STAGE3_GIT_MAX_ENTRIES` can only LOWER
it) is a deliberate fail-closed ceiling: the walk holds one open handle per
entry, and raising it OOM-killed the host before (see
`doc/08_tracking/bug/stage3_walk_retains_handle_per_entry_2026-09-25.md` and
the long comment at authority.shs:5263-5292). The documented workaround is
deleting regenerable caches (on the 2026-09-25 host, `build/c/` alone was
119k entries).

Resolution used 2026-11-11: run the lane in a fresh detached worktree
(`git worktree add ... --detach origin/release/1.0.0`), where HEAD+physical
entries are ~313k (clean-checkout measurement in the same comment) — under
the cap. Long-term fixes: bound the handle retention or exclude ignored
caches from the physical walk so the main checkout can bootstrap too.

## Related: mcp_stdio integration spec qualification gap

`test/02_integration/app/mcp_stdio_integration_spec.spl` needs a real
executable: `send_mcp` reads `SIMPLE_MCP_TEST_BINARY` (default
`bin/simple_mcp_server`) and spawns it through `cmd /d /v:off /s /c` with
stdin redirection. On this host:

- With the env var unset, 12/16 examples fail with
  `MCP executable and input paths must be nonempty` — consistent with the
  seed's `env_get` returning empty text (not nil) for unset vars, so the
  `?? "bin/simple_mcp_server"` fallback never fires under the Rust seed.
- With `SIMPLE_MCP_TEST_BINARY=bin\simple_mcp_server.cmd`, the spawn fails
  with `The network path was not found` (status=1) — the spec's minimal
  cmd quoting only accommodates a plain native `.exe`, exactly as its
  comment states: "Qualification supplies the actual receipt-bound native
  MCP executable."

So the spec's real pass requires the native MCP build (pending the
bootstrap's self-hosted compiler); the launchable guard
(`check-mcp-config-launchable.shs`) remains the green source of truth for
the source-mode servers in the meantime.
