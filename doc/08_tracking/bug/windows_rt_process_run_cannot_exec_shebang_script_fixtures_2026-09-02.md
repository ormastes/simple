# Windows: `rt_process_run` cannot execute a shebang script, so every `.shs` CLI fixture returns exit -1

- **Filed:** 2026-09-02
- **Status:** OPEN
- **Lane:** Windows host, LLM Caret suite triage
- **Impact:** the single dominant cause of RED in the caret suite on Windows

## Defect

`rt_process_run(cmd, args)` passes `cmd` to `CreateProcess`, which can only
launch a PE image. A POSIX shell script — the form every caret CLI fixture takes
(`test/fixtures/llm_caret/mock_claude_cli.shs`, shebang `#!/bin/sh`) — is not a
PE image, so the spawn fails and the runtime reports **exit code -1 with empty
stdout and empty stderr**. `src/app/llm_caret/claude_cli.spl:359,383` call
`rt_process_run(cli_path, args)` directly with the fixture path.

The provider layer turns that into the string `claude CLI exited with code -1`,
which is what the failing expectations quote.

## Measurement (2026-09-02, seed `bin/simple.exe` md5 `d52d770724a9f8797e98ac7819709ab9`)

Direct probe through the same extern the caret code uses:

```
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)
```

| invocation | code | stdout | stderr |
|---|---|---|---|
| `rt_process_run("cmd", ["/c", "echo hello"])` | **0** | `hello` | — |
| `rt_process_run("test/fixtures/llm_caret/mock_claude_cli.shs", ["--version"])` | **-1** | *(empty)* | *(empty)* |
| `rt_process_run("sh", ["test/fixtures/llm_caret/mock_claude_cli.shs", "--version"])` | **65** | *(empty)* | `expected json or stream-json output format` |

Row 1 proves `rt_process_run` itself works on Windows — this is not a general
spawn outage. Row 3 proves the fixture is correct and runs to completion when
routed through its interpreter. Only row 2, direct execution of the script,
fails, and it fails silently: no stderr explains why.

## Blast radius measured in the caret suite

137 caret spec files run as explicit files, interpreter mode, sequentially:
`1260 total, 1033 passed, 227 failed` across 42 files. Bucketing the failure
messages and counting assertion lines only (many failures print no `expected`
line at all): **25** failed assertions across **7** files quote the literal `-1`
signature — `claude_cli_spec`, `config_spec`, `provider_spec`, `tools_spec`,
`llm_caret_claude_cli_stream_spec`,
`llm_caret_claude_cli_full_parity_implementation_spec`, and the stale mirror
`test/unit/app/llm_caret/provider_spec`. A further **40** assertions compare
against an **empty** actual value, the expected downstream shape of a failed
spawn, though not independently proven to share this cause. Total `expected`
lines across the whole sweep: 105. Worst-hit files:
`claude_cli_spec.spl` 50/85 failed,
`provider_spec.spl` 9/42, `llm_caret_installed_claude_cli_spec.spl` 6/6,
`llm_caret_tui_pty_spec.spl` 10/10.

Every caret spec and every file under `src/app/llm_caret/` is **byte-identical
to `origin/main`** (`git diff --stat origin/main -- src/app/llm_caret test/…`
reports no changes), so none of this is introduced by current work.

## Fix shape

In the Windows branch of the process-spawn path, when `cmd` is not a launchable
image, read its first line; if it is a `#!` shebang, re-spawn as
`<interpreter> <cmd> <args…>`. Row 3 above shows that path already produces the
correct result. **Must be Windows-only** — the POSIX branch already works via
`execve` shebang handling and must not be touched.

## Overlap warning

This lives in `src/runtime` process spawn, the same area another session is
already working on for the Windows test-runner `process_run_observed_bounded`
defect. Coordinate before editing; do not land two competing spawn fixes.

## Class-(b) proof: identical on a pristine `origin/main` worktree

`origin/main` (`1b76db1d6c3`) was materialised into a separate worktree and the
same specs run there with the **same** binary (`bin/simple.exe`, md5
`d52d770724a9f8797e98ac7819709ab9`), same flags, repo-relative paths. The run
was confirmed to read the worktree's own sources (`…/main-wt/src/lib` appears in
its diagnostics, 25 occurrences), not the working checkout's:

| spec | working checkout | `origin/main` worktree |
|---|---|---|
| `test/01_unit/app/llm_caret/provider_spec.spl` | 42 total, 33 passed, 9 failed | 42 total, 33 passed, 9 failed |
| `test/01_unit/app/llm_caret/types_spec.spl` | 25 total, 24 passed, 1 failed | 25 total, 24 passed, 1 failed |
| `test/01_unit/app/llm_caret/chat_spec.spl` | 24 total, 0 passed, 24 failed | 24 total, 0 passed, 24 failed |

Byte-identical counts. Nothing in the current working tree contributes.

## Stale mirror trees are a separate, already-baselined bucket

Of the 227 failures, **57 across 6 files** are in the legacy mirror trees
`test/unit/**` and `test/system/**`, which are stale copies of the live
`test/01_unit/**` / `test/03_system/**` specs. Example:
`test/01_unit/app/llm_caret/json_helpers_spec.spl` runs **49 total, 49 passed,
0 failed**, while its mirror `test/unit/app/llm_caret/json_helpers_spec.spl`
runs **47 total, 7 passed, 40 failed** — an older API surface, not a defect.
`scripts/check/test_tree_divergence_baseline.txt` already carries 9 `llm_caret`
entries. The live trees account for the other **170 failures across 36 files**.
