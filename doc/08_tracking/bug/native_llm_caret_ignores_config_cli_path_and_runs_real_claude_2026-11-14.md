# Native `llm_caret` ignores `--config` `claude_cli.cli_path` and spawns the real `claude`

Status: open
Severity: P1 (native-only; a fixture-only spec reaches a real provider CLI)
Found: 2026-11-14, lane `work/caret-native-knob-20261114`
Seed: `/c/dev/wt/seed-tip/simple.exe`, build-commit `97728d94d5f11890bac2e0a5e8d41ce65139047b`
Host: Windows 11, llvm-mingw 20260922 UCRT

## Symptom

`test/fixtures/llm_caret/mock_claude_cli.sdn` sets

```
claude_cli:
    cli_path: test/fixtures/llm_caret/mock_claude_cli.shs
```

Interpreted, caret runs that fixture. The native binary does not: it spawns
whatever `claude` is on `PATH`.

## Repro

```
E=build/nb/llm_caret.exe   # $SEED native-build src/app/llm_caret/main.spl -o $E
$E --config test/fixtures/llm_caret/mock_claude_cli.sdn --provider claude_cli --model sonnet --prompt fixture-error
```

| lane | exit | output |
|------|------|--------|
| interpreted (`bin/simple run src/app/llm_caret/main.spl ...`) | 1 | `ERROR: claude CLI exited with code 7: authorization failed for [REDACTED:anthropic_key:cret]` (fixture) |
| native, real `claude` on PATH | 0 | a real Claude Code reply about the prompt text (38-68 s per call) |
| native, `PATH=/usr/bin:/bin` (no `claude`) | 1 | `ERROR: claude CLI exited with code -1: process spawn failed` |

The third row is the discriminator: with no `claude` on PATH the native binary
fails to spawn, so it is asking for the bare default name, not the configured
`cli_path`.

Suite view, `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl`
with `LLM_CARET_NATIVE_BIN` set - `Results: 3 total, 2 passed, 1 failed`:

```
expected fixture-success ... to contain fixture-ok
expected 0 to equal 1
expected true to equal false
```

Interpreted: `3 total, 3 passed, 0 failed`.

## Safety note

That spec states "No real Claude process or API credential is used". Under
`LLM_CARET_NATIVE_BIN` this is currently false on a host with `claude`
installed: the single-shot and provider-error cases each start a real session.
Until this is fixed, run the native lane of that spec with `claude` off `PATH`.

## Not yet isolated

Whether the config file fails to load natively, loads but
`config_claude_cli_path()` returns "", or the module-level `RT_CLI_PATH`
assignment (`src/app/llm_caret/main.spl:460,1219,1273`) is lost. The
`--config` existence check (`main.spl:1340`) does run. Possibly downstream of
`native_text_to_bytes_for_loop_reads_packed_words_when_agent_workspace_linked_2026-11-14.md`
if the SDN reader walks bytes.

## Unblock condition

Row 2 of the table matches row 1, and the hardening spec passes 3/3 with
`LLM_CARET_NATIVE_BIN` set. No caret-side workaround was applied.
