# Native `llm_caret` ignores `--config` `claude_cli.cli_path` and spawns the real `claude`

Status: verification-pending
Severity: P1 (native-only; a fixture-only spec reaches a real provider CLI)

## Root cause (2026-11-14, lane `work/caret-native-defects-20261114`)

A caret source bug, independent of the `text_to_bytes` defect.
`parse_config_text` (`src/app/llm_caret/config.spl`) wrapped
`trimmed.index_of(":")` in an untyped helper that pattern-matched it as an
Option:

```simple
fn _unwrap_idx_cfg(opt) -> i64:
    match opt:
        Some(i): return i
        nil: return -1
```

`text.index_of` returns a raw `i64` (`-1` on miss), not an Option
(`doc/07_guide/quick_reference/syntax_quick_reference.md`). With a typed
subject this is `error[SPL-PAT-001]`; the untyped parameter erased the type.
The interpreter leniently binds `i` to the integer; the native lane matches
`Some(i)` against the boxed integer and yields `3` for every input, hit or
miss. Single-file repro, native:

```
any_index_of=3      # unwrap_any("provider: x".index_of(":")), expected 8
any_missing=3       # unwrap_any(s.index_of("zz")), expected -1
typed_index_of=8
```

So every line was split at byte 3: `cli_path: X` became key `cli`, no key
matched, and `CLAUDE_CLI_PATH` kept its default `"claude"`.

Fix: use the `i64` directly in `config.spl` and in the same helper in
`server.spl` (`_extract_json_string`).

Not covered (compiler residual, not fixed here): the native lane neither
rejects nor falls through a `Some(i)` arm whose erased subject is a plain
integer; it binds `3`. The interpreter binds the integer. Both lanes accept a
program the typed checker rejects.
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
