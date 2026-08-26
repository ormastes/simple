# LLM Caret Cached Plain-CLI Hidden Command Qualification

**Executable spec:** `test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl`  
**Requirements:** REQ-LLM-CARET-HIDDEN-008, REQ-LLM-CARET-FULL-003  
**Evidence display:** links  
**Capture artifacts:** `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached/<case>/{command.txt,stdout.txt,stderr.txt,exit.txt,provenance.txt,combined.txt}`

## Execution status

This manual is synchronized to the executable SSpec, but has zero executed
scenarios in this refresh. Execution requires a cached Caret binary with an
adjacent provenance manifest that proves a matching pure-Simple self-hosted
runtime; a bootstrap compiler, source fallback, or credentialed provider does
not satisfy this contract.

## Visible scenarios

### should require the pinned cached artifact before hidden-command qualification

1. Load the cached Caret artifact.
2. Invoke the hidden command through plain CLI.
3. Check captured output and status.

The prerequisite gate verifies target, current source commit, artifact and
runtime SHA-256 values, `runtime=pure-simple-self-hosted`, `runtime_probe=pass`,
and `rust_seed_used=false` before any command runs.

### should reject canonical and alias hidden commands by default

1. Load the cached Caret artifact.
2. Invoke the hidden command through plain CLI.
3. Check captured output and status.

`/debug-tool-call` and `/debug_tool_call` must both return their respective
unknown-command messages with no tool-call execution when the feature flag is
unset.

### should admit canonical and alias hidden commands only when explicitly enabled

1. Load the cached Caret artifact.
2. Invoke the hidden command through plain CLI.
3. Check captured output and status.

With `LLM_CARET_ENABLE_HIDDEN_COMMANDS=1`, both spellings must emit the
sanitized `tool call id=call-1 name=Read input_bytes=27` result.

### should reject canonical and alias hidden commands when the flag is explicitly false

1. Load the cached Caret artifact.
2. Invoke the hidden command through plain CLI.
3. Check captured output and status.

`LLM_CARET_ENABLE_HIDDEN_COMMANDS=false` is an explicit denial, not an omitted
setting: canonical and alias forms both remain rejected.

### should reject canonical and alias disabled commands in plain non-TTY mode

1. Load the cached Caret artifact.
2. Invoke the hidden command through plain CLI.
3. Check captured output and status.

`/remote-setup` and `/remote_setup` remain disabled under all hidden-command
settings. Each case runs through a pipe with `TERM=dumb`; these are CLI capture
artifacts, not PTY or raster-screen evidence.
