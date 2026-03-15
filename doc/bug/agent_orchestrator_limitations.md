# Agent Orchestrator — Limitations

## 1. rt_file_read_text returns Option wrapper

**Description:** `rt_file_read_text()` returns `text?` (optional). When used directly
in assertions or print, the value displays as `Option::Some(content)` rather than
raw content.

**Workaround:** Use `?? ""` to unwrap: `val content = (rt_file_read_text(path)) ?? ""`

**Severity:** Low — cosmetic, easy workaround.

## 2. Command functions not unit-testable

**Description:** `_cmd_spawn`, `_cmd_result`, `_cmd_list` depend on `rt_env_get` and
`rt_process_run` which cannot be mocked in interpreter mode. Unit tests cover only
pure helper functions (_provider_binary, _build_args, _result_path, file round-trip).

**Workaround:** Manual integration testing via shell commands. All three commands
verified working end-to-end with real codex and gemini CLIs.

**Severity:** Medium — reduces automated coverage to ~60% of code paths.

## 3. Large prompts may exceed OS arg length limit

**Description:** Prompt file content is passed as a CLI argument to codex/gemini.
Very large documents (>2MB) could exceed the OS argument length limit.

**Workaround:** Split large documents or use shorter prompts. Future: pipe prompt
via stdin or write to temp file.

**Severity:** Low — most plan/design docs are well under 2MB.

## 4. Agent ID timestamp granularity

**Description:** Agent IDs use `date +%s` (second precision). Two spawns within the
same second would produce the same ID, overwriting the first result.

**Workaround:** Add a short delay between rapid successive spawns, or append a
random suffix in future versions.

**Severity:** Low — unlikely in practice (LLM calls take seconds to minutes).

## Related

- [Requirement](../requirement/agent_orchestrator.md)
- [Plan](../plan/agent_orchestrator.md)
