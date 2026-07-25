# LLM Tool Runtime Hardening - Detail Design

Date: 2026-07-01

## OpenCode Wrapper

`build_opencode_args` returns documented OpenCode `run` arguments:

- `run`
- `--format json` by default
- optional `--model`, `--session`, `--attach`, `--auto`
- non-empty extra args
- prompt last

`opencode_cli_spawn` starts OpenCode through the process facade and returns the
PID. `opencode_cli_running_status` and `opencode_cli_kill` operate only on the
provided PID. `opencode_cli_kill` returns `invalid_pid` for `pid <= 0`.

`parse_opencode_response` extracts simple JSON string fields with a local
scanner. This deliberately avoids adding a dependency or a full JSON parser for
the current response fields.

## vLLM/SGLang Serve Planning

`llm_runtime_static_serve_plan` builds static metadata and command previews
without starting a server.

Backend-specific args:

- vLLM: `vllm serve`, `--host`, `--port`, `--tensor-parallel-size`,
  `--data-parallel-size`
- SGLang: `python -m sglang.launch_server`, `--model-path`, `--host`,
  `--port`, `--tp`, `--dp`, `--mem-fraction-static`

Sensitive paths and endpoints are redacted from previews while direct helper
args remain inspectable in unit tests.
