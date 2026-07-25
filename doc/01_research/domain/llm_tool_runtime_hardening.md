# LLM Tool Runtime Hardening - Domain Research

Date: 2026-07-01

## OpenCode CLI

Source: https://opencode.ai/docs/cli/

Relevant current behavior:

- `opencode run` is the documented non-interactive command for automation.
- `run` supports `--session`, `--model`, `--format`, `--attach`, `--dir`, and
  `--auto`.
- `attach` connects a TUI to an already running backend server.
- OpenCode sessions are managed by `opencode session`.

Implication: a wrapper should build first-class OpenCode args instead of shell
snippets, and should manage local spawned processes by PID rather than emitting
ad hoc `kill` or `pkill` commands.

## vLLM

Source: https://docs.vllm.ai/en/stable/cli/serve/

Relevant current behavior:

- vLLM serve exposes `--tensor-parallel-size` / `-tp`.
- vLLM serve exposes `--data-parallel-size` / `-dp`.

Implication: vLLM command planning should keep vLLM's long option names for
readability and generated evidence.

## SGLang

Source: https://docs.sglang.io/docs/advanced_features/server_arguments

Relevant current behavior:

- SGLang server launch is `python -m sglang.launch_server`.
- tensor parallelism is configured with `--tp`.
- data parallelism is configured with `--dp`.
- static memory fraction can be tuned with `--mem-fraction-static`.

Implication: SGLang command planning should not copy vLLM's
`--data-parallel-size` spelling; it should emit SGLang-native `--dp`.
