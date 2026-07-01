# LLM Tool Runtime Hardening - Architecture

Date: 2026-07-01

## Decision

Keep this lane as static command planning plus explicit process primitives.
Do not introduce a process registry or supervisor until requirements select it.

## Components

- `llm_caret/opencode_cli.spl`: OpenCode-specific arg building, response
  parsing, spawn/status/kill wrapper.
- `app.io.mod`: existing process facade for run/spawn/status/kill.
- `llm_runtime/serve_plan.spl`: static vLLM/SGLang command metadata.
- `llm_runtime/manifest.spl`: backend and parallelism inputs.

## Invariants

- OpenCode prompts remain last in `run` args.
- OpenCode attach/session/model/format flags are structured args, not shell.
- Kill uses a PID plus the process facade; wrapper rejects invalid PIDs.
- vLLM uses vLLM-native `--tensor-parallel-size` and
  `--data-parallel-size`.
- SGLang uses SGLang-native `--tp`, `--dp`, and
  `--mem-fraction-static`.
- Static plans redact sensitive paths/endpoints and do not launch servers.

## Verification

- Unit specs cover arg construction, PID kill guard, JSON parsing, redaction,
  and backend-specific serve flags.
- Optional live/runtime gates remain future work until requirements select them.
