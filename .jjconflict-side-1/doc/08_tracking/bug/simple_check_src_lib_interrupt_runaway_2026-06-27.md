# simple check src/lib continues after interrupt

Status: guarded in source, pending release-binary verification
Severity: P2 resource/runaway
Date: 2026-06-27

## Symptom

`release/x86_64-unknown-linux-gnu/simple check src/lib` continued checking files after Ctrl-C. The process printed the shared interrupt-handler message but kept emitting diagnostics for additional files. A second Ctrl-C did not stop it promptly, so the process group had to be terminated externally.

## Evidence

- Command: `release/x86_64-unknown-linux-gnu/simple check src/lib`
- Context: broad verification after the web renderer `flex-flow` slice; the touched renderer file had already passed a targeted check.
- Observed output: `^C Interrupt received - stopping execution...`
- Actual behavior: the check loop continued through many unrelated `src/lib` files after the interrupt message.
- Recovery: process group for PID `1430932` was terminated; final exit status was `143`.

## Impact

Broad check commands can keep running after a user or agent aborts them, flooding logs and consuming resources. This is a concrete runaway-session risk because repeated output after abort can grow context and obscure the original verification result.

## Expected Behavior

The first interrupt should stop the multi-file check before starting another file and exit with an interrupted status. A second interrupt should not be needed for normal broad-check cancellation.

## Suspected Owner

- `src/compiler_rust/driver/src/cli/check.rs`
- `src/compiler_rust/compiler/src/interpreter_state.rs`

## Fix

Added cooperative checks of the existing `simple_compiler::interpreter::is_interrupted()` flag before and after each file in `run_check`. Interrupted runs now stop the file loop and return exit code `130`, with a short partial-progress message.

## Follow-Up

After the release binary is rebuilt, verify with a long directory check in an interactive shell by sending SIGINT during the file loop. Do not rerun this as an unattended broad check in Codex.
