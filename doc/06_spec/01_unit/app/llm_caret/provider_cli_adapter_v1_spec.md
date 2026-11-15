# Caret provider adapter planning scenarios

**AUTHORED_NOT_RUN.** Executable source:
`test/01_unit/app/llm_caret/provider_cli_adapter_v1_spec.spl`.
The scenarios exercise the real production decoder and planner. They construct
planning data, not installed/native capabilities. No agent task, auth mutation,
container command, Simple runtime or native fixture was executed by these specs.

1. **Codex Start and Resume.** Decode the locally observed `codex-cli 0.169.0`
   spelling as data. Plan Start with fixed JSONL output and a flag-like multiline
   prompt supplied on stdin using `-`. Plan Resume with the exact `exec resume`
   subcommand and explicit session. Check full argv, prompt bytes, output format
   and required external containment.
2. **Claude Resume.** Decode Claude Code 2.1.325. Place the exact session after
   `--resume`, preserve the fixed print/JSON contract, and put a flag-like prompt
   after the positional delimiter. Check argv, empty stdin and required external
   containment. The allowed verbose option does not permit an output override.
3. **Gemini and Kimi Resume.** Decode Gemini 0.68.0 and Kimi 2.5.3. Bind the prompt
   to its long-option value so flag-like text remains prompt data. Check Gemini's
   `--resume` and JSON contract separately from Kimi's `--session` and stream-JSON
   contract. Gemini accepts a full UUID and rejects prefix/name shortcuts.
   Both require genuine external containment; Kimi's headless default grants no
   execution authority and neither its yolo nor auto override is added.
4. **Unsupported inputs.** Reject a different Codex version, a family mismatch,
   unknown/empty provider aliases, forged mismatched version data and
   empty/latest/last/numeric/path/flag-like resume selectors. No fallback provider
   or latest session is selected.
5. **Override attempts.** Pass split and equals-spelled output, model, scope,
   session, config, auth/safety and permission overrides through the production
   option allowlist for every provider. Check rejection, including flag-like
   model values and session fields on Start. No shell is invoked.
6. **Authentication and interruption.** Check only the actual read-only Codex
   login-status and Claude auth-status command plans. Gemini/Kimi explicitly need
   external credential inspection metadata rather than a made-up status command.
   Interrupt contains no argv or PID and requires the existing contained control
   owner; it establishes no workload settlement or charge release.

These planning scenarios cover REQ-CARET-PROVIDER-001 through 004 and the neutral
intent portion of 005. Actual contained probes, complete output, image/scope
binding, fresh admission, CoreMux transport and settlement remain separate
required evidence under REQ-CARET-PROVIDER-005 through 008. Local research help
does not establish the CLI installed inside a container.
