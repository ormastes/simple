# Explicit Codex task prompt transport

Status: AUTHORED_NOT_RUN, DATA planning only. Existing adapter8 behavior remains
unchanged. `plan_provider_cli_codex_prompt_mode_v1` accepts only Codex 0.169.0
Start/Resume DATA and an explicit Stdin or Argv mode. It consumes the existing
production planner, preserving model/session/extra-option/output restrictions.

Stdin keeps its original argv sentinel and stdin payload. Argv replaces the final
sentinel with the documented option terminator followed by the exact prompt as
one argument. No shell string, temporary file, raw input write or silent fallback
exists. Literal `-` refuses Argv because the provider still treats it as stdin.
This profile limits prompt UTF-8 to 4096 bytes and logical argv UTF-8 to 8192
bytes; existing native provider command-line bounds remain independently enforced.
The outer DATA record reports mode/counts and the required closed-stdin/non-TTY
profile. That requirement boolean is not an observed fact or authority.

Actual Argv task execution must consume the real contained selection and a
separate versioned input-configuration observation in the SAME genuine Host
current-create/pre-first-start transaction. It must observe OpenStdin=false and
Tty=false, with explicit actual StdinOnce recorded/digest-bound. Missing fields
refuse. The original config-V1 wire/digest stays unchanged. This producer and
input-constraint forwarding are still being coordinated; the pure mode has no
effect port and does not yet enable a task launch.

Argument mode exposes prompt bytes to process/container inspection and retained
signed request metadata. It is an explicit selected transport with bounded values.
No prompt is logged here. Interactive CoreMux delivery, controlled EOF, credential
delivery, Resume custody, workload interruption and settlement remain separate.

The production planner spec checks flag-like/subcommand-like prompts, exact argv
and output safety, unchanged stdin, exact resume selector DATA, UTF-8 byte bounds,
sentinel rejection and unknown family/version/action. Tests are AUTHORED_NOT_RUN;
no task, auth, engine or compiler command was executed.
