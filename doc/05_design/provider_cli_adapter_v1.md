# Versioned Caret provider CLI planning

Status: **DATA IMPLEMENTATION AUTHORED_NOT_RUN**. Local read-only CLI research
ran successfully; it is not a Simple runtime, container-installed program,
vendor trust, authentication, containment or admission qualification. The
contained observation/selection/consumer layer is still required. This design
does not declare the full provider feature done.

The two new app modules separate provider/action/plan data from exact-version
decoding and production argv planning. Existing `AgentLaunchPlan`, legacy local
launchers, `main.spl`, source leases and runtime-provider owners are unchanged.
A caller can construct data values; no such value constructs an installed
capability. The eventual owned consumer must plan again from its own actual
container probe receipt instead of executing a caller-supplied argv DTO.

| Observed local version | Start / resume | Fixed output |
|---|---|---|
| Codex 0.169.0 | `exec`; resume uses `exec resume` and an exact session | `--json` JSONL; prompt supplied on stdin using documented `-` |
| Claude Code 2.1.325 | `--print`; resume adds `--resume` | `--output-format json`; explicit positional delimiter protects the prompt |
| Gemini CLI 0.68.0 | `--prompt`; resume adds `--resume` | `--output-format json`; prompt bound to the long-option value |
| Kimi 2.5.3 | `--prompt`; resume adds `--session` | `--output-format stream-json`; prompt bound to the long-option value |

Unknown providers, other versions and family/version mismatch are rejected.
Model values cannot be flag-like or contain whitespace/control bytes. Resume
requires a bounded explicit session identifier; no picker, latest/last shortcut,
numeric project index, path or empty selector is substituted.
Gemini 0.68.0 specifically requires a full UUID in this adapter; its pinned
source compares the full stored session ID and supplies no prefix match.
Session ownership and project/scope authorization still belong to the actual
contained consumer.
All arguments are arrays; no shell command is generated or task text interpolated
into a shell. Codex stdin bytes remain task data, not process arguments.

The extra-option allowlist is small and typed: Claude's bare `--verbose`, and
Codex Start's color-never spelling. Resume does not borrow Codex Start options.
Other options are refused, including split and equals spellings of output,
model, session, auth, config, directory, executor and safety/permission overrides.
Claude JSON is a document contract rather than a claim that verbose output must
always be a single object. No adapter adds a bypass/yolo/auto or auth-mutating
flag.

Every provider's Start/Resume data plan requires **genuine external containment**.
Kimi 2.5.3 distinguishes its yolo and auto modes and rejects those explicit
overrides together with prompt mode. The adapter preserves its existing
headless default; that CLI policy is not containment. The requirement cannot be
satisfied by flipping a DTO boolean or holding a bare host executable pin. All
new task execution, including the other providers, must follow the user's
Windows Docker/Linux Podman Simple Container API requirement.

AuthInspect plans only actual read-only CLI commands: Codex `login status` and
Claude `auth status --json`. Gemini and Kimi return explicit external-credential
inspection metadata rather than a fictional status subcommand. Gemini's documented
existing login/API-key/Vertex mechanisms are named without reading, printing,
writing or exporting credential values. A status response is not a reusable
authentication or spend authority. No login, logout, browser flow, agent task or
billing mutation was run during research.

Interrupt is a neutral **existing owned invocation control intent**, with no
argv or PID. The contained consumer must use the actual common container control
owner or CoreMux's authorized terminal input. Canceling a local probe/transport
does not cancel its container or settle work; signal/input success never releases
charge or substitutes for actual workload settlement.

## Actual observation and consumer boundary

Local `OwnedExecutablePin` can bind read-only ELF probes to the same actual
snapshot, but no new host task path is permitted. The installed Gemini entry is
a JavaScript bundle: a Node ELF pin alone does not bind its script/assets. Host
version/help observations do not prove the version installed inside a container.
The server75 stdin-command result's echoed expected digest is likewise not an
executed-image attestation.

Existing `simple_container_read_v2(owner, "logs", original_request)` is a candidate
bounded primary-log seam by exact native ID, without line-tail filtering.
Actual EOF/truncation/complete-capture evidence is not currently preserved by
the common wrapper and must be supplied before help completeness can be claimed.
Actual `wait` and `inspect` ports exist. This is a smaller candidate
for short admitted version/help primary probes than adding detached exec output
or relying on attachment after a fast process has exited. Interactive task IO
continues through existing primary terminal/CoreMux owners.

The actual selection producer must retain real common execution/admission and
output/cleanup owners, correlate exact original request/effective probe argv,
observe successful completion and full bounded output, and bind the immutable
installed image, CLI filesystem, provider generation and scope. Public runtime
IDs, request image strings and caller JSON are not that producer. Existing Linux
generic inspect deliberately returns only normalized identity/status and does
not expose image/rootfs/mount provenance; a fixed actual image/filesystem
observation port is needed before reusable selection can be admitted. Mounts,
overlays or environment/interpreter assets that can replace the probed program
must invalidate reuse. Fresh tasks require fresh genuine admission on that same
observed image/scope binding. Missing lower evidence remains explicit and never
falls back to a host launcher.

## Research and verification

Actual local --version and --help probes were run sequentially with one CPU
affinity and finite time/output limits. Additional read-only subhelp confirmed
Codex exec/resume/login-status and Claude auth-status shapes. Kimi login/session/
provider subhelp was inspected; the login command itself was never run. Raw
research outputs are in `/tmp/caret-provider-cli-probes-20261115-sol`. These
ordinary research subprocesses do not mint a retained native selection receipt.

Official primary references consulted alongside installed help:

- [OpenAI CLI command documentation](https://learn.chatgpt.com/docs/developer-commands?surface=cli)
- [Claude Code CLI reference](https://code.claude.com/docs/en/cli-reference)
- [Gemini CLI reference](https://geminicli.com/docs/cli/cli-reference/)
- [Gemini authentication](https://geminicli.com/docs/get-started/authentication/)
- [Kimi command reference](https://www.kimi.com/code/docs/en/kimi-code-cli/reference/kimi-command)

Production planner specs cover exact argv for all four families; hostile prompt
boundaries; version/family and resume-selector rejection; option override attacks;
real read-only auth shapes; Kimi containment marking and neutral interrupt intent.
Every provider task plan's containment requirement is asserted.
They remain **NOT_RUN** because there is no admitted self-hosted runtime here.
Contained probe/image/interactive/task fixtures are not claimed covered or
verified by this data-only test slice.
