# LLM Caret CLI and TUI Hardening — System Test and Traceability Plan

Date: 2026-07-24

## Purpose

This is the single coordinating test plan for hardening LLM Caret in this
order:

1. deterministic CLI behavior;
2. interactive TUI behavior and visible evidence;
3. hidden, disabled, preview, and feature-flagged behavior;
4. row-level Claude parity.

It does not claim that all Claude Code behavior is implemented or passing.
It distinguishes current-tree evidence from the historical upstream snapshot
used to generate the full-parity matrices.

## Evidence Authority and Staleness

| Evidence | Current finding | Authority |
|---|---|---|
| `src/app/llm_caret/*.spl` | 25 direct Caret files; 7,278 LOC; 496 declarations | Finalized working-tree inventory; checker rerun still required |
| `doc/09_report/llm_caret_claude_cli_traceability.md` | Maps all 25 direct files and 7,278 current LOC | Current static mapping; not executable evidence |
| `scripts/check/check-llm-caret-claude-cli-trace.shs` | 25/25 files (100%); 7,278/7,278 LOC (100%); 496/496 file-qualified symbols; `STATUS: PASS` | Current computed gate |
| Full self-hosted CLI bootstrap | Stage 3 built; Stage 4 full-CLI native build was killed by signal 9; no candidate deployed | Current executable-test blocker; do not retry in this session |
| Cached Caret live-PTY qualification | Checker/spec/manual implemented; `--case prerequisites` requires a matching adjacent provenance manifest and fails closed when the cached artifact is absent | Current executable-test blocker; no live PASS or skipped prerequisite |
| `tmp/claude/claude-code-main/src` | Missing | Current-tree evidence |
| Full-parity feature matrix | 599 rows, 1,902 historical source files, 512,685 historical LOC | Snapshot-derived evidence; cannot be refreshed against upstream now |
| Full-parity file matrix | 1,902 rows | Snapshot-derived evidence |
| Full-parity symbol matrix | 14,119 rows | Snapshot-derived evidence |
| Full-parity implementation gate | 745 mapped targets exist; 1,157 missing; 599/1,902 targets reach 80% source LOC | Current target tree checked against stale snapshot rows |
| Full-parity primary tests | 174/1,902 mapped primary test paths exist | Current test tree checked against stale snapshot rows |
| Claude-full system specs | 346 executable specs | Current-tree evidence |
| Generated Claude-full manuals | 55 correctly mirrored, 150 under stale `doc/06_spec/test/...`, 141 missing | Current-tree evidence |

The missing upstream tree makes claims such as “every current Claude feature”
or “no new Claude function is missing” assumptions, not evidence. Restore a
pinned, provenance-recorded upstream snapshot before regenerating any matrix.
Until then, preserve the matrices as historical evidence and do not delete or
rewrite their rows.

## Frozen Modern SSpec Contract

New or substantially revised hardening specs must use these names verbatim.

| Kind | Frozen names |
|---|---|
| Interfaces | `CaretCliFeatureCase`, `CaretTuiFeatureCase`, `CaretHiddenFeatureCase` |
| CLI helpers | `setup_cli_fixture`, `run_cli_case`, `check_cli_result` |
| Installed CLI helper | `probe_current_claude_cli` |
| TUI helpers | `setup_tui_fixture`, `run_tui_action`, `check_tui_snapshot` |
| Hidden helper | `setup_hidden_feature_fixture`, `check_hidden_feature_gate` |
| CLI steps | `Load the accepted Claude feature map`; `Invoke the caret CLI provider`; `Check the structured CLI response` |
| Installed CLI steps | `Load the accepted Claude feature map`; `Invoke the installed Claude CLI with no prompt or provider credentials`; `Check the structured CLI response` |
| TUI steps | `Open the caret TUI`; `Send a prompt through the visible input`; `Check transcript and status` |
| Hidden steps | `Enable the hidden-feature fixture`; `Check the hidden-feature gate` |

Every placeholder helper must fail explicitly with `assert(false)` or
`fail(...)`. No silent helper, `pass_todo`, tautological assertion, or skipped
scenario counts as coverage.

## Requirement Traceability

| Requirement | Implementation evidence | Current tests | Surface/status | Required hardening |
|---|---|---|---|---|
| REQ-LLM-CARET-CLAUDE-TRACE-001 | Historical Claude source references in `doc/09_report/llm_caret_claude_cli_traceability.md` | `llm_caret_claude_cli_traceability_spec.spl` | CLI / FAIL: upstream tree missing | Restore pinned source and regenerate feature groups |
| REQ-LLM-CARET-CLAUDE-TRACE-002 | 25 direct files under `src/app/llm_caret` | Checker maps all 25 files and 7,278 LOC | CLI/TUI / PASS | Keep rows synchronized when direct files move or split |
| REQ-LLM-CARET-CLAUDE-TRACE-003 | `check-llm-caret-claude-cli-trace.shs` | Traceability system spec | CLI / PASS: 100% files, 100% LOC, exact file-qualified symbols | Keep the current filesystem inventory synchronized |
| REQ-LLM-CARET-CLAUDE-TRACE-004 | Checker emits named counters and status | Traceability system spec | CLI / BLOCKED at runner mismatch in parent run | Modernize with frozen steps and assert exit code plus report fields |
| REQ-LLM-CARET-CLAUDE-TRACE-005 | File-qualified Simple symbol inventory | Checker proves 496/496 current declarations | CLI / PASS | Regenerate symbol rows and require zero missing/stale symbols |
| REQ-LLM-CARET-CLI-HARDEN-006 | Production CLI/provider/session/tool declarations plus the installed Claude executable's offline argument surface | Direct production unit specs and CLI process/contract specs; `llm_caret_installed_claude_cli_spec.spl` is supplemental environmental compatibility evidence | CLI / static-complete, execution blocked | Execute the installed offline probe once, then execute Caret on the qualified self-hosted runtime and cached wrapper |
| REQ-LLM-CARET-TUI-HARDEN-007 | `CaretIo`, `caret_chat`, and TUI/plain loops | Runtime component spec plus `llm_caret_tui_pty_spec.spl` routing/lifecycle/raw-rejection scenarios | TUI / designed fail-closed; live execution blocked | Require PTY PASS and pre/post mode plus cursor/screen restoration artifacts |
| REQ-LLM-CARET-HIDDEN-008 | Production hidden command admission | `llm_caret_tui_hidden_feature_spec.spl` plus the production-derived all-record matrix in `root_commands_registry_spec.spl` | Hidden / component and registry coverage, execution blocked; no root Caret CLI/TUI invocation proof | Execute default/enabled/disabled cases without credentials and retain the separate process-invocation gap |
| REQ-LLM-CARET-TUI-HARDEN-009 | Injected `CaretIo` frame/read/loop boundary | Runtime component spec plus PTY UTF-8/edit/navigation/geometry and modeled EOF scenarios | TUI / component designed; live execution blocked | Execute component scenarios and retained live capture on a cached artifact |
| REQ-LLM-CARET-FULL-001..003 | Feature/file/symbol TSV matrices | Full-parity inventory/plan gate | CLI/TUI / STALE | Re-extract only from restored pinned upstream |
| REQ-LLM-CARET-FULL-004 | 745/1,902 target files exist | Implementation gate plus row specs | All / FAIL | Zero missing implementation and test rows |
| REQ-LLM-CARET-FULL-005 | File matrix LOC thresholds | Implementation checker | All / FAIL: 599/1,902 at 80% | Prefer behavioral proof when an approved architecture replaces LOC parity |
| REQ-LLM-CARET-FULL-006 | No feature is marked out of scope in matrices | Plan checker | All / unproved | Keep all rows; phase work without declaring skipped rows complete |
| REQ-LLM-CARET-FULL-007 | Historical progress counters | Implementation checker | All / FAIL: current count is 599/1,902, not the old 551/1,884 baseline | Report fresh counters on every completion claim |
| NFR-LLM-CARET-TRACE-001..004 | Offline shell checker and MDSOC boundary | Traceability spec | CLI / partly covered | Keep deterministic; remove hardcoded report assumptions |
| NFR-LLM-CARET-TUI-005..007 | Simple-only capability boundary, cached real PTY, one-size-snapshot bounded teardown | Runtime component spec and `check-llm-caret-tui-pty.shs` | TUI / static-complete, execution blocked | No leaf externs, source fallback, paid provider, retry, polling, or prerequisite skip |
| NFR-LLM-CARET-FULL-001..005 | `claude_full` capsule and matrices | Distributed Claude-full specs | All / incomplete | Add facade, performance, observability, invalidation, and row-test evidence |

## Caret Feature-to-Test Map

| Feature | Implementation | Unit/integration evidence | System evidence | Surface/status |
|---|---|---|---|---|
| CLI argument parsing, help, and production wrapper | `main.spl`, `bin/caret` | `main_spec.spl` | `llm_caret_cli_hardening_spec.spl` has four source-process cases plus cached-wrapper selection/rejection | CLI / designed process evidence; execution blocked |
| Installed Claude CLI argument compatibility | installed `claude` executable plus `claude_cli.spl` argument builder assumptions | `claude_cli_spec.spl` | `llm_caret_installed_claude_cli_spec.spl` has five bounded, credential-free offline cases for path/hash/version/help/missing-input/removed-option behavior | CLI / static-complete; checker execution pending; does not prove provider or session behavior |
| One-shot prompt and structured response | `main.spl`, `provider.spl` | `main_spec.spl`, `provider_spec.spl` | `llm_caret_interfaces_spec.spl` calls provider functions only | CLI / no process evidence |
| Claude argv: model, system, resume, limits, stream, schema, tools, verbose, extras | `claude_cli.spl` | `claude_cli_spec.spl` | Live specs are credentialed and opt-in | CLI / deterministic unit coverage; no wrapper launch |
| Provider selection and config | `provider.spl`, `config.spl` | `provider_spec.spl`, `config_spec.spl` | None | CLI / unit-only |
| Tool loop and permission policy | `chat.spl`, `tools.spl`, `main.spl` | `tools_spec.spl`, `main_spec.spl` | No CLI fixture proves deny/allow and exit/output contract | CLI / unit-only |
| Session save/list/resume | `session.spl`, `main.spl`, `chat_tui.spl` | `session_spec.spl`, `chat_tui_spec.spl` | Live resume uses real Claude; no offline process scenario | CLI/TUI / unit plus opt-in live |
| Server mode and request guards | `server.spl`, `main.spl` | `main_spec.spl`, `server_spec.spl` | None launches `--server` | CLI / unit-only |
| TUI selection, transcript, markdown, scroll, slash dispatch | `chat_tui.spl`, `tui_input.spl`, `tui_io.spl` | `chat_tui_spec.spl`, `chat_tui_input_spec.spl` | Component transitions in `llm_caret_tui_hidden_feature_spec.spl`; real cached-wrapper PTY lifecycle in `llm_caret_tui_pty_spec.spl` through `check-llm-caret-tui-pty.shs` | TUI / component proof present; live checker is fail-closed and still needs execution on a qualified cached artifact |
| `/help`, `/exit`, `/new`, `/model`, `/provider`, `/sessions`, `/resume` | `chat_tui.spl` | `chat_tui_spec.spl` | TUI hidden-feature spec drives provider/resume/new through `run_chat_tui_submission` | TUI / component dispatch; no live terminal |
| CLI/TUI/GUI shared dummy-provider seam | `provider.spl`, `interface_text.spl`, GUI modules | Core unit specs | `llm_caret_interfaces_spec.spl` | All / no modern steps or visible TUI evidence |
| Live Claude responses, tokens, model, system prompt, resume | `claude_cli.spl` | Parser/argv unit specs | `llm_caret_live_spec.spl`, `llm_caret_live_comprehensive_spec.spl` | CLI / opt-in; comprehensive spec contains three skip helpers |

## Historical Full-Parity Phase Map

These counts describe historical matrix rows, not verified current Claude.

| Phase | File rows | Targets present | Primary tests present | Surface |
|---|---:|---:|---:|---|
| P1 core CLI runtime | 62 | 34 | 22 | CLI |
| P2 tools and slash commands | 393 | 234 | 12 | CLI/TUI |
| P3 terminal UI | 615 | 274 | 30 | TUI |
| P4 remote bridge and server | 40 | 35 | 20 | CLI/hidden/remote |
| P5 services and extensibility | 172 | 17 | 17 | CLI/hidden |
| P6 support utilities and hardening | 620 | 151 | 73 | Shared |

The 346 existing Claude-full system specs exceed the 174 matrix paths because
many tests are aggregated, renamed, or not referenced by the historical
`primary_tests` cells. Coverage is not inferred from spec count.

## Hidden and Feature-Flag Map

| Hidden/gated feature | Implementation | Existing spec | Current evidence/gap |
|---|---|---|---|
| Hidden `/debug-tool-call`; disabled `/remote-setup` | `claude_full/commands.spl` | `root_commands_registry_spec.spl` | Registry-derived matrix covers every canonical/slash/alias identity, default and enabled admission, visibility, and non-vacuous hidden/disabled rows; not invoked through caret CLI/TUI |
| Hidden disabled stub commands: ant-trace, env, bughunter, issue, onboarding, share, summary, teleport, break-cache, ctx-viz, good-claude, mock-limits, oauth-refresh, perf-issue | command index capsules | `ant-trace/index_spec.spl`, `env/index_spec.spl`, `stub_commands_spec.spl`, `more_stub_commands_spec.spl` | Metadata covered; aggregate inventory is hand-maintained and can miss new stubs |
| Fast mode research preview | `commands/fast/index.spl`, `commands/fast/fast.spl` | `fast_command_spec.spl` | Enable/hidden/toggle covered at function level; no CLI/TUI visibility capture |
| Remote-control/bridge entitlement, profile, version, env-less and CCR mirror gates | `bridge/bridgeEnabled.spl`, bridge command capsules | `bridge_small_helpers_spec.spl`, `bridge_command_spec.spl` | Rich helper coverage; no offline root CLI/TUI gate scenario |
| Extra usage interactive/noninteractive visibility | `commands/extra-usage/index.spl` | `extra_usage_command_spec.spl` | Function coverage; no process-mode selection evidence |
| Hidden remote review command | `commands/review/reviewRemote.spl` | `review_remote_spec.spl` | Metadata covered only |
| Todo/Tasks V2 flag and hidden-empty behavior | `hooks/useTasksV2.spl` | `useTasksV2_spec.spl` | Store behavior covered; enabling flag and visible TUI transition not covered |
| New init prompt ANT/env gate | `commands/init.spl` | `init_commands_spec.spl` | Function combinations covered; no command invocation evidence |
| Experimental beta disable and agent teams environment keys | `utils/managedEnvConstants.spl` | `managed_env_constants_spec.spl` plus mirrored manual | Exact safe-list membership and non-provider-managed classification covered; execution blocked |
| Hidden model-visible meta messages | bridge helper capsule | `bridge_small_helpers_spec.spl` | Named inventory covered; must remain distinct from user-visible hidden commands |

The hardening hidden-feature spec must derive its case inventory from one
accepted map and assert, for every case: default state, enabling inputs,
visibility, direct lookup/invocation policy, disabled reason, and absence of
state mutation when rejected.

## Modern SSpec Gaps and Target Specs

Current relevant system-test inventory has 355 specs; 277 use `step("...")`,
5 carry a REQ identifier, and 3 contain capture/evidence markers.
No placeholder tautologies or legacy Given/When/Then helpers were found, but
absence of placeholders does not prove behavioral coverage.

Current focused executable specs:

| Executable spec | Generated manual | Required proof |
|---|---|---|
| `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.md` | Three scenarios: four source-process cases plus cached-wrapper selection and invalid-override rejection; current runner execution remains blocked |
| `test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md` | Five bounded offline compatibility scenarios record installed path/version/hash and validate help, missing-input rejection, and removed-option rejection with no submitted prompt or inherited provider credentials |
| `test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl` | `doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.md` | Eight deterministic CLI/parser/provider/state scenarios with complete folded source; current runner execution remains blocked |
| `test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.md` | Nine TUI/hidden component scenarios, including Unicode raw-line reduction; expected live capture remains unexecuted |
| `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.md` | Five fail-closed process scenarios: cached/offline prerequisites, forced/auto/piped routing, modeled teardown, UTF-8/edit/geometry, and raw-entry rejection before ANSI mutation |
| `test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.md` | Five scenarios, including one registry-derived exhaustive hidden/disabled/admission matrix that cannot silently omit a newly registered root command |

Every relevant REQ needs at least a happy, edge, and error/rejection scenario.
The CLI fixture must use stdlib/facade process APIs, never local `rt_*`
externs. The TUI fixture must use the repository UI access protocol when the
surface exposes it; screenshot-only evidence is insufficient.

## Scenario and Evidence Policy

- CLI manuals display the three frozen CLI steps and a compact `exec`/`text`
  capture; setup and parsing details are folded.
- The installed-Claude manual uses the three frozen installed-CLI steps, links
  raw stdout/stderr/exit/provenance artifacts, and explicitly excludes provider,
  authentication, resume, network, billing, and model-quality claims.
- TUI manuals display the three frozen TUI steps and embed a compact TUI
  capture under
  `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_hardening/`.
- Live-terminal manuals link the complete `script(1)` typescripts, driver logs,
  input bytes, pre/post `stty` modes, and geometry under
  `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/`.
  A missing cached artifact, adjacent provenance manifest, `script(1)`,
  `stty`, `pgrep`, SHA-256 utility, marker, or restoration row is a failure,
  never a skip. Each child has one fixed 20-second watchdog and no retry or
  polling loop. On timeout the watchdog freezes and recursively enumerates the
  `script`/runner/Caret child tree with `pgrep -P`, then terminates every
  captured PID. If the timeout marker is present, the parent waits for TERM,
  CONT, delayed KILL, and a teardown-complete marker before returning. This is
  bounded recursive teardown evidence, not a general process-tree proof.
- Hidden-feature manuals display both frozen hidden steps and the accepted case
  matrix; repetitive rows may fold, but rejected-state evidence remains visible.
- Use `# @evidence-display: embed_tui`. Capture remains off outside the
  scenarios that need it.
- The live specs remain supplemental. They cannot substitute for deterministic
  dummy/fake-backed acceptance and may not silently pass when credentials or
  long-live mode are absent.
- Fix the live-spec run comments that still name `test/system/...`; the
  executable path is `test/03_system/tools/llm/...`.
- Replace `_skip_long_live` placeholder passes with an explicit opt-in suite
  boundary or real scenarios; skipped completion is not release evidence.

## Cached Caret Artifact and Provenance Contract

The live checker selects the first executable repository-cached Caret artifact,
then requires an adjacent `${artifact}.provenance` file. It does not search for
a second artifact after selecting an executable whose provenance is missing or
invalid. The manifest is line-oriented `key=value` text with exactly one
nonempty value for each required key:

```text
source_commit=<40-or-64-lowercase-hex-commit>
binary_sha256=<64-lowercase-hex>
runtime_sha256=<64-lowercase-hex>
runtime_path=bin/release/<target>/simple
target=<canonical-host-target>
```

The checker:

1. selects `shasum -a 256` or `sha256sum`, failing if neither exists;
2. verifies `binary_sha256` against the selected executable;
3. requires a clean committed tree, then verifies `source_commit` against Git
   `HEAD`, or against jj `@-` when the jj `@` working-copy commit is empty;
4. verifies `target` equals the detected host architecture, OS, and Linux ABI;
5. requires `runtime_path` to name `bin/release/<target>/simple`, rehashes that
   executable, and verifies `runtime_sha256`;
6. exports `SIMPLE_CARET_NATIVE` as that exact verified artifact before
   invoking `bin/caret`, with source fallback disabled.

Live PTY driving is currently qualified only for Darwin `script(1)` and
util-linux `script(1)`. FreeBSD, OpenBSD, NetBSD, and other variants fail closed
until their exact harmless invocation syntax has an executable capability gate;
their target triples below remain build-manifest identities, not PTY PASS
claims.

After the future full native build succeeds, create the manifest immediately
from the same clean, committed working copy. These commands are the canonical
build-and-manifest sequence:

```bash
case "$(uname -s):$(uname -m)" in
  Darwin:arm64|Darwin:aarch64) target=aarch64-apple-darwin ;;
  Darwin:x86_64|Darwin:amd64) target=x86_64-apple-darwin ;;
  Linux:arm64|Linux:aarch64) architecture=aarch64 ;;
  Linux:x86_64|Linux:amd64) architecture=x86_64 ;;
  FreeBSD:arm64|FreeBSD:aarch64) target=aarch64-unknown-freebsd ;;
  FreeBSD:x86_64|FreeBSD:amd64) target=x86_64-unknown-freebsd ;;
  OpenBSD:arm64|OpenBSD:aarch64) target=aarch64-unknown-openbsd ;;
  OpenBSD:x86_64|OpenBSD:amd64) target=x86_64-unknown-openbsd ;;
  NetBSD:arm64|NetBSD:aarch64) target=aarch64-unknown-netbsd ;;
  NetBSD:x86_64|NetBSD:amd64) target=x86_64-unknown-netbsd ;;
  *) exit 1 ;;
esac
if [ "$(uname -s)" = Linux ]; then
  if getconf GNU_LIBC_VERSION >/dev/null 2>&1; then
    target="${architecture}-unknown-linux-gnu"
  elif ldd --version 2>&1 | grep -i -F musl >/dev/null 2>&1; then
    target="${architecture}-unknown-linux-musl"
  else
    exit 1
  fi
fi

runtime="bin/release/${target}/simple"
artifact="build/bootstrap/caret-package/caret"
test -x "${runtime}"
if test -e .jj; then
  test "$(jj log -r @ --no-graph -T 'if(empty, "true\n", "false\n")')" = true
  source_commit=$(jj log -r '@-' --no-graph -T 'commit_id ++ "\n"')
elif git rev-parse --verify HEAD >/dev/null 2>&1; then
  test -z "$(git status --porcelain)"
  source_commit=$(git rev-parse --verify HEAD)
else
  exit 1
fi
mkdir -p "$(dirname "${artifact}")"
"${runtime}" native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/llm_caret/main.spl --strip \
  --output "${artifact}"
test -x "${artifact}"

hash_file() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    return 1
  fi
}
binary_sha256=$(hash_file "${artifact}") || exit 1
runtime_sha256=$(hash_file "${runtime}") || exit 1
{
  printf 'source_commit=%s\n' "${source_commit}"
  printf 'binary_sha256=%s\n' "${binary_sha256}"
  printf 'runtime_sha256=%s\n' "${runtime_sha256}"
  printf 'runtime_path=%s\n' "${runtime}"
  printf 'target=%s\n' "${target}"
} >"${artifact}.provenance"
```

Do not copy a manifest from another artifact, edit a hash to satisfy the
checker, build from uncommitted source, or retain a sidecar after replacing its
binary. The subsequent `--case prerequisites` run must print the selected
artifact, manifest path, matched source check, binary hash, runtime path/hash,
and target
before any PTY case is accepted.

## Execution Order and Exact Commands

Run each gate once after its inputs change; stop after convergence.

```bash
sh scripts/check/check-llm-caret-claude-cli-trace.shs
sh scripts/check/check-llm-caret-full-parity-plan.shs
sh scripts/check/check-llm-caret-full-parity-implementation.shs
sh scripts/check/check-llm-caret-installed-claude-cli.shs --case all
sh scripts/check/check-llm-caret-tui-pty.shs --case all

bin/simple test test/01_unit/app/llm_caret/main_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/claude_cli_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_tui_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_tui_input_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/config_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/tools_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/types_spec.spl --mode=interpreter

bin/simple test test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --mode=native

bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl --output doc/06_spec --no-index
bin/simple test test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl --mode=interpreter

sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
find doc/06_spec -name '*_spec.spl' | wc -l
```

The last command must print `0`. Each docgen invocation must report the changed
spec complete with `0 stubs`.

## Pass/Fail Criteria

PASS requires all of the following:

- the focused trace checker maps at least 80% of current direct files and LOC,
  and traces every current direct-file function/struct/extern;
- CLI deterministic scenarios launch the real wrapper and assert exit,
  structured response, stderr, and side effects;
- TUI scenarios send input through the visible surface and verify transcript
  plus status with captured evidence;
- live PTY qualification proves forced/automatic routing, ANSI-free piped
  fallback, modeled terminal teardown, UTF-8 editing/navigation, one bounded
  geometry, the semantic transcript text `You: a界c!`, and failure before
  terminal mutation when raw entry is unavailable;
- the selected live artifact has a matching adjacent provenance manifest,
  binary digest, clean committed source revision, host target, and rehashed
  build runtime, and the wrapper is pinned to that verified artifact;
- the installed-Claude probe submits no prompt, inherits no provider
  credentials, retains path/version/hash/raw stdout/stderr/exit artifacts, and
  makes no authenticated/provider/session claim;
- the root-command registry scenario derives lookup, alias, admission, and
  visibility coverage from every production record;
- every accepted hidden/flag case proves default and enabled/rejected states;
- all frozen helpers and step text are preserved;
- no unresolved runtime symbol, timeout, signal exit, usage exit, empty suite,
  placeholder pass, or missing manual is accepted;
- restored upstream provenance exists before any “all Claude functions” claim;
- full-parity matrices have zero unimplemented or untested rows before a full
  parity completion claim.

Current status is **FAIL / implementation present, execution blocked**. Direct
file/LOC/symbol mapping and the focused manuals are current. Process-level CLI,
live-PTY TUI capture, and the full-parity rows remain unproved by executable
evidence.

## 2026-07-24 Execution Update

The focused hardening lane now includes:

- `llm_caret_claude_cli_feature_contract_spec.spl`, covering the shared
  production builder/parser, local subprocess dispatch, stream envelopes,
  hidden fast/review gates, removed-flag rejection, and redaction;
- `llm_caret_cli_hardening_spec.spl`, launching the actual Caret entrypoint for
  help, offline success, provider failure, and unknown-option cases, plus
  cached production-wrapper selection and invalid-override rejection;
- `llm_caret_installed_claude_cli_spec.spl`, covering five bounded offline
  probes of the currently installed Claude executable with isolated HOME,
  config, working directory, and provider credentials removed;
- `llm_caret_tui_hidden_feature_spec.spl`, covering visible input/transcript,
  provider/model/session status, ANSI/UTF-8 decoder and raw-line control
  transitions, permission
  denial, retry limits, hidden commands, and SGTTI exclusion;
- `llm_caret_tui_pty_spec.spl` plus its shell checker, requiring a repository
  cached `bin/caret` target and real `script(1)` PTY while retaining typescript,
  input, driver, geometry, and terminal-mode evidence for every case;
- `managed_env_constants_spec.spl`, covering the experimental-beta disable and
  agent-team hidden environment keys without reading host state;
- `root_commands_registry_spec.spl`, deriving canonical/slash/alias identity,
  admission, visibility, hidden, and disabled coverage from every production
  root registry record;
- `llm_caret_cli_tui_hardening_smoke.spl`, a non-SSpec native entry for
  toolchain-isolated production-seam validation.

Current Claude Code `2.1.218` was probed without a prompt-bearing success path.
The installed CLI:

- returned a missing-input failure for a promptless stream-JSON invocation;
  that observation does not independently prove verbose-option validation;
- rejects `--max-tokens` as an unknown option;
- exposes `--allowedTools <tools...>` as one variadic option.

Production changes now enforce those contracts. The real provider dispatcher
routes through `claude_cli_send` instead of maintaining a second private
builder/parser. TUI `/provider`, `/model`, successful `/resume`, and `/new`
refresh visible status; `/new` obtains a fresh session ID instead of reusing
and overwriting the prior persisted conversation.

Focused system manuals are mirrored under `doc/06_spec/03_system/...`.
Source-synchronized unit manuals now mirror 80 Claude CLI, 31 provider, 24
production-chat, 60 TUI, 22 raw-input, 19 injected-runtime, 57 main-entry, 12
production-config, 37 production-tools, and 14 production-types scenarios.
Because docgen cannot execute in the current runtime, all refreshed manuals
explicitly report zero executed scenarios and do not claim a PASS.
The 356 source-synchronized unit examples plus eight CLI feature-contract,
three process-hardening, nine TUI/hidden, five managed-environment, five
installed-Claude, one new exhaustive root-registry, and five live-terminal
examples form a 392-example tranche of modern `should` examples
with canonical matchers and zero source/manual body mismatches.

Executable status remains **FAIL / runtime blocked**. The deployed
self-hosted `bin/simple` lacks `rt_process_spawn_guarded`, so the process SSpec
stops during semantic resolution before its scenario body. An isolated
pure-Simple bootstrap compiler accepted the hardening source through native
code generation, but the permitted third attempt stopped at the hosted-runtime
link boundary (`_MTLCreateSystemDefaultDevice` and `_rt_http_request`). Do not
repeat these commands in this session. After the concurrent compiler lane
deploys a full CLI containing the guarded-process symbol, run each focused
unit/system gate once and then the native smoke.

### Follow-up hardening and evidence audit

The current tree now rejects malformed/non-contract Claude JSON, rejects empty
or malformed successful NDJSON streams, requires a terminal stream event, and
redacts protocol-level error/result payloads. Typed JSON traversal replaces the
previous global substring extraction on these production paths and aggregates
all assistant text blocks. Offline fixtures cover empty, malformed,
unterminated, and secret-bearing streams.

TUI session transitions now preserve backend isolation:

- `/new` clears the provider session before issuing a fresh app session ID;
- `/provider` refreshes provider-specific model/key/base URL/CLI path and
  clears the foreign provider session;
- `/resume` restores provider, model, provider session, messages, title, and
  visible status together;
- command-line resume defaults to the persisted provider/model and discards
  the provider session when an explicit backend/model override is incompatible;
- reset/resume confirmations render after transcript replacement so they stay
  visible.

Hidden root commands now pass through `admitRootCommand`: hidden commands are
rejected by default and admitted only when enabled, while disabled commands
remain rejected under every fixture. Retry backoff is capped after jitter and
the configured retry timeout now prevents an over-budget sleep.

The completion audit is still red. Adding the Simple-only `tui_io.spl`
capability owner makes the current direct scope 25 files / 7,278 LOC with
496/496 file-qualified declarations in the regenerated trace inventory.
The focused checker covers all file-qualified declarations, including the
ANSI/UTF-8 raw-key decoder, raw-line reducer, and parser validation helpers.
The historical
1,902-row full-parity matrix has 1,157 missing targets and 1,728 missing primary
specs, and its upstream source tree is absent. The component TUI spec covers
the pure raw-key decoder, input-widget transition, and control-byte precedence.
The live checker now defines the driven PTY qualification and retains
artifacts, but no live PASS or capture is claimed until a cached artifact
executes every fail-closed case.
The root registry now has a production-derived exhaustive scenario for every
registered canonical name, slash name, alias, admission state, and visible
membership. Experimental environment gates and several distributed hidden
features are still not part of one aggregate production invocation map. These
gaps prohibit a full Claude parity or production-ready PASS claim.
