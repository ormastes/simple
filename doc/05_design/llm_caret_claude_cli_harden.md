# LLM Caret Claude CLI Harden - Detail Design

Date: 2026-07-05
Updated: 2026-07-07 (scope correction: hardening targets the shipped path)

## Scope Correction (2026-07-07)

This doc previously described "hardening" as a traceability/mapping checker
(`check-llm-caret-claude-cli-trace.shs`) that verifies file/LOC/symbol-name
presence in a markdown table. That is a **documentation-coverage gate, not a
robustness gate** — it proves a symbol name appears in a report, not that any
transient failure, secret leak, or unsafe tool call is handled.

Real hardening applies to the **shipped path** — the ~3,086-LOC root of
`src/app/llm_caret/` that actually runs (`mod.spl` -> `provider.spl` ->
`claude_api.spl`/`claude_cli.spl`/`openai_api.spl`/...). It does not turn the
broad `claude_full/` parity island (~720 files/~151K LOC) into the shipped
implementation. The shipped TUI deliberately imports the narrow
`claude_full.commands` root-command metadata capsule, but not the distributed
feature-gate registry or the rest of the parity island; `claude_full` has no
`fn main` (see
`doc/05_design/llm_caret_claude_cli_full_parity.md` current-state section).

The traceability report itself (`doc/09_report/llm_caret_claude_cli_traceability.md`)
is honest about its narrow scope ("it is not a full port of Claude Code"). The
overclaim was in reading that mapping gate as a hardening gate. The mapping
checker may remain as a docs-coverage tool, but it is not the hardening gate.

## Hardening Dimensions (shipped path)

Each is designed in full in the parity design doc; here is the hardening view —
what "robust" means and where it lands in the shipped source. Severities from the
2026-07-07 gap analysis.

| Dimension | Severity | Shipped-path landing site | Robustness property |
|---|---|---|---|
| Retry/backoff/timeout | P0 | `provider.spl` `dispatch_send`; every `rt_http_request`/`rt_process_run` site | transient 429/5xx/network failure recovers; hung subprocess is killed |
| Secret redaction | P0 | redaction pass before logging/JSONL persist in `provider.spl`/`chat.spl` | no raw `Authorization`/API key in any transcript or log |
| Injection defense | P0 | tag/wrap untrusted tool output in WebFetch/file-read before re-entering history | fetched content cannot silently steer the loop |
| Permission gating | P0 | single `permission_gate` all tool calls traverse before execution | `deny` blocks a real spawn; nothing executes ungated |
| Crash resilience | P1 | per-turn JSONL persist + subprocess timeout + top-level error boundary | crash loses at most the in-flight turn; `--resume` recovers |
| Observability | P1 | structured JSON-lines events around `dispatch_send` | latency/error/retry/token-cost are emitted |

## Legacy Trace Checker (retained as docs-coverage only)

- `doc/09_report/llm_caret_claude_cli_traceability.md` — feature/file/symbol
  mapping table (narrow scope, honest).
- `scripts/check/check-llm-caret-claude-cli-trace.shs` — counts mapped files/LOC
  and symbol-name presence, fails below 80%. This is a **documentation-coverage**
  signal only; it does not gate robustness and must not be cited as evidence that
  any hardening dimension above is met.
- `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` — runs
  the checker and asserts PASS output.

## Hardening Gate (real)

A dimension is hardened only when an **executed it-block** (not interpreter
file-load PASS) asserts the robustness property in the table above against a
fault it is meant to survive — e.g. a mock 429 for retry, a spawn spy for
permission deny, a transcript scan for redaction. See the hardening plan for the
per-task acceptance tests and the interpreter-mode caveat.

## Installed Claude Hidden-Argument Probe (2026-07-24)

The environmental checker has six bounded cases: provenance, version, help,
missing print input, hidden maximum-turn acceptance, and removed
maximum-token rejection. The hidden case invokes `--max-turns 1` with closed
stdin and passes only when Claude parses the option, rejects the absent input,
and does not report an unknown option. The help case independently requires
that `--max-turns` remain unadvertised, while `--allowedTools` remains variadic.

This two-oracle design prevents a help-only false negative for supported hidden
options and a parse-only false positive for removed options. Every child uses
an isolated HOME/config/work directory, an empty inherited environment, and a
five-second process-tree watchdog.

## Live TUI I/O and Lifecycle (2026-07-24)

`CaretIo` is an injectable capability record for TTY detection, terminal size,
raw/alternate-screen lifecycle, cursor state, drawing, byte/line input, and
text emission. `production_caret_io()` delegates to `std.tui.terminal`,
`app.llm_caret.tui_input.caret_is_tty`, and the canonical stdin facade.

`CaretLoopResult(mode, ok, exit_reason, error)` makes routing and terminal
failures observable to `main.spl`. The TUI loop follows:

1. acquire raw mode; fail before screen mutation if unavailable;
2. enter alternate screen and hide the cursor;
3. read and reduce input, render, dispatch slash/model transitions;
4. on `/exit`, Ctrl-C, Ctrl-D, or EOF, show the cursor, leave the alternate
   screen, then restore raw mode;
5. report raw restoration failure instead of silently returning success.

The plain loop uses the same capability for line input and output, which makes
EOF, slash dispatch, persistence, and automatic non-TTY routing deterministic
in component tests. `_draw_frame` receives the capability and uses exactly one
size snapshot; `_inner_height(rows)` is pure.

Real PTY evidence is a separate fail-closed system lane. It invokes the cached
`bin/caret` artifact through a host pseudo-terminal, records artifacts under
`build/test-artifacts`, and never substitutes source execution or a paid model.
If the cached artifact, PTY utility, or qualified runtime is absent, the gate
fails and records the missing prerequisite.

### Typed terminal lifecycle contract (2026-08-08)

<!-- codex-design -->

The original `CaretIo` capability exposed `enter_alt`, `hide_cursor`,
`show_cursor`, and `exit_alt` as void callbacks. That makes a failed terminal
transition indistinguishable from success and leaves the caller unable to state
which compensating cleanup is required. The next hardening slice replaces that
implicit protocol with one typed, ordered lifecycle surface. This is a contract
freeze: implementation and specs must use these names and signatures exactly.

```simple
struct CaretTerminalResult:
    ok: bool
    phase: text
    error: text

struct CaretIo:
    is_tty: fn() -> bool
    terminal_size: fn() -> TerminalSize
    begin_tui: fn() -> CaretTerminalResult
    end_tui: fn() -> CaretTerminalResult
    clear_screen: fn()
    draw_at: fn(i64, i64, text)
    flush: fn()
    read_byte: fn() -> i64
    read_line: fn() -> text?
    emit: fn(text)

fn caret_terminal_ok(phase: text) -> CaretTerminalResult
fn caret_terminal_error(phase: text, error: text) -> CaretTerminalResult
fn production_caret_io() -> CaretIo

fn run_chat_tui(
    ui0: ChatTui,
    policy: PermissionPolicy,
    responder: fn([Message]) -> ModelResponse,
    hooks: SessionHooks,
    initial_conv: [Message],
    io0: CaretIo? = nil
) -> CaretLoopResult
```

`begin_tui` performs `enter_raw -> enter_alt -> hide_cursor`. It stops at the
first failed phase and returns that phase (`raw-mode`, `alternate-screen`, or
`cursor-hide`) with a nonempty error. It must not attempt a later phase.
`end_tui` is compensating and idempotent: it attempts only the portions acquired
by the matching `begin_tui`, in reverse order (`show_cursor -> exit_alt ->
exit_raw`), records the first cleanup failure, and still attempts later cleanup.
The production adapter owns the acquisition bookkeeping; `chat_tui.spl` never
calls raw terminal primitives directly.

The following boundary semantics are mandatory:

| Caller state | Required result | Visible/output rule |
|---|---|---|
| `begin_tui.ok == false` | Return `CaretLoopResult(mode: "tui", ok: false, exit_reason: "terminal-setup-failed", error: result.error)` after one `end_tui` compensation call | No frame, ANSI draw, model call, or persistence |
| TUI input exits normally | Call `end_tui` once | Emit `chat session ended\n` only when cleanup succeeds |
| TUI command/model loop exits | Call `end_tui` once | Preserve the command/input exit reason unless cleanup fails |
| `end_tui.ok == false` | Return `ok: false`, `exit_reason: "terminal-cleanup-failed"`, and the exact cleanup error | Do not emit a success footer |
| Plain renderer selected | Do not call either lifecycle function | Continue using only `read_line` and `emit` |

`CaretLoopResult` remains the stable application-facing result shape. Its
`error` is empty only on success. `phase` is deliberately kept in the terminal
result rather than added to the public loop result; callers retain the stable
CLI contract while tests can assert precise lifecycle ownership through the
injected capability.

Migration is atomic across the owned TUI seam: delete the old individual
lifecycle fields rather than retaining two competing protocols. The production
adapter and every deterministic fixture construct the same ten-field `CaretIo`.
`run_chat_plain`, `caret_chat`, renderer selection, submission dispatch, and
all provider/session signatures remain unchanged. This prevents a CLI or hidden
command change from being coupled to terminal cleanup work.

Current terminal-owner limitation: the canonical raw-mode functions return a
Boolean, but alternate-screen and cursor primitives currently return unit after
writing ANSI. Therefore the production adapter can presently report an observed
setup failure only for `raw-mode`; `alternate-screen` and `cursor-hide` remain
reserved typed phases exercised by deterministic capability fixtures. A future
terminal-owner upgrade may make those phases observable, but this Caret tranche
must not claim that ANSI write success is verified merely because the capability
has phase names for it.

Required focused scenarios, with no provider/network dependency:

1. setup failure at each phase returns the typed failure, performs only valid
   reverse cleanup, and produces no frame/model/persist effect;
2. normal `/exit`, Ctrl-C, Ctrl-D, and EOF each call `end_tui` exactly once;
3. cleanup failure reports `terminal-cleanup-failed`, attempts remaining
   cleanup, and omits the success footer;
4. plain/automatic non-TTY routing makes zero lifecycle calls;
5. one-frame geometry remains a single `terminal_size` snapshot and one flush.

This contract is intentionally limited to the terminal boundary. Signal/panic
recovery still needs a runtime-owned atexit/signal facility and must not be
simulated by a second Caret terminal adapter.

## Distributed Feature-Gate Cross-Map (2026-07-24)

The bounded `claude_full` gate map contains 33 accepted gate dimensions. Each
`ClaudeFeatureGateRecord` stores stable source identity, exact owner source,
focused or aggregate system-test evidence, surface, applicability/state shape,
owner symbol, optional root command metadata, whether the default is
authoritative, default hidden/enabled state, gate kind, and one or more
`ClaudeFeatureGateProbe` Boolean/text outcomes.

`claudeFeatureGateRegistry()` derives probe values from import-safe owner
functions. It performs no environment reads, process launches, network calls,
or full-tree scans. Conditional, context, and environment records carry at
least two behaviorally distinct probes. Metadata-only safe-environment records
state only classification, not runtime enablement.

The focused SSpec uses:

- `setup_claude_feature_gate_fixture`;
- `check_claude_feature_gate_registry`;
- `Load the accepted Claude feature-gate registry`;
- `Reconcile root metadata with owner behavior`;
- `Check feature-gate completeness and rejection`.

The checker rejects duplicate identities or root commands, root metadata
without a named command, ownerless or incomplete records, invalid gate
kinds/state shapes, empty or duplicate probes, false default labels,
default/probe mismatch, and conditional records without a distinct state.
Every named root is reconciled against the production root map; a dedicated
edge scenario separately preserves `/compact` root metadata and the leaf
disable probe. The malformed fixture compares one exact ordered diagnostic
array, so unexpected failures cannot hide behind membership assertions. The
mirrored manual repeats the exact 33 source-to-spec/state rows and the strict
parts-bin claim limit while explicitly reporting zero executed scenarios.

## Tasks V2 hook/store hardening (2026-07-24)

`TasksV2HookEnvironment` owns one `TasksV2Store` and creates hook models that
share that store. `TasksV2HookModel.commit()` subscribes before its first fetch,
while `fetchAfterCommit()` rejects pre-commit and disabled fetches. `unmount()`
removes only that hook's subscription, so sibling hooks continue to observe the
shared snapshot.

`TasksV2Store.revision` is the stable external-store snapshot token. Fetches and
hide-timer transitions increment it only when the visible task/hidden snapshot
changes. This makes snapshot stability, commit ordering, disabled-hook behavior,
and shared-store semantics directly testable without hardcoded parity sentinels.

The obsolete helper that returned the historical modeled source-line value 240
was removed. The upstream matrix target remains 250 source lines and stays
explicitly non-PASS until pinned upstream regeneration can provide executable
evidence.

## Deterministic retry loop/effect seam (2026-07-24)

`RetryEffectTrace` is the import-safe substitute for sleeps, heartbeat yields,
credential-cache mutation, and stale-connection cooldowns. It records
`sleepDelaysMs`, `heartbeatCounts`, `cacheClears`, `cooldownDelaysMs`, and
`attemptStatuses`; it never sleeps or reads provider state.

`RetrySequenceResult` returns the ordered per-attempt outcomes plus total retry
sleep delay (excluding separately recorded stale-connection cooldown), total
heartbeat count, and the terminal status/error. `WithRetryModel` owns one trace
and exposes the loop through `run_retry_sequence(model, errors)`.
Persistent 429/529 errors may continue beyond `maxRetries`; nonpersistent
errors fail exactly at `maxRetries + 1`. Each retry appends one delay and
heartbeat count, which makes timing and boundary behavior deterministic.
`WithRetryModel` caches each numeric attempt and its outcome before exposing
the trace; immediate or nonconsecutive reuse returns that outcome without
re-running policy, logging, cache clearing, cooldown, sleep, or heartbeat
effects.
Retry-After values are capped by the configured maximum as an intentional
hardening policy; this is not claimed as proven upstream-exact parity while the
pinned upstream source is unavailable.

Provider recovery is modeled before the generic retry decision. AWS and GCP
credential failures append their exact cache identity once per attempt;
`ECONNRESET`/`EPIPE` append the configured stale-connection cooldown. These
effects make the error retryable but remain parts-bin evidence: no network,
credential provider, process, clock, or shipped CLI/TUI path is invoked.

The executable SSpec contract uses `setup_retry_sequence_fixture`,
`run_retry_sequence`, and `check_retry_sequence`. The canonical manual mirrors
complete scenario bodies and reports zero execution until a qualified
self-hosted runtime is available.

## Shipped promptless command reachability (2026-07-24)

The shipped path imports only `claude_full.commands`. `dispatch_slash` resolves
root aliases through `findRootCommand` and returns one canonical result before
either the plain or TUI caller can submit input to a model. Therefore
`/compact` and `/summarize` share the exact message
`Command not implemented in Caret: /compact`; `/init` and `/bootstrap` share
`Command not implemented in Caret: /init`.

This is intentionally distinct from the parity-island `compactCommand` and
`useNewInitPrompt` gates, which the shipped Caret path does not call. Component
evidence must prove exact canonical output, unchanged conversation/session and
title/status, one exact System transcript line, cleared input, zero responder
calls, and zero persistence. The injected `CaretIo` plain-loop case additionally
proves no raw/alternate-screen/cursor mutation. It remains component evidence,
not cached-wrapper stdin process evidence.

The same submission boundary applies to hidden aliases. With the hidden gate
off, `/debug_tool_call` must be indistinguishable from an unknown command; with
the gate on, it canonicalizes to `/debug-tool-call`. `/remote_setup` remains
disabled even when hidden admission is enabled. All three paths preserve
conversation/session/title/status and invoke neither responder nor persistence.

The fail-closed PTY checker projects the same mapping into four independent
cached-wrapper cases: `promptless-compact`, `promptless-summarize`,
`promptless-init`, and `promptless-bootstrap`. Each drives one command plus
`/exit` through a real PTY and retains the common child-exit, ANSI, cursor,
alternate-screen, geometry, and `stty` restoration gates before checking the
canonical System transcript. Four parallel explicit-`--plain` stdin cases
require zero exit, empty stderr, no ANSI, and the same canonical mapping.
Both routes fail on unknown/assistant output or any isolated-HOME session file.
These cases are designed but not executed while the qualified cached Caret
artifact is absent.
