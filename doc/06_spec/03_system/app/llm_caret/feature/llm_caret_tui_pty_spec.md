# LLM Caret Live PTY Qualification

> Launches the shipped cached Caret artifact through a real host PTY and
> explicit `--plain` stdin with the offline dummy provider. Missing
> prerequisites and incomplete routing evidence fail closed.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 7 | 7 | 0 | 0 |

This manual records zero executed scenarios and does not claim PASS because
cached process execution is blocked until a qualified Caret artifact exists.

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Live PTY Qualification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / TUI |
| Status | Active; execution requires a qualified cached Caret artifact |
| Requirements | REQ-LLM-CARET-TUI-HARDEN-007, REQ-LLM-CARET-TUI-HARDEN-009, REQ-LLM-CARET-HIDDEN-008, NFR-LLM-CARET-TUI-006 |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` |
| Updated | 2026-07-24 |
| Generator | Manual synchronization; docgen execution remains a qualification gate |

## Scope

The checker invokes only `bin/caret`, disables its source fallback, and pins
the wrapper override to the exact repository-cached native artifact whose
binary, clean committed source, target, and build-runtime hashes were verified.
The provenance must also attest `runtime=pure-simple-self-hosted`,
`runtime_probe=pass`, and `rust_seed_used=false`; missing or different values
fail closed.
All chat work uses `--provider dummy`; the checker removes its enumerated known
provider/cloud credential variables from the child environment. The dummy
provider requires no provider credential or network.
`script(1)` owns the pseudo-terminal and a child wrapper records
`stty -g` and geometry before and after Caret.

The checker rejects missing cache, `script(1)`, `stty`, `cmp`, markers, ANSI TUI
rendering, plain-output purity, edited UTF-8 text, geometry, or restoration.
It also drives the real TUI root-command path with no hidden-feature
environment, with `LLM_CARET_ENABLE_HIDDEN_COMMANDS=1`, and with a disabled
registry command. The three retained transcripts must respectively show
unknown-command rejection, sanitized debug-command execution, and
disabled-command rejection. Those cases use a fixed 12x80 PTY so inherited
geometry cannot truncate the exact semantic lines. Every PTY case must also
retain an explicit `caret_exit=0` child marker; `script -e` is only supplemental
exit propagation.
The promptless case is narrower: it proves that the shipped root metadata
admits `/compact`, `/summarize`, `/init`, and `/bootstrap`, including the two
canonical/alias pairs. Each command runs once through the real TUI and once
through explicit `--plain` stdin. Both routes reject `Unknown command:` and
`Assistant:` semantic output and reject any entries under the isolated
`HOME/.llm_caret/sessions` directory. Plain cases additionally require zero
exit, empty stderr, and no ANSI bytes. These checks do not promote the
corresponding leaf feature gates from parts-bin evidence or claim that their
feature implementations are shipped.
Forced TUI on non-TTY stdin must fail before emitting escape bytes with
`terminal raw mode unavailable`. Each child is guarded by one fixed 20-second
watchdog; timeout evidence is retained and fails the case without retry. The
outer SSpec process bound is 240 seconds for the seven-case hidden group and
eight-case promptless group, and 120 seconds for every other scenario.

**TUI Captures:**
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/`

The hard-panic/signal path remains outside this lane until the runtime exposes a
qualified atexit/signal restoration owner. EOF here means the PTY driver's
stdin closes normally; it is not evidence for an uncatchable runtime abort.

## Scenarios

### REQ-LLM-CARET-TUI-HARDEN-007: renderer routing uses real terminal state

#### should route forced and automatic TTY sessions while keeping piped auto output plain

- Open the caret TUI.
- Send a prompt through the visible input.
  - Expected: forced and automatic PTY sessions render and exit.
  - Expected: piped auto mode completes `/exit` with stdout exactly `> `,
    empty stderr, and no ANSI byte.
- Check transcript and status.
  - Expected: the checker reports `evidence_status=PASS` and exits zero.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the caret TUI")
val result = run_caret_pty_case("routing")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=forced-tui-route status=PASS")
expect(result.stdout).to_contain("case=auto-tty-route status=PASS")
expect(result.stdout).to_contain("case=piped-auto-plain status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

### REQ-LLM-CARET-TUI-HARDEN-009: terminal lifecycle is restored

#### should restore terminal state after slash exit Ctrl-C Ctrl-D and EOF

- Open the caret TUI.
- Send each modeled exit through the PTY input.
  - Expected: `/exit`, Ctrl-C, Ctrl-D, and closed input all terminate cleanly.
- Check transcript and status.
  - Expected: every case has equal pre/post terminal modes and zero failures.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the caret TUI")
val result = run_caret_pty_case("lifecycle")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=restore-after-slash-exit status=PASS")
expect(result.stdout).to_contain("case=restore-after-ctrl-c status=PASS")
expect(result.stdout).to_contain("case=restore-after-ctrl-d status=PASS")
expect(result.stdout).to_contain("case=restore-after-eof status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)
```

</details>

#### should preserve UTF-8 editing navigation and bounded terminal geometry

- Open the caret TUI.
- Insert U+754C, move left/end, submit, and repeat at 12 rows by 50 columns.
- Check transcript and status.
  - Expected: capture contains `a界c!`, frame ANSI, a row-12 status draw, no
    row-13 draw, and unchanged geometry.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the caret TUI")
val result = run_caret_pty_case("editing")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=utf8-edit-navigation status=PASS")
expect(result.stdout).to_contain("case=small-terminal-geometry status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

#### should reject forced TUI before terminal mutation when raw mode is unavailable

- Open the caret TUI without a PTY.
- Send `/exit` on piped stdin.
- Check transcript and status.
  - Expected: nonzero Caret exit, no ANSI, and the raw-mode error marker.
  - Expected: the checker converts the observed rejection into a passing case.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the caret TUI")
val result = run_caret_pty_case("raw-failure")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=forced-tui-without-tty status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: hidden command admission reaches the real TUI

#### should enforce hidden canonical alias and explicit false admission through the real TUI

- Enable the hidden-feature fixture.
  - Expected: canonical and alias default state renders the matching
    unknown-command response.
  - Expected: explicit `false` renders
    `system: Unknown command: /debug-tool-call (try /help)`.
  - Expected: canonical and alias enabled fixtures render
    `system: tool call id=call-1 name=Read input_bytes=27`.
  - Expected: canonical and alias disabled commands remain rejected.
- Check the hidden-feature gate.
  - Expected: all seven PTY cases pass with zero failures.

<details>
<summary>Executable SSpec</summary>

```simple
step("Enable the hidden-feature fixture")
val result = run_caret_pty_case("hidden")
expect(result.stdout).to_contain(
    "case=hidden-default-rejected status=PASS"
)
expect(result.stdout).to_contain(
    "case=hidden-false-rejected status=PASS"
)
expect(result.stdout).to_contain(
    "case=hidden-enabled-executed status=PASS"
)
expect(result.stdout).to_contain(
    "case=hidden-disabled-rejected status=PASS"
)
expect(result.stdout).to_contain(
    "case=hidden-alias-default-rejected status=PASS"
)
expect(result.stdout).to_contain(
    "case=hidden-alias-enabled-executed status=PASS"
)
expect(result.stdout).to_contain(
    "case=hidden-disabled-alias-rejected status=PASS"
)

step("Check the hidden-feature gate")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)
```

</details>

### Supporting evidence: promptless commands reach shipped root metadata

#### should reach compact summarize init and bootstrap aliases through shipped TUI and plain roots

- Open the caret TUI.
- Send the four promptless slash commands through the visible input and
  explicit `--plain` stdin.
  - Expected: `/compact`, `/summarize`, `/init`, and `/bootstrap` each reach
    the shipped root metadata through both routes and report eight passing
    checker cases.
  - Expected: aliases produce only their canonical result; no route produces
    unknown-command or assistant output or creates a session artifact.
- Check transcript and status.
  - Expected: the checker reports complete evidence, zero failed cases, and
    exits zero.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the caret TUI")
val result = run_caret_pty_case("promptless")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain(
    "case=promptless-compact status=PASS"
)
expect(result.stdout).to_contain(
    "case=promptless-summarize status=PASS"
)
expect(result.stdout).to_contain(
    "case=promptless-init status=PASS"
)
expect(result.stdout).to_contain(
    "case=promptless-bootstrap status=PASS"
)
expect(result.stdout).to_contain(
    "case=plain-promptless-compact status=PASS"
)
expect(result.stdout).to_contain(
    "case=plain-promptless-summarize status=PASS"
)
expect(result.stdout).to_contain(
    "case=plain-promptless-init status=PASS"
)
expect(result.stdout).to_contain(
    "case=plain-promptless-bootstrap status=PASS"
)
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)
```

</details>

### NFR-LLM-CARET-TUI-006: qualification is cached offline and fail closed

#### should prove cached offline qualification prerequisites fail closed

- Open the qualification boundary.
- Resolve the clean-source artifact, its build runtime, and host PTY
  implementation.
- Check transcript and status.
  - Expected: output names the manifest, matched source revision, binary and
    runtime hashes, target, exact wrapper pin, script style, and artifact root.
  - Expected: any missing prerequisite exits nonzero instead of skipping.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the caret TUI")
val result = run_caret_pty_case("prerequisites")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("cached_artifact=")
expect(result.stdout).to_contain("provenance_file=")
expect(result.stdout).to_contain("source_commit_check=matched")
expect(result.stdout).to_contain("verified_binary_sha256=")
expect(result.stdout).to_contain("verified_runtime_path=")
expect(result.stdout).to_contain("verified_runtime_sha256=")
expect(result.stdout).to_contain("runtime=pure-simple-self-hosted")
expect(result.stdout).to_contain("runtime_probe=pass")
expect(result.stdout).to_contain("rust_seed_used=false")
expect(result.stdout).to_contain("verified_target=")
expect(result.stdout).to_contain("wrapper_native_pin=")
expect(result.stdout).to_contain("script_style=")
step("Check transcript and status")
expect(result.stdout).to_contain(
    "build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty"
)
expect(result.exit_code).to_equal(0)
```

</details>

</details>

<details>
<summary>Executable helper source</summary>

The authoritative executable source is
`test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl`. The complete
shared checker helper is reproduced below; scenario bodies are reproduced
above without truncation.

```simple
use app.io.mod.{process_run_timeout}

struct CaretPtyEvidence:
    stdout: text
    stderr: text
    exit_code: i32

fn caret_pty_case_timeout_ms(case_name: text) -> i64:
    if case_name == "hidden" or case_name == "promptless":
        return 240000
    120000

fn run_caret_pty_case(case_name: text) -> CaretPtyEvidence:
    val (stdout, stderr, exit_code) = process_run_timeout(
        "sh",
        [
            "scripts/check/check-llm-caret-tui-pty.shs",
            "--case",
            case_name
        ],
        caret_pty_case_timeout_ms(case_name)
    )
    CaretPtyEvidence(
        stdout: stdout,
        stderr: stderr,
        exit_code: exit_code
    )
```

It declares no leaf runtime extern. Hidden and promptless checker groups have a
240-second hard bound; every other checker invocation has a 120-second hard
bound.

</details>
