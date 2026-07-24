# LLM Caret Live PTY Qualification

> Launches the shipped cached Caret artifact through a real host PTY with the
> offline dummy provider. Missing prerequisites and incomplete terminal
> evidence fail closed.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Live PTY Qualification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / TUI |
| Status | Active; execution requires a qualified cached Caret artifact |
| Requirements | REQ-LLM-CARET-TUI-HARDEN-007, REQ-LLM-CARET-TUI-HARDEN-009, NFR-LLM-CARET-TUI-006 |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` |
| Updated | 2026-07-24 |
| Generator | Manual synchronization; docgen execution remains a qualification gate |

## Scope

The checker invokes only `bin/caret`, disables its source fallback, and pins
the wrapper override to the exact repository-cached native artifact whose
binary, clean committed source, target, and build-runtime hashes were verified.
All chat work uses `--provider dummy`; no credential or network is needed.
`script(1)` owns the pseudo-terminal and a child wrapper records
`stty -g` and geometry before and after Caret.

The checker rejects missing cache, `script(1)`, `stty`, markers, ANSI TUI
rendering, plain-output purity, edited UTF-8 text, geometry, or restoration.
Forced TUI on non-TTY stdin must fail before emitting escape bytes with
`terminal raw mode unavailable`. Each child is guarded by one fixed 20-second
watchdog; timeout evidence is retained and fails the case without retry.

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
  - Expected: piped auto mode uses the plain prompt with no ANSI byte.
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

fn run_caret_pty_case(case_name: text) -> CaretPtyEvidence:
    val (stdout, stderr, exit_code) = process_run_timeout(
        "sh",
        [
            "scripts/check/check-llm-caret-tui-pty.shs",
            "--case",
            case_name
        ],
        120000
    )
    CaretPtyEvidence(
        stdout: stdout,
        stderr: stderr,
        exit_code: exit_code
    )
```

It declares no leaf runtime extern and gives every checker invocation a
120-second hard bound.

</details>
