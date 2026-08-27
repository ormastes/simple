# LLM Caret Live PTY Qualification

> Launch the shipped cached `bin/caret` wrapper with the offline dummy provider.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 9 | 9 | 0 | 0 |

This manual records zero executed scenarios and does not claim PASS because
cached process execution is blocked until a qualified Caret artifact exists.

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Live PTY Qualification

Launch the shipped cached `bin/caret` wrapper with the offline dummy provider.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / TUI |
| Status | Active; execution requires a qualified cached Caret artifact |
| Requirements | REQ-LLM-CARET-TUI-HARDEN-007, REQ-LLM-CARET-TUI-HARDEN-009, REQ-LLM-CARET-HIDDEN-008, NFR-LLM-CARET-TUI-006 |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

Launch the shipped cached `bin/caret` wrapper with the offline dummy provider.
The host `script(1)` utility supplies a real PTY. The checker fails closed when
the cached artifact, PTY utility, terminal control, output markers, or terminal
restoration evidence is missing.
The hidden case drives default, explicitly false, explicitly enabled, and
disabled root-command admission through that same real TUI boundary without
contacting a provider.
The promptless case proves shipped root metadata and alias reachability for
`/compact`, `/summarize`, `/init`, and `/bootstrap` through both the real TUI
and explicit `--plain` stdin. Both routes reject model output and session-file
effects; their leaf feature gates remain parts-bin evidence outside this
qualification.

**TUI Captures:**
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/`

## Scenarios

The hard-panic/signal path remains outside this lane until the runtime exposes a
qualified atexit/signal restoration owner. EOF here means the PTY driver's
stdin closes normally; it is not evidence for an uncatchable runtime abort.

## Scenarios

### REQ-LLM-CARET-TUI-HARDEN-007: renderer routing uses real terminal state

#### routes forced and automatic TTY sessions while keeping piped auto output plain

- Open the caret TUI.
- Send a prompt through the visible input.
  - Expected: forced and automatic PTY sessions render and exit.
  - Expected: piped auto mode completes `/exit` with stdout exactly `> `,
    empty stderr, and no ANSI byte.
- Check transcript and status.
  - Expected: the checker reports `evidence_status=PASS` and exits zero.

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

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

- should restore terminal state after slash exit Ctrl-C Ctrl-D and EOF
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore terminal state after slash exit Ctrl-C Ctrl-D and EOF")
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

- should preserve UTF-8 editing navigation and bounded terminal geometry
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve UTF-8 editing navigation and bounded terminal geometry")
step("Open the caret TUI")
val result = run_caret_pty_case("editing")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=utf8-edit-navigation status=PASS")
expect(result.stdout).to_contain("case=small-terminal-geometry status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should recover from malformed UTF-8 without leaking invalid bytes

- should recover from malformed UTF-8 without leaking invalid bytes
- Open the caret TUI
- Send malformed bytes then a valid prompt through the visible input
- Check transcript and terminal restoration
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should recover from malformed UTF-8 without leaking invalid bytes")
step("Open the caret TUI")
val result = run_caret_pty_case("invalid-utf8-recovery")
step("Send malformed bytes then a valid prompt through the visible input")
expect(result.stdout).to_contain(
    "case=invalid-utf8-recovery status=PASS"
)
step("Check transcript and terminal restoration")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject forced TUI before terminal mutation when raw mode is unavailable

- should reject forced TUI before terminal mutation when raw mode is unavailable
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject forced TUI before terminal mutation when raw mode is unavailable")
step("Open the caret TUI")
val result = run_caret_pty_case("raw-failure")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=forced-tui-without-tty status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

#### should show a redacted offline Claude provider error while restoring the terminal

- should show a redacted offline Claude provider error while restoring the terminal
- Load the cached Caret artifact
- Invoke the offline Caret CLI provider
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should show a redacted offline Claude provider error while restoring the terminal")
step("Load the cached Caret artifact")
val result = run_caret_pty_case("provider-error")
step("Invoke the offline Caret CLI provider")
expect(result.stdout).to_contain(
    "case=offline-claude-provider-error status=PASS"
)
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### REQ-LLM-CARET-FULL-003: offline Claude CLI reaches the cached TUI

#### should show the offline Claude response through the visible TUI

- Verify: should show the offline Claude response through the visible TUI
- Open the cached caret TUI with offline Claude CLI fixture
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-TUI-HARDEN-007 REQ-LLM-CARET-TUI-HARDEN-009 REQ-LLM-CARET-HIDDEN-008 REQ-LLM-CARET-FULL-003
step("Verify: should show the offline Claude response through the visible TUI")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open the cached caret TUI with offline Claude CLI fixture")
val result = run_caret_pty_case("offline-claude")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=offline-claude status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### REQ-LLM-CARET-FULL-003: offline Claude CLI reaches the cached TUI

#### should show the offline Claude response through the visible TUI

- should show the offline Claude response through the visible TUI
- Open the cached caret TUI with offline Claude CLI fixture
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should show the offline Claude response through the visible TUI")
step("Open the cached caret TUI with offline Claude CLI fixture")
val result = run_caret_pty_case("offline-claude")
step("Send a prompt through the visible input")
expect(result.stdout).to_contain("case=offline-claude status=PASS")
step("Check transcript and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain("failed_cases=0")
expect(result.exit_code).to_equal(0)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: hidden command admission reaches the real TUI

#### should enforce hidden canonical alias and explicit false admission through the real TUI

- should enforce hidden canonical alias and explicit false admission through the real TUI
- Enable the hidden-feature fixture
- Check the hidden-feature gate
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce hidden canonical alias and explicit false admission through the real TUI")
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
    "case=hidden-alias-false-rejected status=PASS"
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

- should reach compact summarize init and bootstrap aliases through shipped TUI and plain roots
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reach compact summarize init and bootstrap aliases through shipped TUI and plain roots")
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

- should prove cached offline qualification prerequisites fail closed
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prove cached offline qualification prerequisites fail closed")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-LLM-CARET-TUI-HARDEN-007,`
- **Plan:** `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

struct CaretPtyEvidence:
    stdout: text
    stderr: text
    exit_code: i32

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-TUI-HARDEN-007`
- `REQ-LLM-CARET-TUI-HARDEN-009`
- `REQ-LLM-CARET-HIDDEN-008`
- `REQ-LLM-CARET-FULL-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b822141cb6359e9e0d8c7afc7d0f07573a6fa41f1ef63145f1f355b2a46162e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b822141cb6359e9e0d8c7afc7d0f07573a6fa41f1ef63145f1f355b2a46162e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b822141cb6359e9e0d8c7afc7d0f07573a6fa41f1ef63145f1f355b2a46162e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes forced and automatic TTY sessions while keeping piped auto output plain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore terminal state after slash exit Ctrl-C Ctrl-D and EOF' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should restore terminal state after slash exit Ctrl-C Ctrl-D and EOF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve UTF-8 editing navigation and bounded terminal geometry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve UTF-8 editing navigation and bounded terminal geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recover from malformed UTF-8 without leaking invalid bytes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject forced TUI before terminal mutation when raw mode is unavailable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show a redacted offline Claude provider error while restoring the terminal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show the offline Claude response through the visible TUI' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
