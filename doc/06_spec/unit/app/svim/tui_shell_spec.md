# Tui Shell Specification

> Tests covering svim host shell helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Shell Specification

## Scenarios

### svim host shell helpers

#### renders help text with shared and host commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders help text with shared and host commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders help text with shared and host commands")
val help = svim_shell_help_text()
expect help.contains(":w <path>") to_equal true
expect help.contains("open <path>") to_equal true
expect help.contains(".buffers") to_equal true
```

</details>

#### formats pending prompts for open save and search flows

- formats pending prompts for open save and search flows


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats pending prompts for open save and search flows")
val session = SvimSession.new()
expect svim_shell_prompt(session, "open-buffer") to_equal "open path> "
expect svim_shell_prompt(session, "save-as") to_equal "write path> "
expect svim_shell_prompt(session, "search-forward") to_equal "search> "
```

</details>

#### classifies host aliases and shell meta commands

- classifies host aliases and shell meta commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies host aliases and shell meta commands")
val open_cmd = svim_shell_classify_line(SvimMode.Normal, "open /tmp/demo.txt")
expect open_cmd.0 to_equal "dispatch"
expect open_cmd.1 to_equal "open-buffer:/tmp/demo.txt"
val write_cmd = svim_shell_classify_line(SvimMode.Normal, "write /tmp/demo.txt")
expect write_cmd.0 to_equal "dispatch"
expect write_cmd.1 to_equal "save-as:/tmp/demo.txt"
val buffers_cmd = svim_shell_classify_line(SvimMode.Normal, ".buffers")
expect buffers_cmd.0 to_equal "buffers"
expect buffers_cmd.1 to_equal ""
```

</details>

#### routes insert mode text and shell escapes distinctly

- routes insert mode text and shell escapes distinctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes insert mode text and shell escapes distinctly")
val insert_text = svim_shell_classify_line(SvimMode.Insert, "hello")
expect insert_text.0 to_equal "insert"
expect insert_text.1 to_equal "hello"
val insert_escape = svim_shell_classify_line(SvimMode.Insert, ".esc")
expect insert_escape.0 to_equal "dispatch"
expect insert_escape.1 to_equal "set-mode:normal"
val insert_commandline = svim_shell_classify_line(SvimMode.Insert, ":w")
expect insert_commandline.0 to_equal "dispatch"
expect insert_commandline.1 to_equal ":w"
```

</details>

#### renders session status and buffer listings

- renders session status and buffer listings


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders session status and buffer listings")
var session = SvimSession.new()
session.open_text("/tmp/alpha.txt", "alpha")
val tui = svim_render_tui(session)
expect tui.contains("mode NORMAL") to_equal true
expect tui.contains("/tmp/alpha.txt") to_equal true
val buffers = svim_render_buffer_list(session)
expect buffers.contains("[No Name]") to_equal true
expect buffers.contains("/tmp/alpha.txt") to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/svim/tui_shell_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering svim host shell helpers.
- svim host shell helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1ba0a8e661ccc73ad76497349d1a38794bb85b9db89c65431cd8ba9f4ee71771`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ba0a8e661ccc73ad76497349d1a38794bb85b9db89c65431cd8ba9f4ee71771`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ba0a8e661ccc73ad76497349d1a38794bb85b9db89c65431cd8ba9f4ee71771`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/svim/tui_shell_spec.spl
mirror: doc/06_spec/unit/app/svim/tui_shell_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/svim/tui_shell_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/svim/tui_shell_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/svim/tui_shell_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders help text with shared and host commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/svim/tui_shell_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats pending prompts for open save and search flows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/svim/tui_shell_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies host aliases and shell meta commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
