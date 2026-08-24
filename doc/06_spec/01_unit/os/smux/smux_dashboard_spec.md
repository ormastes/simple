# @manual: primary

> Purpose: Specify the smux dashboard adapter — the session overview rows, pane

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Specify the smux dashboard adapter — the session overview rows, pane

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/smux/smux_dashboard_spec.spl` |
| Updated | 2026-08-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Specify the smux dashboard adapter — the session overview rows, pane
geometry and preview lines, the status bar, attach/detach results, and resize
hints that the multiplexer presents to an operator.
Audience: engineers changing `src/os/apps/smux/smux_dashboard.spl` who need to
know which rendered strings operators depend on.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines.
Each scenario narrates the row or widget it builds before asserting the exact
text it renders, so a failing verdict names the widget that changed shape.
## Compatibility and limitations
These scenarios pin rendered text and stored values only. Live terminal
drawing, attach side effects, and real PTY resize are out of scope here.
# @manual: primary
REQ-TOOLS-SMUX-DASH-001
doc/01_research/os/qemu/tmux_simpleos.md
doc/03_plan/sys_test/smux_caret_sspec_quality.md
doc/04_architecture/os/tmux_simpleos.md
doc/05_design/os/desktop/tmux_simpleos_tui.md

## Scenarios

### smux dashboard session rows

#### renders an attached row with window and pane counts

- Build an attached session row for dev with 3 windows and 5 panes
   - Expected: row.to_text() equals `dev (attached) w=3 p=5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-DASH-001
step("Build an attached session row for dev with 3 windows and 5 panes")
val row = DashSessionRow.make("s0", "dev", 3, 5, true)
expect(row.to_text()).to_equal("dev (attached) w=3 p=5")
```

</details>

#### renders a detached row with window and pane counts

- Build a detached session row for ci with 1 window and 2 panes
   - Expected: row.to_text() equals `ci (detached) w=1 p=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a detached session row for ci with 1 window and 2 panes")
val row = DashSessionRow.make("s1", "ci", 1, 2, false)
expect(row.to_text()).to_equal("ci (detached) w=1 p=2")
```

</details>

#### preserves the identifiers and counts it was built from

- Build a row for session sid99 with 4 windows and 8 panes
   - Expected: row.session_id equals `sid99`
   - Expected: row.window_count equals `4)  # oracle: the window count passed to make() is stored verbatim`
   - Expected: row.pane_count equals `8)  # oracle: the pane count passed to make() is stored verbatim`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a row for session sid99 with 4 windows and 8 panes")
val row = DashSessionRow.make("sid99", "prod", 4, 8, true)
expect(row.session_id).to_equal("sid99")
expect(row.window_count).to_equal(4)  # oracle: the window count passed to make() is stored verbatim
expect(row.pane_count).to_equal(8)  # oracle: the pane count passed to make() is stored verbatim
```

</details>

#### reports a zero window count for an empty session

- Build a row for a session that owns nothing
   - Expected: row.window_count equals `0)  # oracle: a session that owns nothing reports zero, never a placeholder`
   - Expected: row.pane_count equals `0)  # oracle: a session that owns nothing reports zero panes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a row for a session that owns nothing")
val row = DashSessionRow.make("s2", "empty", 0, 0, false)
expect(row.window_count).to_equal(0)  # oracle: a session that owns nothing reports zero, never a placeholder
expect(row.pane_count).to_equal(0)  # oracle: a session that owns nothing reports zero panes
```

</details>

### smux dashboard pane info

#### formats geometry as columns by rows

- Build pane info at the default 80x24 geometry
   - Expected: info.geometry_text() equals `80x24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-DASH-001
step("Build pane info at the default 80x24 geometry")
val info = DashPaneInfo.make("p0", "w0", "s0", 80, 24, false, "")
expect(info.geometry_text()).to_equal("80x24")
```

</details>

#### marks an active pane with a leading star

- Build an active 120x40 pane previewing $ ls
   - Expected: info.to_text() equals `*pane[p1] 120x40 > $ ls`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build an active 120x40 pane previewing $ ls")
val info = DashPaneInfo.make("p1", "w0", "s0", 120, 40, true, "$ ls")
expect(info.to_text()).to_equal("*pane[p1] 120x40 > $ ls")
```

</details>

#### marks an inactive pane with a leading space

- Build an inactive 80x24 pane with no preview
   - Expected: info.to_text() equals ` pane[p2] 80x24 > `


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build an inactive 80x24 pane with no preview")
val info = DashPaneInfo.make("p2", "w0", "s0", 80, 24, false, "")
expect(info.to_text()).to_equal(" pane[p2] 80x24 > ")
```

</details>

#### stores the preview line verbatim

- Build a pane previewing hello world
   - Expected: info.preview_line equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a pane previewing hello world")
val info = DashPaneInfo.make("p3", "w1", "s1", 80, 24, false, "hello world")
expect(info.preview_line).to_equal("hello world")
```

</details>

#### preserves width and height

- Build a 160x50 pane
   - Expected: info.width equals `160)  # oracle: the width passed to make() is stored verbatim`
   - Expected: info.height equals `50)  # oracle: the height passed to make() is stored verbatim`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 160x50 pane")
val info = DashPaneInfo.make("p4", "w2", "s2", 160, 50, true, "")
expect(info.width).to_equal(160)  # oracle: the width passed to make() is stored verbatim
expect(info.height).to_equal(50)  # oracle: the height passed to make() is stored verbatim
```

</details>

### smux dashboard status bar

#### starts empty with no sessions

- Read the empty status bar
   - Expected: sb.session_count equals `0)  # oracle: an empty status bar counts zero sessions`
   - Expected: sb.active_session_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-DASH-001
step("Read the empty status bar")
val sb = DashStatusBar.empty()
expect(sb.session_count).to_equal(0)  # oracle: an empty status bar counts zero sessions
expect(sb.active_session_name).to_equal("")
```

</details>

#### renders session count, names and geometry

- Build a status bar over 2 sessions, active dev:main at 80x24
   - Expected: sb.to_text() equals `[smux 2s] dev:main 80x24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a status bar over 2 sessions, active dev:main at 80x24")
val sb = DashStatusBar.build(2, "dev", "main", "80x24", true)
expect(sb.to_text()).to_equal("[smux 2s] dev:main 80x24")
```

</details>

#### renders placeholders when no session is active

- Render the empty status bar
   - Expected: sb.to_text() equals `[smux 0s] : `


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the empty status bar")
val sb = DashStatusBar.empty()
expect(sb.to_text()).to_equal("[smux 0s] : ")
```

</details>

#### reports an attached session

- Build a status bar whose session is attached
   - Expected: sb.has_attached is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a status bar whose session is attached")
val sb = DashStatusBar.build(1, "work", "editor", "100x30", true)
expect(sb.has_attached).to_equal(true)
```

</details>

#### reports a detached session

- Build a status bar whose session is detached
   - Expected: sb.has_attached is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a status bar whose session is detached")
val sb = DashStatusBar.build(1, "ci", "build", "80x24", false)
expect(sb.has_attached).to_equal(false)
```

</details>

### smux dashboard attach results

#### reports success with the attached session id

- Attach successfully to session s42
   - Expected: r.ok is true
   - Expected: r.session_id equals `s42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-DASH-001
step("Attach successfully to session s42")
val r = DashAttachResult.success("s42")
expect(r.ok).to_equal(true)
expect(r.session_id).to_equal("s42")
```

</details>

#### reports failure with the error message

- Attempt to attach to a session that does not exist
   - Expected: r.ok is false
   - Expected: r.error_msg equals `session not found: ghost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt to attach to a session that does not exist")
val r = DashAttachResult.failure("session not found: ghost")
expect(r.ok).to_equal(false)
expect(r.error_msg).to_equal("session not found: ghost")
```

</details>

#### renders a successful attach

- Render a successful attach result
   - Expected: r.to_text() equals `attached:sid1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a successful attach result")
val r = DashAttachResult.success("sid1")
expect(r.to_text()).to_equal("attached:sid1")
```

</details>

#### renders a failed attach

- Render a failed attach result
   - Expected: r.to_text() equals `error:not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a failed attach result")
val r = DashAttachResult.failure("not found")
expect(r.to_text()).to_equal("error:not found")
```

</details>

### smux dashboard resize hints

#### formats a resize hint from ids and geometry

- Ask for a resize hint targeting 120x40
   - Expected: h equals `resize s0/w0/p0 -> 120x40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-DASH-001
step("Ask for a resize hint targeting 120x40")
val h = dashboard_resize_hint("s0", "w0", "p0", 120, 40)
expect(h).to_equal("resize s0/w0/p0 -> 120x40")
```

</details>

#### formats a resize hint at the default terminal size

- Ask for a resize hint at the default 80x24 terminal size
   - Expected: h equals `resize sid/wid/pid -> 80x24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a resize hint at the default 80x24 terminal size")
val h = dashboard_resize_hint("sid", "wid", "pid", 80, 24)
expect(h).to_equal("resize sid/wid/pid -> 80x24")
```

</details>

#### preserves hyphenated identifiers

- Ask for a resize hint whose ids contain hyphens
   - Expected: h equals `resize my-session/win-3/pane-7 -> 200x60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a resize hint whose ids contain hyphens")
val h = dashboard_resize_hint("my-session", "win-3", "pane-7", 200, 60)
expect(h).to_equal("resize my-session/win-3/pane-7 -> 200x60")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b932f11301b8963414c83f647b7d5ed6b58f2f3491cbd21c59811e868b9adf16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b932f11301b8963414c83f647b7d5ed6b58f2f3491cbd21c59811e868b9adf16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b932f11301b8963414c83f647b7d5ed6b58f2f3491cbd21c59811e868b9adf16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/smux/smux_dashboard_spec.spl
mirror: doc/06_spec/01_unit/os/smux/smux_dashboard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smux/smux_dashboard_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/smux/smux_dashboard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smux/smux_dashboard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/smux/smux_dashboard_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders an attached row with window and pane counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smux/smux_dashboard_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a detached row with window and pane counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smux/smux_dashboard_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the identifiers and counts it was built from' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
