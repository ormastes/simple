# @manual: primary

> Purpose: Specify the smux terminal-multiplexer value model — session identity,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Specify the smux terminal-multiplexer value model — session identity,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/smux_spec.spl` |
| Updated | 2026-08-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Specify the smux terminal-multiplexer value model — session identity,
windows, panes, layout splits, PTY configuration, the output ring buffer, the
pane backend lifecycle, and command classification.
Audience: engineers changing `src/os/apps/smux/**` who need to know which
observable behaviors are pinned before they touch the multiplexer.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines.
Each scenario narrates its arrange/act steps, so a failing verdict names the
operation that regressed rather than only the value that differed.
## Compatibility and limitations
These scenarios exercise the pure value model only. PTY allocation, real
process attachment, and the on-screen renderer are covered by
`test/03_system/tools/smux_system_spec.spl`, not here.
# @manual: primary
REQ-TOOLS-SMUX-UNIT-001
doc/01_research/os/qemu/tmux_simpleos.md
doc/03_plan/sys_test/smux_caret_sspec_quality.md
doc/04_architecture/os/tmux_simpleos.md
doc/05_design/os/desktop/tmux_simpleos_tui.md

## Scenarios

### smux session identity

#### stores the name it was created with

- Create session \
   - Expected: s.session_name equals `main`
   - Expected: s.session_index equals `0)  # oracle: index 0 is the first session slot; smux numbers sessions from 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Create session \"main\" at index 0")
val s = SessionId.create("main", 0)
# oracle: create() is the only constructor, so it must round-trip both
# arguments verbatim; anything else silently renames a user's session.
expect(s.session_name).to_equal("main")
expect(s.session_index).to_equal(0)  # oracle: index 0 is the first session slot; smux numbers sessions from 0
```

</details>

#### matches its own name

- Create session \
   - Expected: s.matches_name("work") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create session \"work\" and ask it to match that same name")
val s = SessionId.create("work", 1)
expect(s.matches_name("work")).to_equal(true)
```

</details>

#### rejects a different name

- Ask session \
   - Expected: s.matches_name("other") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask session \"work\" to match an unrelated name")
val s = SessionId.create("work", 1)
expect(s.matches_name("other")).to_equal(false)
```

</details>

### smux windows

#### records index and title on creation

- Create window 2 titled \
   - Expected: w.window_index equals `2)  # oracle: the window index passed to create() is stored verbatim`
   - Expected: w.title equals `editor`
   - Expected: w.is_active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Create window 2 titled \"editor\"")
val w = WindowId.create(2, "editor")
expect(w.window_index).to_equal(2)  # oracle: the window index passed to create() is stored verbatim
expect(w.title).to_equal("editor")
# oracle: a freshly created window is never the active one; the caller
# activates it explicitly, so two new windows cannot both claim focus.
expect(w.is_active).to_equal(false)
```

</details>

#### becomes active when activated

- Create window 0 titled \
- Activate it
   - Expected: a.is_active is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create window 0 titled \"shell\"")
val w = WindowId.create(0, "shell")
step("Activate it")
val a = w.activate()
expect(a.is_active).to_equal(true)
```

</details>

#### becomes inactive when deactivated after activation

- Create window 0, activate it, then deactivate it
   - Expected: d.is_active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create window 0, activate it, then deactivate it")
val w = WindowId.create(0, "shell")
val a = w.activate()
val d = a.deactivate()
# oracle: deactivate must undo activate exactly, or focus leaks across
# windows and the multiplexer shows two active tabs.
expect(d.is_active).to_equal(false)
```

</details>

### smux panes

#### records the width and height it was created with

- Create pane 0 at the default 80x24 terminal geometry
   - Expected: p.width equals `80)  # oracle: 80 columns is the POSIX default terminal width`
   - Expected: p.height equals `24)  # oracle: 24 rows is the POSIX default terminal height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Create pane 0 at the default 80x24 terminal geometry")
val p = PaneId.create(0, 80, 24)
# oracle: 80x24 is the POSIX default terminal geometry inherited from
# PtyConfig.default_config(), not an arbitrary fixture size.
expect(p.width).to_equal(80)  # oracle: 80 columns is the POSIX default terminal width
expect(p.height).to_equal(24)  # oracle: 24 rows is the POSIX default terminal height
```

</details>

#### computes area as width times height

- Create an 80x24 pane and ask for its cell area
   - Expected: p.area() equals `1920)  # oracle: 1920 = 80 * 24 addressable cells`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an 80x24 pane and ask for its cell area")
val p = PaneId.create(0, 80, 24)
# oracle: 1920 = 80 * 24, the addressable cell count the renderer must
# allocate for this pane.
expect(p.area()).to_equal(1920)  # oracle: 1920 = 80 * 24 addressable cells
```

</details>

#### adopts new dimensions when resized

- Create an 80x24 pane, then resize it to 120x40
   - Expected: r.width equals `120)  # oracle: the requested resize width is stored verbatim`
   - Expected: r.height equals `40)  # oracle: the requested resize height is stored verbatim`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an 80x24 pane, then resize it to 120x40")
val p = PaneId.create(0, 80, 24)
val r = p.resize(120, 40)
expect(r.width).to_equal(120)  # oracle: the requested resize width is stored verbatim
expect(r.height).to_equal(40)  # oracle: the requested resize height is stored verbatim
```

</details>

### smux session state

#### starts empty for a fresh session

- Build session state over a newly created session
   - Expected: ss.is_empty() is true
   - Expected: ss.active_count equals `0)  # oracle: a fresh session owns no windows yet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Build session state over a newly created session")
val s = SessionId.create("main", 0)
val ss = SmuxSessionState.create(s)
# oracle: a session with no attached window must report empty, so the
# dashboard does not draw a pane that has no backing process.
expect(ss.is_empty()).to_equal(true)
expect(ss.active_count).to_equal(0)  # oracle: a fresh session owns no windows yet
```

</details>

### smux layout splits

#### creates a horizontal split

- Split node 1 horizontally at an even 50 percent ratio
   - Expected: sp.direction equals `horizontal`
   - Expected: sp.is_horizontal() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Split node 1 horizontally at an even 50 percent ratio")
val sp = LayoutSplit.horizontal(1, 50)
expect(sp.direction).to_equal("horizontal")
expect(sp.is_horizontal()).to_equal(true)
```

</details>

#### creates a vertical split

- Split node 2 vertically at a 30 percent ratio
   - Expected: sp.direction equals `vertical`
   - Expected: sp.ratio equals `30)  # oracle: the requested split ratio is stored unrounded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Split node 2 vertically at a 30 percent ratio")
val sp = LayoutSplit.vertical(2, 30)
expect(sp.direction).to_equal("vertical")
# oracle: the requested ratio is stored verbatim; the layout engine
# rounds to cells later, so a stored ratio must not be pre-rounded.
expect(sp.ratio).to_equal(30)  # oracle: the requested split ratio is stored unrounded
```

</details>

#### inverts horizontal into vertical

- Invert a horizontal split
   - Expected: inv.direction equals `vertical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invert a horizontal split")
val sp = LayoutSplit.horizontal(1, 50)
val inv = sp.invert()
expect(inv.direction).to_equal("vertical")
```

</details>

#### reports a leaf node as holding a pane

- Build a leaf node bound to pane 0
   - Expected: n.has_pane() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a leaf node bound to pane 0")
val n = LayoutNode.leaf(1, 0)
expect(n.has_pane()).to_equal(true)
```

</details>

#### reports an internal node as holding no pane

- Build an internal node wrapping a vertical split
   - Expected: n.has_pane() is false
   - Expected: n.pane_index equals `-1)  # oracle: -1 is the sentinel meaning "this node holds no pane"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build an internal node wrapping a vertical split")
val sp = LayoutSplit.vertical(1, 50)
val n = LayoutNode.internal(2, sp)
expect(n.has_pane()).to_equal(false)
# oracle: -1 is the sentinel for \"no pane\"; a real index here would
# make the renderer draw an internal node's children twice.
expect(n.pane_index).to_equal(-1)  # oracle: -1 is the sentinel meaning "this node holds no pane"
```

</details>

### smux pty configuration

#### defaults to an 80x24 terminal

- Read the default PTY configuration
   - Expected: cfg.rows equals `24)  # oracle: 24 rows is the POSIX default terminal height`
   - Expected: cfg.cols equals `80)  # oracle: 80 columns is the POSIX default terminal width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Read the default PTY configuration")
val cfg = PtyConfig.default_config()
# oracle: 24 rows by 80 columns is the POSIX default terminal geometry
# that every consumer of default_config() inherits.
expect(cfg.rows).to_equal(24)  # oracle: 24 rows is the POSIX default terminal height
expect(cfg.cols).to_equal(80)  # oracle: 80 columns is the POSIX default terminal width
```

</details>

#### adopts a new terminal size

- Resize the default configuration to 40 rows by 120 columns
   - Expected: r.rows equals `40)  # oracle: the requested row count is stored verbatim`
   - Expected: r.cols equals `120)  # oracle: the requested column count is stored verbatim`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resize the default configuration to 40 rows by 120 columns")
val cfg = PtyConfig.default_config()
val r = cfg.with_size(40, 120)
expect(r.rows).to_equal(40)  # oracle: the requested row count is stored verbatim
expect(r.cols).to_equal(120)  # oracle: the requested column count is stored verbatim
```

</details>

### smux output buffer

#### returns the first appended line

- Create a 4-line ring buffer and append one line
   - Expected: b1.get_line(0) equals `hello`
   - Expected: b1.line_count equals `1)  # oracle: one append yields exactly one buffered line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Create a 4-line ring buffer and append one line")
val buf = OutputBuffer.create(4)
val b1 = buf.append_line("hello")
expect(b1.get_line(0)).to_equal("hello")
# oracle: one append yields exactly one line; a ring buffer that
# miscounts here drops scrollback once it wraps.
expect(b1.line_count).to_equal(1)  # oracle: one append yields exactly one buffered line
```

</details>

### smux pane backend

#### stops running once stopped

- Create a pane backend over the default PTY configuration
- Stop it with a clean exit status
   - Expected: stopped.is_running is false
   - Expected: stopped.exit_code equals `0)  # oracle: stop() records the status it was handed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Create a pane backend over the default PTY configuration")
val cfg = PtyConfig.default_config()
val be = PaneBackend.create(1, cfg)
step("Stop it with a clean exit status")
val stopped = be.stop(0)
expect(stopped.is_running).to_equal(false)
# oracle: 0 is the exit status handed to stop(); the backend records
# what it was told rather than inventing a status of its own.
expect(stopped.exit_code).to_equal(0)  # oracle: stop() records the status it was handed
```

</details>

### smux commands

#### classifies new-session as a session command

- Build a new-session command targeting \
   - Expected: cmd.is_session_cmd() is true
   - Expected: cmd.target_name equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-UNIT-001
step("Build a new-session command targeting \"dev\"")
val cmd = SmuxCommand.new_session("dev")
expect(cmd.is_session_cmd()).to_equal(true)
expect(cmd.target_name).to_equal("dev")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80fbcebc0fb8bc255f2b8d666ee48a5543de6723b3262fd26f77c301fb519220`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80fbcebc0fb8bc255f2b8d666ee48a5543de6723b3262fd26f77c301fb519220`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80fbcebc0fb8bc255f2b8d666ee48a5543de6723b3262fd26f77c301fb519220`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/smux_spec.spl
mirror: doc/06_spec/01_unit/os/smux_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smux_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/smux_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smux_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/smux_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores the name it was created with' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smux_spec.spl:257:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches its own name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smux_spec.spl:262:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a different name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
