# pane_backend_spec

> As a caret-suite operator I open the `cs` dashboard, see every pane my session

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pane_backend_spec

As a caret-suite operator I open the `cs` dashboard, see every pane my session

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/pane_backend_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
As a caret-suite operator I open the `cs` dashboard, see every pane my session
owns, switch the pane I want to talk to, and maximize the pane that is taking
my command so its output fills the terminal. This spec is for the engineers
who own `src/app/llm_caret/pane_backend.spl` and the tmux contract behind it.
The dashboard must be honest about the host it runs on: on a machine with tmux
it drives real tmux panes, and on a machine without one (Windows, or a POSIX
box with no tmux installed) it drives smux panes - Simple's own multiplexer,
on a real ConPTY on Windows - and never shows me panes that do not exist.
## Operator workflow
bin/simple test test/01_unit/app/llm_caret/pane_backend_spec.spl
## Compatibility and limitations
The live tmux scenario needs a real tmux on PATH; on a host without one the
scenario pins the degraded-backend verdict instead of driving panes. The
disposable session name is `cs-pane-backend-spec` and must never be the
operator's own session.
## Verification guidance and troubleshooting
A parser failure means tmux output shape drifted; a command-builder failure
means the argv contract moved. Rerun
bin/simple test test/01_unit/app/llm_caret/pane_backend_spec.spl after any
pane_backend change; a leftover `cs-pane-backend-spec` session from a crashed
run can be killed with tmux before rerunning.

## Scenarios

### cs pane backend reads tmux pane lines

#### types a chat message literally and submits it as a separate keystroke

- Build the literal-write argv
   - Protocol capture: after_step
- Build the submit argv
   - Expected: pane_send_enter_argv("%3") equals `["send-keys", "-t", "%3", "Enter"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-001
step("Build the literal-write argv")
expect(pane_send_literal_argv("%3", "say Enter please")).to_equal(
    ["send-keys", "-t", "%3", "-l", "say Enter please"])

step("Build the submit argv")
expect(pane_send_enter_argv("%3")).to_equal(["send-keys", "-t", "%3", "Enter"])
```

</details>

#### turns a realistic list-panes line into a fully populated Pane

- parse one active, unzoomed pane line emitted by tmux
   - TUI capture: after_step
   - Evidence: TUI state verified by 4 expected checks
   - Expected: panes.len() equals `1)  # oracle: one well-formed line parses to exactly one Pane`
   - Expected: panes[0].pane_id equals `%3`
   - Expected: panes[0].pid equals `48211)  # oracle: the second whitespace column is the host PID`
   - Expected: panes[0].title equals `claude-worker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-002
step("parse one active, unzoomed pane line emitted by tmux")
val panes = pane_parse_line("%3 48211 1 0 claude-worker")
expect(panes.len()).to_equal(1)  # oracle: one well-formed line parses to exactly one Pane
expect(panes[0].pane_id).to_equal("%3")
expect(panes[0].pid).to_equal(48211)  # oracle: the second whitespace column is the host PID
expect(panes[0].title).to_equal("claude-worker")
assert_true(panes[0].active)
assert_false(panes[0].zoomed)
```

</details>

#### keeps a multi-word pane title intact

- titles carry spaces, so they are the trailing columns
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: panes.len() equals `1)  # oracle: one well-formed line parses to exactly one Pane`
   - Expected: panes[0].title equals `caret agent two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("titles carry spaces, so they are the trailing columns")
val panes = pane_parse_line("%12 991 0 1 caret agent two")
expect(panes.len()).to_equal(1)  # oracle: one well-formed line parses to exactly one Pane
expect(panes[0].title).to_equal("caret agent two")
assert_false(panes[0].active)
assert_true(panes[0].zoomed)
```

</details>

#### accepts a pane whose title tmux left empty

- an untitled pane is still a real pane
   - TUI capture: after_step
   - Evidence: TUI state verified by 3 expected checks
   - Expected: panes.len() equals `1)  # oracle: a short line without a title still parses to one Pane`
   - Expected: panes[0].title equals ``
   - Expected: panes[0].pid equals `7)  # oracle: the PID column decodes even when the title is absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("an untitled pane is still a real pane")
val panes = pane_parse_line("%0 7 1 0")
expect(panes.len()).to_equal(1)  # oracle: a short line without a title still parses to one Pane
expect(panes[0].title).to_equal("")
expect(panes[0].pid).to_equal(7)  # oracle: the PID column decodes even when the title is absent
```

</details>

#### yields no Pane at all for a malformed line

- fail closed: garbage must never become a Pane with garbage fields
   - Text capture: after_step
   - Evidence: text output verified by 6 expected checks
   - Expected: pane_parse_line("").len() equals `0)  # oracle: an empty line is absence, not a Pane`
   - Expected: pane_parse_line("garbage").len() equals `0)  # oracle: a line without columns is absence, not a Pane`
   - Expected: pane_parse_line("3 48211 1 0 title").len() equals `0)  # oracle: a pane id must start with %, so this is absence`
   - Expected: pane_parse_line("%3 notapid 1 0 title").len() equals `0)  # oracle: a non-numeric PID column is absence, not a Pane`
   - Expected: pane_parse_line("%3 48211 yes 0 title").len() equals `0)  # oracle: a non-numeric active flag is absence, not a Pane`
   - Expected: pane_parse_line("%3 48211 1 maybe title").len() equals `0)  # oracle: a non-numeric zoom flag is absence, not a Pane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-003
step("fail closed: garbage must never become a Pane with garbage fields")
expect(pane_parse_line("").len()).to_equal(0)  # oracle: an empty line is absence, not a Pane
expect(pane_parse_line("garbage").len()).to_equal(0)  # oracle: a line without columns is absence, not a Pane
expect(pane_parse_line("3 48211 1 0 title").len()).to_equal(0)  # oracle: a pane id must start with %, so this is absence
expect(pane_parse_line("%3 notapid 1 0 title").len()).to_equal(0)  # oracle: a non-numeric PID column is absence, not a Pane
expect(pane_parse_line("%3 48211 yes 0 title").len()).to_equal(0)  # oracle: a non-numeric active flag is absence, not a Pane
expect(pane_parse_line("%3 48211 1 maybe title").len()).to_equal(0)  # oracle: a non-numeric zoom flag is absence, not a Pane
```

</details>

#### drops only the bad line when a block mixes good and bad

- one corrupt line must not lose the healthy panes around it
   - TUI capture: after_step
   - Evidence: TUI state verified by 3 expected checks
   - Expected: panes.len() equals `2)  # oracle: only the corrupt middle line is dropped from the block`
   - Expected: panes[0].pane_id equals `%1`
   - Expected: panes[1].pane_id equals `%2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("one corrupt line must not lose the healthy panes around it")
val panes = pane_parse_lines("%1 100 1 0 alpha\nrubbish\n%2 200 0 1 beta\n")
expect(panes.len()).to_equal(2)  # oracle: only the corrupt middle line is dropped from the block
expect(panes[0].pane_id).to_equal("%1")
expect(panes[1].pane_id).to_equal("%2")
assert_true(panes[1].zoomed)
```

</details>

### cs pane backend builds the right tmux commands

#### asks tmux for the pane fields the parser expects

- the list argv must carry the session and the documented format
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: argv[0] equals `list-panes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-004
step("the list argv must carry the session and the documented format")
val argv = pane_list_argv("caret")
expect(argv[0]).to_equal("list-panes")
expect(argv).to_contain("caret")
expect(argv).to_contain(PANE_FORMAT)
expect(PANE_FORMAT).to_contain("#{{pane_id}}")
expect(PANE_FORMAT).to_contain("#{{pane_title}}")
```

</details>

#### switches the active pane with select-pane on the pane id

- pane ids are globally unique, so -t takes the id alone
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: argv.len() equals `3)  # oracle: select-pane -t <id> is exactly three argv words`
   - Expected: argv[0] equals `select-pane`
   - Expected: argv[1] equals `-t`
   - Expected: argv[2] equals `%7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("pane ids are globally unique, so -t takes the id alone")
val argv = pane_select_argv("%7")
expect(argv.len()).to_equal(3)  # oracle: select-pane -t <id> is exactly three argv words
expect(argv[0]).to_equal("select-pane")
expect(argv[1]).to_equal("-t")
expect(argv[2]).to_equal("%7")
```

</details>

<details>
<summary>Advanced: maximizes with resize-pane -Z so the zoom toggles</summary>

#### maximizes with resize-pane -Z so the zoom toggles

- -Z is tmux's toggle for pane zoom
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: argv[0] equals `resize-pane`
   - Expected: argv[argv.len() - 1] equals `%7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("-Z is tmux's toggle for pane zoom")
val argv = pane_zoom_argv("%7")
expect(argv[0]).to_equal("resize-pane")
expect(argv).to_contain("-Z")
expect(argv[argv.len() - 1]).to_equal("%7")
```

</details>


</details>

#### kills a pane with kill-pane on the pane id

- teardown targets the same pane id
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: argv[0] equals `kill-pane`
   - Expected: argv[argv.len() - 1] equals `%7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("teardown targets the same pane id")
val argv = pane_kill_argv("%7")
expect(argv[0]).to_equal("kill-pane")
expect(argv[argv.len() - 1]).to_equal("%7")
```

</details>

### cs pane backend is honest about the host

#### names tmux only when tmux answers, and smux otherwise

- Read the backend the dashboard will drive on this host
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: pane_available() is true
- Windows has no tmux, so the in-process smux backend is chosen
   - Expected: name equals `smux`
- A POSIX host drives tmux when present and smux otherwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-005
step("Read the backend the dashboard will drive on this host")
val name = pane_backend_name()
expect(pane_available()).to_equal(true)
if sosix_platform() == "windows":
    step("Windows has no tmux, so the in-process smux backend is chosen")
    expect(name).to_equal("smux")
else:
    step("A POSIX host drives tmux when present and smux otherwise")
    assert_true(name == "tmux" or name == "smux")
```

</details>

#### refuses pane operations that were given no target

- An empty session or pane id is a caller bug, not a no-op success
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: pane_spawn("", "t", "sh", []).pane_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-005
step("An empty session or pane id is a caller bug, not a no-op success")
assert_false(pane_select("caret", ""))
assert_false(pane_zoom("", "%1"))
assert_false(pane_kill("caret", ""))
assert_false(pane_send("caret", "", "hello"))
expect(pane_spawn("", "t", "sh", []).pane_id).to_equal("")
```

</details>

#### rejects an unknown pane instead of inventing output for it

- Capture a pane id that no session owns
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: pane_capture("cs-pane-backend-nobody", "no-such-pane", 10).len() equals `0)  # oracle: an unknown pane has no lines`
- Send to it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-005
step("Capture a pane id that no session owns")
expect(pane_capture("cs-pane-backend-nobody", "no-such-pane", 10).len()).to_equal(0)  # oracle: an unknown pane has no lines
step("Send to it")
assert_false(pane_send("cs-pane-backend-nobody", "no-such-pane", "hi"))
```

</details>

### cs pane backend drives a live pane

#### spawns a shell, runs a typed command in it, then maximizes and kills it

- Spawn a real shell in a disposable session, never the operator's own
   - TUI capture: after_step
- Type a command through the pane and wait for the child's answer
- Maximize the pane, then toggle it back
- Kill the pane; the session no longer lists it


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-APP-LLM-CARET-PANE-006
val session = "cs-pane-backend-spec"
step("Spawn a real shell in a disposable session, never the operator's own")
val pane = pane_spawn(session, "spec-shell", _live_shell(), [])
expect(pane.pane_id).to_not_equal("")
expect(pane.pid).to_be_greater_than(0)
var listed = false
for p in pane_list(session):
    if p.pane_id == pane.pane_id:
        listed = true
assert_true(listed)

step("Type a command through the pane and wait for the child's answer")
assert_true(pane_send(session, pane.pane_id, _times_three_line(4711)))
# 14133 = 4711*3, computed by the child; the typed line holds only 4711.
val seen = _await_pane_text(session, pane.pane_id, "14133")
expect(seen).to_contain("14133")

step("Maximize the pane, then toggle it back")
assert_true(pane_zoom(session, pane.pane_id))
var zoomed = false
for p in pane_list(session):
    if p.pane_id == pane.pane_id and p.zoomed:
        zoomed = true
assert_true(zoomed)
assert_true(pane_zoom(session, pane.pane_id))

step("Kill the pane; the session no longer lists it")
assert_true(pane_kill(session, pane.pane_id))
var still = false
for p in pane_list(session):
    if p.pane_id == pane.pane_id:
        still = true
assert_false(still)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
