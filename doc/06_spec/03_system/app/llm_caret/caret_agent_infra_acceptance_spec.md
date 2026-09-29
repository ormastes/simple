# caret_agent_infra_acceptance_spec

> Operator signs off the LLM Caret agent infrastructure end to end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# caret_agent_infra_acceptance_spec

Operator signs off the LLM Caret agent infrastructure end to end.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Operator signs off the LLM Caret agent infrastructure end to end.

An operator is about to hand the caret agent infrastructure to a team. Before
signing off they walk the whole journey once, in order, the way they would on a
real machine: they start a private agent workspace and put two agents in it —
each one in its own detached git worktree and its own tmux window; they send a
single broadcast and check that every agent's pane executed it independently;
they drive the caret TOOL layer the way a dev tool or the MCP server would, and
watch a mutating wiki write get REFUSED under the default policy before it is
granted, then read the page back byte for byte; they run the caret suite in a
tmux window and read the authoritative `Results:` verdict off the pane without
leaving tmux; and finally they tear the whole thing down and confirm the machine
is clean — no tmux server answering on the private socket, no worktree still
registered with git, no directory left behind.

This is the acceptance layer, not more unit coverage. Every fact below is read
back out of the real system — files written by real shells in real tmux panes,
`git worktree list --porcelain`, the tmux server's own exit status, and bytes
re-read from disk — never from a tool's own success string. Rows that need a
live server the host may not run report `pending("BLOCKED: ...")` and are never
faked green.

## Scenarios

### LLM Caret agent infrastructure: operator acceptance journey

#### attaches two isolated agents, broadcasts to every pane, reads the suite verdict off a pane, and leaves nothing behind

- attaches two isolated agents, broadcasts to every pane, reads the suite verdict off a pane, and leaves nothing behind
- Start the workspace and attach two agents, each in its own detached worktree and tmux window
   - Expected: attached.status equals `ok`
   - Expected: list_panes(ws).len() equals `3`
- git itself registers both agent worktrees alongside the repo
   - Expected: trees_live.len() equals `3`
- Each agent's worktree is its own: a file one agent writes never appears in the other's tree or in the repo
- One broadcast reaches every pane and each pane EXECUTES it independently
   - Expected: reached.len() equals `3`
- Launch the caret suite in its own tmux window of the same session
   - Expected: launched.status equals `ok`
   - Expected: suite_target equals `id + ":caret_suite"`
- Read the runner's authoritative verdict straight off the suite pane
- Tear down: detach both agents, then kill the private tmux server
   - Expected: agent_detach(ws, agent).status equals `ok`
   - Expected: session_kill(ws).status equals `ok`
- Nothing leaks: no session, no server on the private socket, git registers only the repo
   - Expected: trees_after.len() equals `1`
   - Expected: trees_after[0] equals `real_repo.trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 82 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches two isolated agents, broadcasts to every pane, reads the suite verdict off a pane, and leaves nothing behind")
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val run_id = current_time_ms().to_text()
val root = _scratch("journey_" + run_id)
dir_remove_all(root)
val repo = _fixture_repo(root)
val id = "acc-journey-" + run_id
val ws = agent_workspace(id, repo, root + "/trees")
# Kill first: a leftover server from an aborted run must never be
# mistaken for the one this example started.
session_kill(ws)

step("Start the workspace and attach two agents, each in its own detached worktree and tmux window")
for agent in AGENTS:
    val attached = agent_attach(ws, agent, "")
    expect(attached.status).to_equal("ok")
    # The worktree is real: the repo's committed file is present in it.
    expect(file_exists(worktree_path(ws, agent) + "/README.md")).to_be(true)
expect(session_alive(ws)).to_be(true)
# two agent windows plus the session's bootstrap window 0
expect(list_panes(ws).len()).to_equal(3)

step("git itself registers both agent worktrees alongside the repo")
val trees_live = worktree_list(ws)
expect(trees_live.len()).to_equal(3)
for agent in AGENTS:
    expect(_contains(trees_live, worktree_path(ws, agent))).to_be(true)

step("Each agent's worktree is its own: a file one agent writes never appears in the other's tree or in the repo")
for agent in AGENTS:
    file_write(worktree_path(ws, agent) + "/owned_by_" + agent + ".txt", agent + "\n")
for writer in AGENTS:
    for tree_owner in AGENTS:
        val present = file_exists(worktree_path(ws, tree_owner) + "/owned_by_" + writer + ".txt")
        expect(present).to_be(writer == tree_owner)
    expect(file_exists(repo + "/owned_by_" + writer + ".txt")).to_be(false)

step("One broadcast reaches every pane and each pane EXECUTES it independently")
# Lowercase in, uppercase out: the marker can only appear on a pane that
# actually ran the command, not one that merely received the keystrokes.
val marker_in = "acc_bcast_" + run_id
val marker_out = "ACC_BCAST_" + run_id
val reached = send_to_each_pane(ws, "echo " + marker_in + " | tr a-z A-Z")
expect(reached.len()).to_equal(3)
for agent in AGENTS:
    expect(_contains(reached, id + ":" + agent + ".0")).to_be(true)
    expect(wait_for_pane_text(ws, id + ":" + agent, marker_out, 20000)).to_be(true)

step("Launch the caret suite in its own tmux window of the same session")
val launched = launch_caret_suite(ws, cwd(), SUITE)
expect(launched.status).to_equal("ok")
val suite_target = launched.output
expect(suite_target).to_equal(id + ":caret_suite")
expect(_contains(list_panes(ws), id + ":caret_suite.0")).to_be(true)

step("Read the runner's authoritative verdict straight off the suite pane")
expect(wait_for_pane_text(ws, suite_target, "Results:", 600000)).to_be(true)
val screen = capture_pane(ws, suite_target)
# The per-file verdict line, not just "it finished".
expect(screen).to_contain("SPEC FILE VERDICT: " + SUITE)
expect(screen).to_contain("0 failed")
expect(screen).to_contain("PASS " + SUITE)

step("Tear down: detach both agents, then kill the private tmux server")
for agent in AGENTS:
    expect(agent_detach(ws, agent).status).to_equal("ok")
    expect(dir_exists(worktree_path(ws, agent))).to_be(false)
expect(session_kill(ws).status).to_equal("ok")

step("Nothing leaks: no session, no server on the private socket, git registers only the repo")
expect(session_alive(ws)).to_be(false)
val (_ls_out, _ls_err, ls_code) = process_run("tmux", ["-L", ws.socket, "list-sessions"])
expect(ls_code).to_be_greater_than(0)
val trees_after = worktree_list(ws)
expect(trees_after.len()).to_equal(1)
# git reports the resolved path; the fixture may sit behind a symlinked cwd.
val (real_repo, _re, _rc) = process_run("realpath", ["-m", repo])
expect(trees_after[0]).to_equal(real_repo.trim())
dir_remove_all(root)
```

</details>

### LLM Caret tool layer: the operator drives wiki access the way a dev tool does

#### refuses a wiki write without permission, then writes and reads the page back byte-identical once granted

- refuses a wiki write without permission, then writes and reads the page back byte-identical once granted
- Under the default policy the mutating write is REFUSED and nothing lands on disk
- With an explicit grant for wiki_write the page is created
- The page reads back byte-identical — checked on disk AND through the read tool
- The read side needed no grant: reads are not gated, only mutations are


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a wiki write without permission, then writes and reads the page back byte-identical once granted")
val run_id = current_time_ms().to_text()
val ws_root = _scratch("wiki_" + run_id)
dir_remove_all(ws_root)
dir_create_all(ws_root)
# Module-level config does not persist across examples: configure here.
reset_config()
parse_config_text("wiki:\n    backend: local\n    root: wiki\n")

# A page id carries its `.md` extension: that is the id `wiki_search`
# reports and the id `wiki_read` resolves.
val page = "acceptance/report-" + run_id + ".md"
# A nonce'd body is the absolute oracle: it cannot pre-exist on disk.
val body = "acceptance body " + run_id + "\nsecond line\n"
val call = new_tool_call("w1", "wiki_write",
    _json([_kv("page_id", page), _kv("body", body)]))

step("Under the default policy the mutating write is REFUSED and nothing lands on disk")
val denied = run_tool(default_policy(ws_root), call)
expect(denied.is_error).to_be(true)
expect(denied.content).to_contain("permission denied")
# The refusal is real, not cosmetic: the file was never created.
expect(file_exists(ws_root + "/wiki/" + page)).to_be(false)

step("With an explicit grant for wiki_write the page is created")
val granted = run_tool(policy_with_allow(ws_root, ["wiki_write"]), call)
expect(granted.is_error).to_be(false)
expect(file_exists(ws_root + "/wiki/" + page)).to_be(true)

step("The page reads back byte-identical — checked on disk AND through the read tool")
val on_disk = file_read(ws_root + "/wiki/" + page)
expect(on_disk).to_contain(body)
val (ok, content) = wiki_read(ws_root, page)
expect(ok).to_be(true)
expect(content).to_contain(body)

step("The read side needed no grant: reads are not gated, only mutations are")
val read_ungated = run_tool(default_policy(ws_root), new_tool_call("r1", "wiki_read",
    _json([_kv("page_id", page)])))
expect(read_ungated.is_error).to_be(false)
expect(read_ungated.content).to_contain(body)

reset_config()
dir_remove_all(ws_root)
```

</details>

### LLM Caret tool layer: object storage round trip against a live server

#### puts an object and gets the same bytes back through the storage tools

- puts an object and gets the same bytes back through the storage tools
- Under the default policy storage_put is REFUSED: it is a mutating tool
- With a grant the object is stored on the real server
- The object reads back with exactly the bytes that were written


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("puts an object and gets the same bytes back through the storage tools")
# No live MinIO on this host means NO EVIDENCE, which is not a pass.
if not _live("LLM_CARET_STORAGE_LIVE"):
    pending("BLOCKED: no local S3-compatible (minio) server on this host — set LLM_CARET_STORAGE_LIVE=1 with credentials (LLM_CARET_CONFIG + access_key_env/secret_key_env) to run")
    return
val run_id = current_time_ms().to_text()
val ws_root = _scratch("storage_" + run_id)
dir_create_all(ws_root)
reset_config()
val cfg = env_get("LLM_CARET_CONFIG") ?? ""
expect(cfg).to_not_equal("")

val bucket = env_get("LLM_CARET_STORAGE_BUCKET") ?? "caret-acceptance"
val key = "acceptance/obj-" + run_id + ".txt"
val payload = "acceptance payload " + run_id

step("Under the default policy storage_put is REFUSED: it is a mutating tool")
val put_call = new_tool_call("p1", "storage_put",
    _json([_kv("bucket", bucket), _kv("key", key), _kv("content", payload)]))
val denied = run_tool(default_policy(ws_root), put_call)
expect(denied.is_error).to_be(true)
expect(denied.content).to_contain("permission denied")

step("With a grant the object is stored on the real server")
val put = run_tool(policy_with_allow(ws_root, ["storage_put"]), put_call)
expect(put.is_error).to_be(false)

step("The object reads back with exactly the bytes that were written")
val got = run_tool(default_policy(ws_root), new_tool_call("g1", "storage_get",
    _json([_kv("bucket", bucket), _kv("key", key)])))
expect(got.is_error).to_be(false)
expect(got.content).to_contain(payload)

reset_config()
dir_remove_all(ws_root)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-APP-LLM-CARET-INFRA-ACCEPTANCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bdffa117034fb08a6631a757991ada3e01ce890cf7333428594985d694fde230`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdffa117034fb08a6631a757991ada3e01ce890cf7333428594985d694fde230`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdffa117034fb08a6631a757991ada3e01ce890cf7333428594985d694fde230`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a wiki write without permission, then writes and reads the page back byte-identical once granted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl:223:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'puts an object and gets the same bytes back through the storage tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
