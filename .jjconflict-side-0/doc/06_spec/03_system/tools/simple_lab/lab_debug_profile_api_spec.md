# Simple Lab debug/profile API — real loopback system spec (Stream P10)

> `start_lab_server` polls for the portfile with `while waited < 150000` and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Lab debug/profile API — real loopback system spec (Stream P10)

`start_lab_server` polls for the portfile with `while waited < 150000` and the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/simple_lab/lab_debug_profile_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Poll-loop constants are load-bearing — do not "tidy" them

`start_lab_server` polls for the portfile with `while waited < 150000` and the
success path sets `waited = 150000` to leave the loop. An earlier revision of
the sibling spec set `15000` there instead: that never satisfies the guard, and
because a non-empty `bound` also skips the only branch that advances `waited`,
the loop spun forever — the spec hung past 700s on a one-digit typo. Both
constants must stay 150000, and the `if bound == ""` branch must remain the
sleep-and-advance path.

Design: doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md §9
Plan:   doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md (P10)

## Scenarios

### Simple Lab debug/profile API (real loopback, ref lane)

#### attaches a ref lane and reports a live stop state over real HTTP

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- attaches a ref lane and reports a live stop state over real HTTP
- POST .../debug attaches the host SVM-G ref lane — no GPU involved
   - Expected: attach.ok is true
   - Expected: attach.status equals `200`
- the lane reports the Emulated profile tier, and says profiling was armed AT ATTACH
- a freshly attached target is stopped at entry in SVM-G pc units
   - Expected: json_raw_field(attach.body, "pc") equals `0`
- GET .../debug/state is a PURE read — it does not advance execution
   - Expected: s1.status equals `200`
   - Expected: json_raw_field(s1.body, "pc") equals `0`
   - Expected: json_raw_field(s2.body, "pc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches a ref lane and reports a live stop state over real HTTP")
val server = start_lab_server(30)
if not server.started:
    fail("lab_server subprocess did not start listening")

val sid = create_session(server.addr)
expect(sid).to_start_with("sess_")

step("POST .../debug attaches the host SVM-G ref lane — no GPU involved")
val attach = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug", attach_body(true))
expect(attach.ok).to_equal(true)
expect(attach.status).to_equal(200)
expect(attach.headers.to_lower()).to_contain("x-lab-protocol-version: 1")
expect(attach.body).to_contain("\"kind\":\"ref\"")

step("the lane reports the Emulated profile tier, and says profiling was armed AT ATTACH")
expect(attach.body).to_contain("\"profile_level\":\"emulated\"")
expect(attach.body).to_contain("\"profile_armed_at_attach\":true")

step("a freshly attached target is stopped at entry in SVM-G pc units")
expect(attach.body).to_contain("\"pc_kind\":\"svmg_pc\"")
expect(json_raw_field(attach.body, "pc")).to_equal("0")

step("GET .../debug/state is a PURE read — it does not advance execution")
val s1 = http_request(server.addr, "GET", "/api/lab/sessions/{sid}/debug/state", "")
val s2 = http_request(server.addr, "GET", "/api/lab/sessions/{sid}/debug/state", "")
expect(s1.status).to_equal(200)
expect(json_raw_field(s1.body, "pc")).to_equal("0")
expect(json_raw_field(s2.body, "pc")).to_equal("0")

server.stop()
```

</details>

#### steps one instruction at a time and stops on a real breakpoint via resume

- steps one instruction at a time and stops on a real breakpoint via resume
- POST .../debug/step advances exactly one instruction (PUSHI is 5 bytes)
   - Expected: st1.status equals `200`
   - Expected: json_raw_field(st1.body, "pc") equals `{PC_PUSHI2}`
- the step really mutated SERVER-SIDE state — the stack grew by one
   - Expected: json_raw_field(st1.body, "sp") equals `1`
- POST .../debug/break sets a breakpoint on ADD and reports it back
   - Expected: bp.status equals `200`
- setting the SAME breakpoint again is idempotent: changed=false, still one entry
- POST .../debug/resume runs until that breakpoint, not to completion
   - Expected: res.status equals `200`
   - Expected: json_raw_field(res.body, "pc") equals `{PC_ADD}`
- the three PUSHIs ran and ADD did NOT — proven by the live stack, not by the pc alone
- clearing the breakpoint and resuming again runs to a terminal halt


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("steps one instruction at a time and stops on a real breakpoint via resume")
val server = start_lab_server(30)
if not server.started:
    fail("lab_server subprocess did not start listening")
val sid = create_session(server.addr)
val _a = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug", attach_body(true))

step("POST .../debug/step advances exactly one instruction (PUSHI is 5 bytes)")
val st1 = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/step", "")
expect(st1.status).to_equal(200)
expect(json_raw_field(st1.body, "pc")).to_equal("{PC_PUSHI2}")
expect(st1.body).to_contain("\"stop_reason\":\"step\"")

step("the step really mutated SERVER-SIDE state — the stack grew by one")
expect(st1.body).to_contain("\"stack\":[1]")
expect(json_raw_field(st1.body, "sp")).to_equal("1")

step("POST .../debug/break sets a breakpoint on ADD and reports it back")
val bp = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/break", break_body(PC_ADD, false))
expect(bp.status).to_equal(200)
expect(bp.body).to_contain("\"changed\":true")
expect(bp.body).to_contain("\"breakpoints\":[{PC_ADD}]")

step("setting the SAME breakpoint again is idempotent: changed=false, still one entry")
val bp2 = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/break", break_body(PC_ADD, false))
expect(bp2.body).to_contain("\"changed\":false")
expect(bp2.body).to_contain("\"breakpoints\":[{PC_ADD}]")

step("POST .../debug/resume runs until that breakpoint, not to completion")
val res = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/resume", "")
expect(res.status).to_equal(200)
expect(json_raw_field(res.body, "pc")).to_equal("{PC_ADD}")
expect(res.body).to_contain("\"stop_reason\":\"breakpoint\"")

step("the three PUSHIs ran and ADD did NOT — proven by the live stack, not by the pc alone")
expect(res.body).to_contain("\"stack\":[1,3,4]")

step("clearing the breakpoint and resuming again runs to a terminal halt")
val clr = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/break", break_body(PC_ADD, true))
expect(clr.body).to_contain("\"changed\":true")
expect(clr.body).to_contain("\"breakpoints\":[]")
val done = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/resume", "")
expect(done.body).to_contain("\"stop_reason\":\"halt\"")

server.stop()
```

</details>

#### profile begin/end over the wire reports the Emulated tier with EXACT steps and absent device time

- profile begin/end over the wire reports the Emulated tier with EXACT steps and absent device time
- POST .../debug/profile/begin opens a window on the already-armed target
   - Expected: begin.status equals `200`
- resume the whole program inside the window
- POST .../debug/profile/end returns a ProfileReport with an EXACT step count
   - Expected: end.status equals `200`
   - Expected: json_raw_field(end.body, "steps") equals `{ADD_PROGRAM_STEPS}`
- device time is ABSENT on a lane with no device — JSON null, never 0 and never -1
   - Expected: json_raw_field(end.body, "device_ns") equals `null`
- wall time IS measured at every tier, so it is a real non-null number
   - Expected: wall == "null" is false
   - Expected: wall == "" is false
- `detail` names exactly which pieces were measured, per the tier contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("profile begin/end over the wire reports the Emulated tier with EXACT steps and absent device time")
val server = start_lab_server(30)
if not server.started:
    fail("lab_server subprocess did not start listening")
val sid = create_session(server.addr)
val _a = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug", attach_body(true))

step("POST .../debug/profile/begin opens a window on the already-armed target")
val begin = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/profile/begin", "")
expect(begin.status).to_equal(200)
expect(begin.body).to_contain("\"begun\":true")
expect(begin.body).to_contain("\"profile_level\":\"emulated\"")

step("resume the whole program inside the window")
val res = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/resume", "")
expect(res.body).to_contain("\"stop_reason\":\"halt\"")

step("POST .../debug/profile/end returns a ProfileReport with an EXACT step count")
val end = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/profile/end", "")
expect(end.status).to_equal(200)
expect(end.body).to_contain("\"level\":\"emulated\"")
expect(json_raw_field(end.body, "steps")).to_equal("{ADD_PROGRAM_STEPS}")
expect(end.body).to_contain("\"steps_present\":true")

step("device time is ABSENT on a lane with no device — JSON null, never 0 and never -1")
expect(json_raw_field(end.body, "device_ns")).to_equal("null")
expect(end.body).to_contain("\"device_time_present\":false")

step("wall time IS measured at every tier, so it is a real non-null number")
val wall = json_raw_field(end.body, "wall_ns")
expect(wall == "null").to_equal(false)
expect(wall == "").to_equal(false)

step("`detail` names exactly which pieces were measured, per the tier contract")
expect(end.body).to_contain("steps=exact")
expect(end.body).to_contain("device=none")

server.stop()
```

</details>

#### a lane attached with profile:false stays Unavailable — begin/end never re-arms it

- a lane attached with profile:false stays Unavailable — begin/end never re-arms it
- attach with {"profile":false} — profiling is armed AT ATTACH and nowhere else
   - Expected: attach.status equals `200`
- begin + resume + end still runs, but end refuses to invent numbers
   - Expected: end.status equals `200`
- EVERY quantity is null — a zero here would chart as a real measurement
   - Expected: json_raw_field(end.body, "steps") equals `null`
   - Expected: json_raw_field(end.body, "wall_ns") equals `null`
   - Expected: json_raw_field(end.body, "device_ns") equals `null`
- and it says WHY, naming the attach-time lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a lane attached with profile:false stays Unavailable — begin/end never re-arms it")
val server = start_lab_server(30)
if not server.started:
    fail("lab_server subprocess did not start listening")
val sid = create_session(server.addr)

step("attach with {\"profile\":false} — profiling is armed AT ATTACH and nowhere else")
val attach = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug", attach_body(false))
expect(attach.status).to_equal(200)
expect(attach.body).to_contain("\"profile_level\":\"unavailable\"")
expect(attach.body).to_contain("\"profile_armed_at_attach\":false")

step("begin + resume + end still runs, but end refuses to invent numbers")
val _b = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/profile/begin", "")
val _r = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/resume", "")
val end = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/profile/end", "")
expect(end.status).to_equal(200)
expect(end.body).to_contain("\"level\":\"unavailable\"")

step("EVERY quantity is null — a zero here would chart as a real measurement")
expect(json_raw_field(end.body, "steps")).to_equal("null")
expect(json_raw_field(end.body, "wall_ns")).to_equal("null")
expect(json_raw_field(end.body, "device_ns")).to_equal("null")
expect(end.body).to_contain("\"steps_present\":false")

step("and it says WHY, naming the attach-time lifecycle")
expect(end.body).to_contain("profiling-disabled-at-attach")

server.stop()
```

</details>

#### %profile magic measures a cell body on a fresh ref lane, needing no prior attach

- %profile magic measures a cell body on a fresh ref lane, needing no prior attach
- POST .../profile with a %profile cell — note NO .../debug attach happened first
   - Expected: resp.status equals `200`
- the report is Emulated with the same EXACT step count the trait-level spec pins
   - Expected: json_raw_field(resp.body, "steps") equals `{ADD_PROGRAM_STEPS}`
   - Expected: json_raw_field(resp.body, "device_ns") equals `null`
- a cell that is NOT a %profile cell is handed back unhandled, code intact
   - Expected: plain.status equals `200`
- a BARE %profile with no attached lane reports absence, never a zero window
   - Expected: bare.status equals `200`
   - Expected: json_raw_field(bare.body, "steps") equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("%profile magic measures a cell body on a fresh ref lane, needing no prior attach")
val server = start_lab_server(30)
if not server.started:
    fail("lab_server subprocess did not start listening")
val sid = create_session(server.addr)

step("POST .../profile with a %profile cell — note NO .../debug attach happened first")
val cell = profile_cell_body("%profile\\n{ADD_PROGRAM}")
val resp = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/profile", cell)
expect(resp.status).to_equal(200)
expect(resp.body).to_contain("\"handled\":true")

step("the report is Emulated with the same EXACT step count the trait-level spec pins")
expect(resp.body).to_contain("\"level\":\"emulated\"")
expect(json_raw_field(resp.body, "steps")).to_equal("{ADD_PROGRAM_STEPS}")
expect(json_raw_field(resp.body, "device_ns")).to_equal("null")

step("a cell that is NOT a %profile cell is handed back unhandled, code intact")
val plain = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/profile", profile_cell_body("print(1)"))
expect(plain.status).to_equal(200)
expect(plain.body).to_contain("\"handled\":false")
expect(plain.body).to_contain("print(1)")

step("a BARE %profile with no attached lane reports absence, never a zero window")
val bare = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/profile", profile_cell_body("%profile"))
expect(bare.status).to_equal(200)
expect(bare.body).to_contain("\"level\":\"unavailable\"")
expect(bare.body).to_contain("no-debug-lane-attached")
expect(json_raw_field(bare.body, "steps")).to_equal("null")

server.stop()
```

</details>

#### debug endpoints 404 on an unknown session and on an unattached lane, and never wedge the server

- debug endpoints 404 on an unknown session and on an unattached lane, and never wedge the server
- unknown session -> 404 with the version header
   - Expected: unknown.status equals `404`
- known session but no attached lane -> 404 naming that specific cause
   - Expected: unattached.status equals `404`
- an empty SVM-G source is a client ERROR (400), never a silent empty attach
   - Expected: bad.status equals `400`
- the server is still alive and answers the next request
   - Expected: status_resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("debug endpoints 404 on an unknown session and on an unattached lane, and never wedge the server")
val server = start_lab_server(30)
if not server.started:
    fail("lab_server subprocess did not start listening")
val sid = create_session(server.addr)

step("unknown session -> 404 with the version header")
val unknown = http_request(server.addr, "POST", "/api/lab/sessions/sess_nope/debug/step", "")
expect(unknown.status).to_equal(404)
expect(unknown.headers.to_lower()).to_contain("x-lab-protocol-version: 1")

step("known session but no attached lane -> 404 naming that specific cause")
val unattached = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug/step", "")
expect(unattached.status).to_equal(404)
expect(unattached.body).to_contain("no debug lane attached")

step("an empty SVM-G source is a client ERROR (400), never a silent empty attach")
val bad = http_request(server.addr, "POST", "/api/lab/sessions/{sid}/debug", profile_cell_body(""))
expect(bad.status).to_equal(400)

step("the server is still alive and answers the next request")
val status_resp = http_request(server.addr, "GET", "/api/lab/status", "")
expect(status_resp.status).to_equal(200)

server.stop()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `963cca6346d08e87e3bcc8d77026d27573e0f61a5cdbb05bdb4bd5e0abe8f8f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `963cca6346d08e87e3bcc8d77026d27573e0f61a5cdbb05bdb4bd5e0abe8f8f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `963cca6346d08e87e3bcc8d77026d27573e0f61a5cdbb05bdb4bd5e0abe8f8f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/simple_lab/lab_debug_profile_api_spec.spl
mirror: doc/06_spec/03_system/tools/simple_lab/lab_debug_profile_api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/simple_lab/lab_debug_profile_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/simple_lab/lab_debug_profile_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/simple_lab/lab_debug_profile_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/simple_lab/lab_debug_profile_api_spec.spl:263:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaches a ref lane and reports a live stop state over real HTTP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/simple_lab/lab_debug_profile_api_spec.spl:297:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'steps one instruction at a time and stops on a real breakpoint via resume' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/simple_lab/lab_debug_profile_api_spec.spl:345:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'profile begin/end over the wire reports the Emulated tier with EXACT steps and absent device time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
