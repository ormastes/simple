# Adversarial: Sealed / No-Ambient + Token Confusion (OCap Hardening)

> These specs attack the LLM-session sealing model and the type/port safety of capability matching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adversarial: Sealed / No-Ambient + Token Confusion (OCap Hardening)

These specs attack the LLM-session sealing model and the type/port safety of capability matching.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-OCAP-HARDEN |
| Category | Runtime / Security (adversarial) |
| Difficulty | 4/5 |
| Status | Implemented |
| Plan | doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1) |
| Source | `test/01_unit/os/security/adversarial_sealed_confusion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These specs attack the LLM-session sealing model and the type/port safety of
capability matching.

Requirement 4 (sealed / no-ambient):
  - a sealed session denies any cap not explicitly granted;
  - an UNSEALED session denies everything (fail-closed default), even when its
    caps list holds a real token — a construction bug can never leak authority;
  - `resolve_tool` returns nil for any tool whose cap is absent, and the tool
    name is not even ENUMERABLE (no probing surface);
  - the ambient allow-all hole is UNREACHABLE from the spawn primitives (their
    output is always pledged).

Requirement 5 (token forgery / confusion):
  - a cap of the wrong KIND (FileRead where IpcConnect is required, etc.) is
    denied;
  - a mismatched port / object / generation is denied (no confusion across
    designations).

## Scenarios

### adversarial sealed: a sealed session denies un-granted authority

#### the session is sealed and holds its granted ticket cap

- the session is sealed and holds its granted ticket cap
   - Expected: s.sealed is true
   - Expected: s.can(_tickets()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the session is sealed and holds its granted ticket cap")
val s = ticketing_session()
expect(s.sealed).to_equal(true)
expect(s.can(_tickets())).to_equal(true)
```

</details>

#### it denies FileWrite, calendar, and ProcessSpawn (no ambient authority)

- it denies FileWrite, calendar, and ProcessSpawn (no ambient authority)
   - Expected: s.can(_fwrite_var()) is false
   - Expected: s.can(_calendar_ro()) is false
   - Expected: s.can(CapabilityKind.ProcessSpawn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("it denies FileWrite, calendar, and ProcessSpawn (no ambient authority)")
val s = ticketing_session()
expect(s.can(_fwrite_var())).to_equal(false)
expect(s.can(_calendar_ro())).to_equal(false)
expect(s.can(CapabilityKind.ProcessSpawn)).to_equal(false)
```

</details>

#### an UNSEALED session denies EVERYTHING even with a real cap in its list

- an UNSEALED session denies EVERYTHING even with a real cap in its list
   - Expected: bug.can(_tickets()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("an UNSEALED session denies EVERYTHING even with a real cap in its list")
val bug = LlmSession(role: "x", session_id: 1u64, image_hash: IMG, caps: CapabilitySet(caps: [_tok(_tickets(), 1u64, 1u64, 2)], is_pledged: true), sealed: false, rejected: 0, grant_labels: [])
expect(bug.can(_tickets())).to_equal(false)
```

</details>

### adversarial sealed: resolve_tool has no probing surface
_An absent capability makes the tool nil AND un-enumerable._

#### resolve_tool returns nil for every un-granted tool

- resolve_tool returns nil for every un-granted tool
   - Expected: resolve_tool(s, "file_write") equals `nil`
   - Expected: resolve_tool(s, "system_exec") equals `nil`
   - Expected: resolve_tool(s, "process_spawn") equals `nil`
   - Expected: resolve_tool(s, "calendar_write") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolve_tool returns nil for every un-granted tool")
val s = ticketing_session()
expect(resolve_tool(s, "file_write")).to_equal(nil)
expect(resolve_tool(s, "system_exec")).to_equal(nil)
expect(resolve_tool(s, "process_spawn")).to_equal(nil)
expect(resolve_tool(s, "calendar_write")).to_equal(nil)
```

</details>

#### resolve_tool returns the ticket tool the role WAS granted

- resolve_tool returns the ticket tool the role WAS granted
   - Expected: resolve_tool(s, "ticket_submit") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolve_tool returns the ticket tool the role WAS granted")
val s = ticketing_session()
expect(resolve_tool(s, "ticket_submit") != nil).to_equal(true)
```

</details>

#### an un-granted tool is not even ENUMERABLE in the visible menu

- an un-granted tool is not even ENUMERABLE in the visible menu
   - Expected: _names_has(names, "ticket_submit") is true
   - Expected: _names_has(names, "file_write") is false
   - Expected: _names_has(names, "system_exec") is false
   - Expected: _names_has(names, "calendar_write") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("an un-granted tool is not even ENUMERABLE in the visible menu")
val s = ticketing_session()
val names = available_tool_names(s, os_mcp_tool_cap_map())
expect(_names_has(names, "ticket_submit")).to_equal(true)
expect(_names_has(names, "file_write")).to_equal(false)
expect(_names_has(names, "system_exec")).to_equal(false)
expect(_names_has(names, "calendar_write")).to_equal(false)
```

</details>

#### a completely unknown tool name is nil (indistinguishable from denied)

- a completely unknown tool name is nil (indistinguishable from denied)
   - Expected: resolve_tool(s, "no_such_tool_xyz") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a completely unknown tool name is nil (indistinguishable from denied)")
val s = ticketing_session()
expect(resolve_tool(s, "no_such_tool_xyz")).to_equal(nil)
```

</details>

### adversarial sealed: the ambient allow-all hole is unreachable
_spawn_with_cspace / fork / spawn_llm always emit a pledged set._

#### an empty recipe yields a pledged (deny-all) set, never ambient full

- an empty recipe yields a pledged (deny-all) set, never ambient full
   - Expected: em.caps.is_pledged is true
   - Expected: em.caps.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("an empty recipe yields a pledged (deny-all) set, never ambient full")
val em = spawn_with_cspace(make_orch(), SpawnSpec(image_hash: IMG, grants: [], isolation: "s", budget: 0u64), 22u64, 5000u64, 600u64)
expect(em.caps.is_pledged).to_equal(true)
expect(em.caps.caps.len()).to_equal(0)
```

</details>

#### forking ambient full() yields a pledged empty set (deny-all)

- forking ambient full() yields a pledged empty set (deny-all)
   - Expected: fk.caps.is_pledged is true
   - Expected: fk.caps.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("forking ambient full() yields a pledged empty set (deny-all)")
val fk = fork_cspace(spawn_full(), 23u64, 6000u64, 700u64)
expect(fk.caps.is_pledged).to_equal(true)
expect(fk.caps.caps.len()).to_equal(0)
```

</details>

#### spawn_llm from an ambient full() parent grants nothing (all rejected)

- spawn_llm from an ambient full() parent grants nothing (all rejected)
   - Expected: amb.sealed is true
   - Expected: amb.can(_tickets()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("spawn_llm from an ambient full() parent grants nothing (all rejected)")
val amb = spawn_llm(spawn_full(), ticketing_spec(), "t", 8u64, 24u64, 7000u64, 800u64)
expect(amb.sealed).to_equal(true)
expect(amb.rejected).to_be_greater_than(0)
expect(amb.can(_tickets())).to_equal(false)
```

</details>

### adversarial confusion: wrong-KIND caps never satisfy a requirement
_capability_kind_allows never crosses capability kinds._

#### FileRead cannot satisfy IpcConnect

- FileRead cannot satisfy IpcConnect
   - Expected: capability_kind_allows(CapabilityKind.FileRead(path_prefix: "/"), _window()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("FileRead cannot satisfy IpcConnect")
expect(capability_kind_allows(CapabilityKind.FileRead(path_prefix: "/"), _window())).to_equal(false)
```

</details>

#### IpcConnect cannot satisfy FileRead

- IpcConnect cannot satisfy FileRead
   - Expected: capability_kind_allows(_window(), CapabilityKind.FileRead(path_prefix: "/")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("IpcConnect cannot satisfy FileRead")
expect(capability_kind_allows(_window(), CapabilityKind.FileRead(path_prefix: "/"))).to_equal(false)
```

</details>

#### ProcessSpawn cannot satisfy ProcessSignalAny (spawn is not kill)

- ProcessSpawn cannot satisfy ProcessSignalAny (spawn is not kill)
   - Expected: capability_kind_allows(CapabilityKind.ProcessSpawn, CapabilityKind.ProcessSignalAny) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("ProcessSpawn cannot satisfy ProcessSignalAny (spawn is not kill)")
expect(capability_kind_allows(CapabilityKind.ProcessSpawn, CapabilityKind.ProcessSignalAny)).to_equal(false)
```

</details>

#### a FileRead-only session cannot resolve an IPC-gated tool

- a FileRead-only session cannot resolve an IPC-gated tool
   - Expected: s.can(CapabilityKind.FileRead(path_prefix: "/etc")) is true
   - Expected: resolve_tool(s, "window_create") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a FileRead-only session cannot resolve an IPC-gated tool")
val fr_parent = CapabilitySet(caps: [_tok(CapabilityKind.FileRead(path_prefix: "/"), 1u64, 210u64, 2)], is_pledged: true)
val fr_spec = SpawnSpec(image_hash: IMG, grants: [CapGrant(label: "fs.read", requested: CapabilityKind.FileRead(path_prefix: "/"), atten: atten_identity())], isolation: "s", budget: 0u64)
val s = spawn_llm(fr_parent, fr_spec, "reader", 6u64, 26u64, 8000u64, 900u64)
expect(s.can(CapabilityKind.FileRead(path_prefix: "/etc"))).to_equal(true)
expect(resolve_tool(s, "window_create")).to_equal(nil)
```

</details>

### adversarial confusion: mismatched designation is denied
_Port / object / generation confusion never leaks authority._

#### IpcConnect port confusion: svc.window does not grant svc.tickets

- IpcConnect port confusion: svc.window does not grant svc.tickets
   - Expected: capability_kind_allows(_window(), _tickets()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("IpcConnect port confusion: svc.window does not grant svc.tickets")
expect(capability_kind_allows(_window(), _tickets())).to_equal(false)
```

</details>

#### a window-only session cannot resolve the ticket tool

- a window-only session cannot resolve the ticket tool
   - Expected: ws.can(_window()) is true
   - Expected: resolve_tool(ws, "window_create") != nil is true
   - Expected: resolve_tool(ws, "ticket_submit") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a window-only session cannot resolve the ticket tool")
val ws = spawn_llm(CapabilitySet(caps: [_tok(_window(), 1u64, 220u64, 2)], is_pledged: true), window_spec(), "window", 5u64, 25u64, 8500u64, 950u64)
expect(ws.can(_window())).to_equal(true)
expect(resolve_tool(ws, "window_create") != nil).to_equal(true)
expect(resolve_tool(ws, "ticket_submit")).to_equal(nil)
```

</details>

#### SharedDataset stale generation is denied (generation mismatch)

- SharedDataset stale generation is denied (generation mismatch)
   - Expected: capability_kind_allows(held, stale) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("SharedDataset stale generation is denied (generation mismatch)")
val held = CapabilityKind.SharedDataset(object_id: CAL_OBJ, generation: 7u64, rights: CAP_RIGHT_READ)
val stale = CapabilityKind.SharedDataset(object_id: CAL_OBJ, generation: 8u64, rights: CAP_RIGHT_READ)
expect(capability_kind_allows(held, stale)).to_equal(false)
```

</details>

#### SharedDataset wrong object id is denied

- SharedDataset wrong object id is denied
   - Expected: capability_kind_allows(held, other) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("SharedDataset wrong object id is denied")
val held = CapabilityKind.SharedDataset(object_id: CAL_OBJ, generation: 7u64, rights: CAP_RIGHT_READ)
val other = CapabilityKind.SharedDataset(object_id: 9999u64, generation: 7u64, rights: CAP_RIGHT_READ)
expect(capability_kind_allows(held, other)).to_equal(false)
```

</details>

#### ProcessQueue wrong queue id is denied

- ProcessQueue wrong queue id is denied
   - Expected: capability_kind_allows(held, other) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("ProcessQueue wrong queue id is denied")
val held = CapabilityKind.ProcessQueue(queue_id: 5u64, generation: 1u64, rights: CAP_RIGHT_QUEUE_SUBMIT)
val other = CapabilityKind.ProcessQueue(queue_id: 6u64, generation: 1u64, rights: CAP_RIGHT_QUEUE_SUBMIT)
expect(capability_kind_allows(held, other)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3fbcfa5a288ac251f35f952ef9c2b362fb5740fd6d11ad58491b55a3a1b0675c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fbcfa5a288ac251f35f952ef9c2b362fb5740fd6d11ad58491b55a3a1b0675c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fbcfa5a288ac251f35f952ef9c2b362fb5740fd6d11ad58491b55a3a1b0675c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/security/adversarial_sealed_confusion_spec.spl
mirror: doc/06_spec/01_unit/os/security/adversarial_sealed_confusion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/security/adversarial_sealed_confusion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/security/adversarial_sealed_confusion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/security/adversarial_sealed_confusion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/security/adversarial_sealed_confusion_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the session is sealed and holds its granted ticket cap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/adversarial_sealed_confusion_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'it denies FileWrite, calendar, and ProcessSpawn (no ambient authority)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/adversarial_sealed_confusion_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an UNSEALED session denies EVERYTHING even with a real cap in its list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
