# Debug Target Ref Specification

> Tests covering CapLevel — the honesty tier, DebugSessionCore (ref) — attach / accessors / shutdown lifecycle, AttachOpts — the shared attach knobs, DebugTarget (ref) — identity and capability tier, DebugTarget (ref) — breakpoint set/clear/list contract, DebugTarget (ref) — step() advances exactly one instruction, DebugTarget (ref) — resume() and breakpoint stops, DebugTarget (ref) — terminal stop reasons are distinguished, DebugTarget (ref) — state() is a pure read, DebugTarget (ref) — read_mem bounds contract, DebugTarget (ref) — detach, ProfileTarget (ref) — tiered honesty and exact step counts, DebugProfiler group — all-or-nothing acquisition, Cross-backend vector table — the shape later lanes diff against.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Target Ref Specification

## Scenarios

### CapLevel — the honesty tier

#### round-trips every tier through its stable wire name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips every tier through its stable wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every tier through its stable wire name")
assert_equal(cap_level_name(CapLevel.Native), "native")
assert_equal(cap_level_name(CapLevel.Emulated), "emulated")
assert_equal(cap_level_name(CapLevel.Unavailable), "unavailable")
assert_equal(cap_level_name(cap_level_from_name("native")), "native")
assert_equal(cap_level_name(cap_level_from_name("emulated")), "emulated")
assert_equal(cap_level_name(cap_level_from_name("unavailable")), "unavailable")
```

</details>

#### decodes an unknown tier name to Unavailable, never to a working tier

- decodes an unknown tier name to Unavailable, never to a working tier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes an unknown tier name to Unavailable, never to a working tier")
# Fail-CLOSED: a typo or a newer backend's unknown tier must never
# be mistaken for a capability that works.
assert_equal(cap_level_name(cap_level_from_name("Native")), "unavailable")
assert_equal(cap_level_name(cap_level_from_name("")), "unavailable")
assert_equal(cap_level_name(cap_level_from_name("hardware")), "unavailable")
```

</details>

#### treats Native and Emulated as usable and Unavailable as not

- treats Native and Emulated as usable and Unavailable as not


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats Native and Emulated as usable and Unavailable as not")
assert_equal(cap_level_is_usable(CapLevel.Native), true)
assert_equal(cap_level_is_usable(CapLevel.Emulated), true)
assert_equal(cap_level_is_usable(CapLevel.Unavailable), false)
```

</details>

### DebugSessionCore (ref) — attach / accessors / shutdown lifecycle

#### answers kind() before any attach

- answers kind() before any attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers kind() before any attach")
val session = RefDebugSession.new()
assert_equal(session.kind(), REF_KIND)
assert_equal(session.kind(), "ref")
```

</details>

#### returns None from both accessors BEFORE attach

- returns None from both accessors BEFORE attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None from both accessors BEFORE attach")
# None here is a truthful lifecycle absence, not an unimplemented
# hole -- both accessors exist and both answer.
val session = RefDebugSession.new()
assert_true(session.debug() == nil)
assert_true(session.profile() == nil)
```

</details>

#### returns Some from both accessors after a successful attach

- returns Some from both accessors after a successful attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Some from both accessors after a successful attach")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
assert_true(session.debug() != nil)
assert_true(session.profile() != nil)
```

</details>

#### reports attach success as the empty string, classified as ok

- reports attach success as the empty string, classified as ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports attach success as the empty string, classified as ok")
val session = RefDebugSession.new()
val res = session.attach(ADD_PROGRAM, attach_opts_default())
assert_equal(res, "")
assert_equal(attach_is_ok(res), true)
assert_equal(attach_is_skip(res), false)
assert_equal(attach_is_error(res), false)
```

</details>

#### reports an empty program as an ERROR, never as a host skip

- reports an empty program as an ERROR, never as a host skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an empty program as an ERROR, never as a host skip")
# `ref` always exists, so it must never answer "skip:" -- a skip
# from the always-available lane would make every host look
# capability-poor.
val session = RefDebugSession.new()
val res = session.attach("", attach_opts_default())
assert_equal(attach_is_error(res), true)
assert_equal(attach_is_skip(res), false)
assert_equal(attach_is_ok(res), false)
assert_true(res.contains("empty"))
```

</details>

#### leaves the accessors at None after a failed attach

- leaves the accessors at None after a failed attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the accessors at None after a failed attach")
val session = RefDebugSession.new()
session.attach("   ", attach_opts_default())
assert_true(session.debug() == nil)
assert_true(session.profile() == nil)
```

</details>

#### returns None from both accessors after shutdown

- returns None from both accessors after shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None from both accessors after shutdown")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
assert_true(session.debug() != nil)
assert_equal(session.shutdown(), "")
assert_true(session.debug() == nil)
assert_true(session.profile() == nil)
```

</details>

#### is idempotent on shutdown

- is idempotent on shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is idempotent on shutdown")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
assert_equal(session.shutdown(), "")
assert_equal(session.shutdown(), "")
assert_true(session.debug() == nil)
```

</details>

#### classifies the three attach verdicts distinctly

- classifies the three attach verdicts distinctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies the three attach verdicts distinctly")
assert_equal(attach_is_ok(""), true)
assert_equal(attach_is_skip("skip:no cuda device"), true)
assert_equal(attach_is_error("skip:no cuda device"), false)
assert_equal(attach_is_error("error: bad program"), true)
assert_equal(attach_is_ok("error: bad program"), false)
```

</details>

### AttachOpts — the shared attach knobs

#### defaults to a usable budget, entry 0 and profiling armed

- defaults to a usable budget, entry 0 and profiling armed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to a usable budget, entry 0 and profiling armed")
val opts = attach_opts_default()
assert_true(opts.step_budget > 0)
assert_equal(opts.entry_pc, 0)
assert_true(opts.log_cap > 0)
assert_equal(opts.profile, true)
```

</details>

#### honours a caller-supplied step budget

- honours a caller-supplied step budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honours a caller-supplied step budget")
val opts = attach_opts_with_budget(3)
assert_equal(opts.step_budget, 3)
assert_equal(opts.entry_pc, 0)
```

</details>

### DebugTarget (ref) — identity and capability tier

#### reports kind() matching the session that produced it

- reports kind() matching the session that produced it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports kind() matching the session that produced it")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.kind(), REF_KIND)
```

</details>

#### reports Native debug capability (real instruction-level control)

- reports Native debug capability (real instruction-level control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Native debug capability (real instruction-level control)")
# `ref` single-steps the actual interpreter, so its debug control is
# genuine, not synthesized -- Emulated would be a false claim.
val target = _attached_target(ADD_PROGRAM)
assert_equal(cap_level_name(target.debug_level()), "native")
assert_equal(cap_level_is_usable(target.debug_level()), true)
```

</details>

### DebugTarget (ref) — breakpoint set/clear/list contract

#### returns true when a breakpoint is newly added

- returns true when a breakpoint is newly added


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when a breakpoint is newly added")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.set_breakpoint(PC_ADD), true)
assert_equal(target.breakpoints().len(), 1)
assert_equal(target.breakpoints()[0], PC_ADD)
```

</details>

#### returns FALSE when setting an already-present breakpoint (idempotent)

- returns FALSE when setting an already-present breakpoint (idempotent)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns FALSE when setting an already-present breakpoint (idempotent)")
# Idempotent in effect, but the bool distinguishes "added" from
# "already there" -- a DAP adapter needs that difference.
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.set_breakpoint(PC_ADD), true)
assert_equal(target.set_breakpoint(PC_ADD), false)
assert_equal(target.breakpoints().len(), 1)
```

</details>

#### keeps the breakpoint list ascending regardless of insertion order

- keeps the breakpoint list ascending regardless of insertion order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the breakpoint list ascending regardless of insertion order")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_HALT)
target.set_breakpoint(PC_ADD)
target.set_breakpoint(PC_SYS_RESULT)
val bps = target.breakpoints()
assert_equal(bps.len(), 3)
assert_equal(bps[0], PC_ADD)
assert_equal(bps[1], PC_SYS_RESULT)
assert_equal(bps[2], PC_HALT)
```

</details>

#### returns true when clearing an existing breakpoint and false otherwise

- returns true when clearing an existing breakpoint and false otherwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when clearing an existing breakpoint and false otherwise")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_ADD)
assert_equal(target.clear_breakpoint(PC_ADD), true)
assert_equal(target.clear_breakpoint(PC_ADD), false)
assert_equal(target.breakpoints().len(), 0)
```

</details>

#### reports no breakpoints on a fresh target

- reports no breakpoints on a fresh target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no breakpoints on a fresh target")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.breakpoints().len(), 0)
```

</details>

#### clears only the named location, leaving siblings intact

- clears only the named location, leaving siblings intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears only the named location, leaving siblings intact")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_ADD)
target.set_breakpoint(PC_SYS_RESULT)
target.set_breakpoint(PC_HALT)
assert_equal(target.clear_breakpoint(PC_SYS_RESULT), true)
val bps = target.breakpoints()
assert_equal(bps.len(), 2)
assert_equal(bps[0], PC_ADD)
assert_equal(bps[1], PC_HALT)
```

</details>

### DebugTarget (ref) — step() advances exactly one instruction

#### starts stopped at the entry pc with an empty stack

- starts stopped at the entry pc with an empty stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts stopped at the entry pc with an empty stack")
val target = _attached_target(ADD_PROGRAM)
val s = target.state()
assert_equal(s.pc, 0)
assert_equal(s.sp, 0)
assert_equal(s.stack.len(), 0)
assert_equal(s.call_stack.len(), 0)
assert_equal(s.pc_kind, PC_KIND_SVMG)
```

</details>

#### advances one PUSHI per step, growing the stack by one each time

- advances one PUSHI per step, growing the stack by one each time


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances one PUSHI per step, growing the stack by one each time")
val target = _attached_target(ADD_PROGRAM)
val s1 = target.step()
assert_equal(s1.pc, 5)
assert_equal(s1.sp, 1)
assert_equal(s1.stack.len(), 1)
assert_equal(s1.stack[0], 1)
assert_equal(s1.stop_reason, STOP_STEP)

val s2 = target.step()
assert_equal(s2.pc, 10)
assert_equal(s2.sp, 2)
assert_equal(s2.stack[1], 3)

val s3 = target.step()
assert_equal(s3.pc, PC_ADD)
assert_equal(s3.sp, 3)
assert_equal(s3.stack[2], 4)
```

</details>

#### collapses two operands into their sum on the ADD step

- collapses two operands into their sum on the ADD step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapses two operands into their sum on the ADD step")
val target = _attached_target(ADD_PROGRAM)
target.step()
target.step()
target.step()
val s = target.step()
assert_equal(s.pc, PC_SYS_RESULT)
assert_equal(s.sp, 2)
assert_equal(s.stack[1], 7)
```

</details>

#### reports halt after stepping through the whole program

- reports halt after stepping through the whole program


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports halt after stepping through the whole program")
val target = _attached_target(ADD_PROGRAM)
var i = 0
while i < ADD_PROGRAM_STEPS:
    target.step()
    i = i + 1
val s = target.state()
assert_equal(s.stop_reason, STOP_HALT)
assert_equal(debug_state_is_terminal(s), true)
assert_equal(debug_state_is_stopped_alive(s), false)
```

</details>

#### stays terminal when stepped past the end (no panic, no progress)

- stays terminal when stepped past the end (no panic, no progress)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stays terminal when stepped past the end (no panic, no progress)")
val target = _attached_target(ADD_PROGRAM)
var i = 0
while i < ADD_PROGRAM_STEPS:
    target.step()
    i = i + 1
val pc_at_halt = target.state().pc
val extra1 = target.step()
val extra2 = target.step()
assert_equal(extra1.stop_reason, STOP_HALT)
assert_equal(extra2.stop_reason, STOP_HALT)
assert_equal(extra2.pc, pc_at_halt)
```

</details>

#### steps THROUGH a breakpoint on the current location (never wedges)

- steps THROUGH a breakpoint on the current location (never wedges)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("steps THROUGH a breakpoint on the current location (never wedges)")
# If `step` consulted the breakpoint on the location it is standing
# on, a breakpointed instruction could never be stepped over.
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(0)
val s = target.step()
assert_equal(s.pc, 5)
assert_equal(s.sp, 1)
```

</details>

#### reports 'breakpoint' when a single step LANDS on a breakpoint

- reports 'breakpoint' when a single step LANDS on a breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports 'breakpoint' when a single step LANDS on a breakpoint")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(5)
val s = target.step()
assert_equal(s.pc, 5)
assert_equal(s.stop_reason, STOP_BREAKPOINT)
assert_equal(debug_state_is_stopped_alive(s), true)
```

</details>

### DebugTarget (ref) — resume() and breakpoint stops

#### runs to completion when no breakpoint is set

- runs to completion when no breakpoint is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs to completion when no breakpoint is set")
val target = _attached_target(ADD_PROGRAM)
val s = target.resume()
assert_equal(s.stop_reason, STOP_HALT)
assert_equal(debug_state_is_terminal(s), true)
```

</details>

#### stops exactly AT the breakpoint pc, before executing it

- stops exactly AT the breakpoint pc, before executing it


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops exactly AT the breakpoint pc, before executing it")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_ADD)
val s = target.resume()
assert_equal(s.stop_reason, STOP_BREAKPOINT)
assert_equal(s.pc, PC_ADD)
# The three PUSHIs ran; ADD itself has NOT -- proven by the stack
# still holding all three operands rather than their sum.
assert_equal(s.sp, 3)
assert_equal(s.stack.len(), 3)
assert_equal(s.stack[0], 1)
assert_equal(s.stack[1], 3)
assert_equal(s.stack[2], 4)
```

</details>

#### makes progress when resumed FROM the breakpoint it is standing on

- makes progress when resumed FROM the breakpoint it is standing on


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes progress when resumed FROM the breakpoint it is standing on")
# The classic debugger bug: re-reporting the same location forever.
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_ADD)
val first = target.resume()
assert_equal(first.pc, PC_ADD)
val second = target.resume()
assert_true(second.pc != PC_ADD)
assert_equal(second.stop_reason, STOP_HALT)
```

</details>

#### honours multiple breakpoints in execution order

- honours multiple breakpoints in execution order


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honours multiple breakpoints in execution order")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_ADD)
target.set_breakpoint(PC_HALT)
val first = target.resume()
assert_equal(first.pc, PC_ADD)
val second = target.resume()
assert_equal(second.pc, PC_HALT)
assert_equal(second.stop_reason, STOP_BREAKPOINT)
# ADD and SYS_RESULT ran between the two stops.
assert_equal(second.sp, 0)
val third = target.resume()
assert_equal(third.stop_reason, STOP_HALT)
```

</details>

#### does not stop at a breakpoint that was cleared before resuming

- does not stop at a breakpoint that was cleared before resuming


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not stop at a breakpoint that was cleared before resuming")
val target = _attached_target(ADD_PROGRAM)
target.set_breakpoint(PC_ADD)
target.clear_breakpoint(PC_ADD)
val s = target.resume()
assert_equal(s.stop_reason, STOP_HALT)
```

</details>

#### ignores a breakpoint on a location that is never reached

- ignores a breakpoint on a location that is never reached


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores a breakpoint on a location that is never reached")
val target = _attached_target(ADD_PROGRAM)
# 4 is inside the PUSHI operand bytes -- never a real pc.
target.set_breakpoint(4)
val s = target.resume()
assert_equal(s.stop_reason, STOP_HALT)
```

</details>

### DebugTarget (ref) — terminal stop reasons are distinguished

#### reports 'trap' (not 'halt') when the program traps

- reports 'trap' (not 'halt') when the program traps


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports 'trap' (not 'halt') when the program traps")
val target = _attached_target(TRAP_PROGRAM)
val s = target.resume()
assert_equal(s.stop_reason, STOP_TRAP)
assert_equal(debug_state_is_terminal(s), true)
```

</details>

#### reports 'timeout' (not 'halt') when the step budget is exhausted

- reports 'timeout' (not 'halt') when the step budget is exhausted


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports 'timeout' (not 'halt') when the step budget is exhausted")
val session = _attached_session(SPIN_PROGRAM, attach_opts_with_budget(20))
val target = session.debug()!
val s = target.resume()
assert_equal(s.stop_reason, STOP_TIMEOUT)
assert_equal(debug_state_is_terminal(s), true)
```

</details>

#### keeps reporting the SAME terminal reason on repeated state() reads

- keeps reporting the SAME terminal reason on repeated state() reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps reporting the SAME terminal reason on repeated state() reads")
val target = _attached_target(TRAP_PROGRAM)
target.resume()
assert_equal(target.state().stop_reason, STOP_TRAP)
assert_equal(target.state().stop_reason, STOP_TRAP)
```

</details>

### DebugTarget (ref) — state() is a pure read

#### does not advance execution when called repeatedly

- does not advance execution when called repeatedly


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not advance execution when called repeatedly")
val target = _attached_target(ADD_PROGRAM)
target.step()
val a = target.state()
val b = target.state()
val c = target.state()
assert_equal(a.pc, b.pc)
assert_equal(b.pc, c.pc)
assert_equal(a.sp, c.sp)
assert_equal(a.stop_reason, c.stop_reason)
assert_equal(c.pc, 5)
```

</details>

#### reports the live stack only, never the fixed backing slots

- reports the live stack only, never the fixed backing slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the live stack only, never the fixed backing slots")
# The VM's operand stack is a fixed 256-slot array; reporting it
# whole would present stale slots above `sp` as live values.
val target = _attached_target(ADD_PROGRAM)
target.step()
target.step()
val s = target.state()
assert_equal(s.sp, 2)
assert_equal(s.stack.len(), 2)
```

</details>

#### always names its pc unit as svmg_pc on this lane

- always names its pc unit as svmg_pc on this lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("always names its pc unit as svmg_pc on this lane")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.state().pc_kind, PC_KIND_SVMG)
assert_equal(target.step().pc_kind, PC_KIND_SVMG)
assert_equal(target.resume().pc_kind, PC_KIND_SVMG)
```

</details>

### DebugTarget (ref) — read_mem bounds contract

#### reads exactly the requested length from a valid range

- reads exactly the requested length from a valid range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads exactly the requested length from a valid range")
val target = _attached_target(ADD_PROGRAM)
val bytes = target.read_mem(0, 8)
assert_equal(bytes.len(), 8)
```

</details>

#### returns EMPTY for a zero or negative length

- returns EMPTY for a zero or negative length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns EMPTY for a zero or negative length")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.read_mem(0, 0).len(), 0)
assert_equal(target.read_mem(0, -1).len(), 0)
```

</details>

#### returns EMPTY for a negative offset

- returns EMPTY for a negative offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns EMPTY for a negative offset")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.read_mem(-1, 4).len(), 0)
```

</details>

#### returns EMPTY rather than a SHORT buffer when the range overruns

- returns EMPTY rather than a SHORT buffer when the range overruns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns EMPTY rather than a SHORT buffer when the range overruns")
# A short-but-nonempty read would be indistinguishable from a
# successful read of a smaller region.
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.read_mem(0, 1 << 30).len(), 0)
```

</details>

#### reads back the uploaded program bytes (the DATA region is real)

- reads back the uploaded program bytes (the DATA region is real)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads back the uploaded program bytes (the DATA region is real)")
val target = _attached_target(ADD_PROGRAM)
# SGP_HEADER_SIZE is 36; the code section starts immediately after
# it, and the first opcode byte is PUSHI.
val bytes = target.read_mem(36, 1)
assert_equal(bytes.len(), 1)
```

</details>

### DebugTarget (ref) — detach

#### detaches cleanly and is safe to call twice

- detaches cleanly and is safe to call twice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detaches cleanly and is safe to call twice")
val target = _attached_target(ADD_PROGRAM)
assert_equal(target.detach(), "")
assert_equal(target.detach(), "")
```

</details>

#### refuses to add breakpoints after detach

- refuses to add breakpoints after detach


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to add breakpoints after detach")
val target = _attached_target(ADD_PROGRAM)
target.detach()
assert_equal(target.set_breakpoint(PC_ADD), false)
```

</details>

#### does not execute after detach

- does not execute after detach


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not execute after detach")
val target = _attached_target(ADD_PROGRAM)
target.detach()
val before = target.state().pc
target.step()
target.resume()
assert_equal(target.state().pc, before)
```

</details>

### ProfileTarget (ref) — tiered honesty and exact step counts

#### reports the Emulated tier when profiling was armed at attach

- reports the Emulated tier when profiling was armed at attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the Emulated tier when profiling was armed at attach")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
val prof = session.profile()!
assert_equal(cap_level_name(prof.profile_level()), "emulated")
```

</details>

#### reports Unavailable when profiling was disabled at attach

- reports Unavailable when profiling was disabled at attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Unavailable when profiling was disabled at attach")
val opts = AttachOpts(step_budget: 1000, entry_pc: 0, log_cap: 256, profile: false)
val session = _attached_session(ADD_PROGRAM, opts)
val prof = session.profile()!
assert_equal(cap_level_name(prof.profile_level()), "unavailable")
```

</details>

#### counts steps EXACTLY over a begin/end window

- counts steps EXACTLY over a begin/end window


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts steps EXACTLY over a begin/end window")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_equal(report.steps, ADD_PROGRAM_STEPS)
assert_equal(profile_has_steps(report), true)
```

</details>

#### counts only the instructions inside the window

- counts only the instructions inside the window


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts only the instructions inside the window")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
dp.step()
dp.step()
dp.profile_begin()
dp.step()
val report = dp.profile_end()
assert_equal(report.steps, 1)
```

</details>

#### reports device_ns as ABSENT (-1), never as zero, on a deviceless lane

- reports device_ns as ABSENT (-1), never as zero, on a deviceless lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports device_ns as ABSENT (-1), never as zero, on a deviceless lane")
# A zero would chart as "instantaneous"; -1 cannot be mistaken for
# a measurement.
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_equal(report.device_ns, PROFILE_ABSENT)
assert_equal(profile_has_device_time(report), false)
```

</details>

#### measures a real, non-negative wall time

- measures a real, non-negative wall time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures a real, non-negative wall time")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_true(report.wall_ns >= 0)
```

</details>

#### records in `detail` which quantities were actually measured

- records in `detail` which quantities were actually measured


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records in `detail` which quantities were actually measured")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
val prof = session.profile()!
prof.profile_begin()
val report = prof.profile_end()
assert_true(report.detail.contains("target=ref"))
assert_true(report.detail.contains("steps=exact"))
assert_true(report.detail.contains("device=none"))
```

</details>

#### returns an Unavailable report for end-without-begin, not a fake zero

- returns an Unavailable report for end-without-begin, not a fake zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an Unavailable report for end-without-begin, not a fake zero")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
val prof = session.profile()!
val report = prof.profile_end()
assert_equal(cap_level_name(report.level), "unavailable")
assert_equal(report.steps, PROFILE_ABSENT)
assert_equal(report.wall_ns, PROFILE_ABSENT)
assert_true(report.detail.contains("without"))
```

</details>

#### restarts the window on a second begin (last-begin-wins)

- restarts the window on a second begin (last-begin-wins)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restarts the window on a second begin (last-begin-wins)")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
dp.profile_begin()
dp.step()
dp.step()
dp.profile_begin()
dp.step()
val report = dp.profile_end()
assert_equal(report.steps, 1)
```

</details>

#### consumes the arming, so a second end reports absence

- consumes the arming, so a second end reports absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consumes the arming, so a second end reports absence")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
val prof = session.profile()!
prof.profile_begin()
val first = prof.profile_end()
assert_equal(cap_level_name(first.level), "emulated")
val second = prof.profile_end()
assert_equal(cap_level_name(second.level), "unavailable")
```

</details>

#### reports absence for every quantity when profiling is disabled

- reports absence for every quantity when profiling is disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports absence for every quantity when profiling is disabled")
val opts = AttachOpts(step_budget: 1000, entry_pc: 0, log_cap: 256, profile: false)
val dp = _attached_group(ADD_PROGRAM, opts)
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_equal(report.steps, PROFILE_ABSENT)
assert_equal(report.wall_ns, PROFILE_ABSENT)
assert_equal(report.device_ns, PROFILE_ABSENT)
```

</details>

#### counts a trapped run's steps up to and including the trap

- counts a trapped run's steps up to and including the trap


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts a trapped run's steps up to and including the trap")
# PUSHI, PUSHI, SYS_RESULT, TRAP = 4 instructions.
val dp = _attached_group(TRAP_PROGRAM, attach_opts_default())
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_equal(report.steps, 4)
```

</details>

#### counts a timed-out run's steps up to the budget

- counts a timed-out run's steps up to the budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts a timed-out run's steps up to the budget")
val dp = _attached_group(SPIN_PROGRAM, attach_opts_with_budget(12))
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_equal(report.steps, 12)
```

</details>

#### builds a canonical all-absent report from the helper

- builds a canonical all-absent report from the helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a canonical all-absent report from the helper")
val report = profile_report_unavailable("reason=no-device")
assert_equal(cap_level_name(report.level), "unavailable")
assert_equal(report.wall_ns, PROFILE_ABSENT)
assert_equal(report.device_ns, PROFILE_ABSENT)
assert_equal(report.steps, PROFILE_ABSENT)
assert_equal(profile_has_steps(report), false)
assert_equal(profile_has_device_time(report), false)
```

</details>

### DebugProfiler group — all-or-nothing acquisition

#### acquires the group when BOTH capabilities are present

- acquires the group when BOTH capabilities are present


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("acquires the group when BOTH capabilities are present")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
val maybe = ref_debug_profiler(session)
assert_true(maybe != nil)
assert_equal(maybe!.kind(), REF_KIND)
```

</details>

#### refuses to acquire before attach (neither accessor answers)

- refuses to acquire before attach (neither accessor answers)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to acquire before attach (neither accessor answers)")
val session = RefDebugSession.new()
assert_true(ref_debug_profiler(session) == nil)
```

</details>

#### refuses to acquire after shutdown

- refuses to acquire after shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to acquire after shutdown")
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
session.shutdown()
assert_true(ref_debug_profiler(session) == nil)
```

</details>

#### exposes the whole DebugTarget half of the union

- exposes the whole DebugTarget half of the union


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the whole DebugTarget half of the union")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
assert_equal(dp.debug_level() == CapLevel.Native, true)
assert_equal(dp.set_breakpoint(PC_ADD), true)
assert_equal(dp.breakpoints().len(), 1)
val stopped = dp.resume()
assert_equal(stopped.pc, PC_ADD)
assert_equal(stopped.stop_reason, STOP_BREAKPOINT)
assert_equal(dp.state().pc, PC_ADD)
val stepped = dp.step()
assert_equal(stepped.pc, PC_SYS_RESULT)
assert_equal(dp.clear_breakpoint(PC_ADD), true)
assert_equal(dp.read_mem(0, 4).len(), 4)
assert_equal(dp.detach(), "")
```

</details>

#### exposes the whole ProfileTarget half of the union

- exposes the whole ProfileTarget half of the union


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the whole ProfileTarget half of the union")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
assert_equal(cap_level_name(dp.profile_level()), "emulated")
dp.profile_begin()
dp.resume()
val report = dp.profile_end()
assert_equal(report.steps, ADD_PROGRAM_STEPS)
```

</details>

#### reports the same values through the group as through a member trait

- reports the same values through the group as through a member trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the same values through the group as through a member trait")
# The group adds nothing and renames nothing -- this is what makes
# the sugar swap a pure refactor.
val session = _attached_session(ADD_PROGRAM, attach_opts_default())
val member = session.debug()!
val group = ref_debug_profiler(session)!
assert_equal(group.kind(), member.kind())
assert_equal(group.state().pc, member.state().pc)
assert_equal(group.state().pc_kind, member.state().pc_kind)
```

</details>

#### runs the design's worked example with no runtime capability checks

- runs the design's worked example with no runtime capability checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the design's worked example with no runtime capability checks")
val dp = _attached_group(ADD_PROGRAM, attach_opts_default())
val report = dp_trace_run(dp)
assert_equal(report.steps, ADD_PROGRAM_STEPS)
assert_equal(cap_level_name(report.level), "emulated")
assert_equal(report.device_ns, PROFILE_ABSENT)
```

</details>

### Cross-backend vector table — the shape later lanes diff against

#### produces the reference (pc, sp, stop_reason) trace for the ADD program

- produces the reference (pc, sp, stop_reason) trace for the ADD program


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces the reference (pc, sp, stop_reason) trace for the ADD program")
# This table is the literal anchor: a CUDA/Vulkan/Metal lane
# running the SAME program must produce the same pc/sp/reason
# sequence (with pc_kind still "svmg_pc").
val target = _attached_target(ADD_PROGRAM)
val expected_pc = [5, 10, 15, 16, 17, 17]
val expected_sp = [1, 2, 3, 2, 0, 0]
var i = 0
while i < expected_pc.len():
    val s = target.step()
    assert_equal(s.pc, expected_pc[i])
    assert_equal(s.sp, expected_sp[i])
    assert_equal(s.pc_kind, PC_KIND_SVMG)
    i = i + 1
assert_equal(target.state().stop_reason, STOP_HALT)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/debug_target_ref_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CapLevel — the honesty tier, DebugSessionCore (ref) — attach / accessors / shutdown lifecycle, AttachOpts — the shared attach knobs, DebugTarget (ref) — identity and capability tier, DebugTarget (ref) — breakpoint set/clear/list contract, DebugTarget (ref) — step() advances exactly one instruction, DebugTarget (ref) — resume() and breakpoint stops, DebugTarget (ref) — terminal stop reasons are distinguished, DebugTarget (ref) — state() is a pure read, DebugTarget (ref) — read_mem bounds contract, DebugTarget (ref) — detach, ProfileTarget (ref) — tiered honesty and exact step counts, DebugProfiler group — all-or-nothing acquisition, Cross-backend vector table — the shape later lanes diff against.
- CapLevel — the honesty tier
- DebugSessionCore (ref) — attach / accessors / shutdown lifecycle
- AttachOpts — the shared attach knobs
- DebugTarget (ref) — identity and capability tier
- DebugTarget (ref) — breakpoint set/clear/list contract
- DebugTarget (ref) — step() advances exactly one instruction
- DebugTarget (ref) — resume() and breakpoint stops
- DebugTarget (ref) — terminal stop reasons are distinguished
- DebugTarget (ref) — state() is a pure read
- DebugTarget (ref) — read_mem bounds contract
- DebugTarget (ref) — detach
- ProfileTarget (ref) — tiered honesty and exact step counts
- DebugProfiler group — all-or-nothing acquisition
- Cross-backend vector table — the shape later lanes diff against

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
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

- Canonical SPipe generation for source `1bbd20524525bf0caf04f49870ca24c7ffb1db10310111da82464e8b6fcee88f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1bbd20524525bf0caf04f49870ca24c7ffb1db10310111da82464e8b6fcee88f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1bbd20524525bf0caf04f49870ca24c7ffb1db10310111da82464e8b6fcee88f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/debug/debug_target_ref_spec.spl
mirror: doc/06_spec/01_unit/lib/debug/debug_target_ref_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug/debug_target_ref_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug/debug_target_ref_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug/debug_target_ref_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every tier through its stable wire name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/debug_target_ref_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes an unknown tier name to Unavailable, never to a working tier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/debug_target_ref_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats Native and Emulated as usable and Unavailable as not' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
