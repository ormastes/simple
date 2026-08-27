# registry_scoping_spec

> Purpose: Prove that bare-name registry collision (current policy).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# registry_scoping_spec

Purpose: Prove that bare-name registry collision (current policy).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that bare-name registry collision (current policy).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### bare-name registry collision (current policy)

#### two modules registering the same function name collide onto ONE global entry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- two modules registering the same function name collide onto ONE global entry
- Verify: two modules registering the same function name collide onto ONE global entry
   - Expected: rs_ft_lookup("helper") equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("two modules registering the same function name collide onto ONE global entry")
step("Verify: two modules registering the same function name collide onto ONE global entry")
# @req: REQ-COMPILER-CORE-INTERPRETER-001
rs_tracker_reset()
rs_begin_module("mod_a")
rs_begin_module("mod_b")
rs_ft_register("helper", 100)
rs_track_func_owned("mod_a", "helper", 100)
rs_ft_register("helper", 200)
rs_track_func_owned("mod_b", "helper", 200)
# Documents the ACTUAL policy: last write wins, no per-module
# isolation. This is the same failure class as the seed's flat
# registry — pinned here as regression armor, not fixed by adding
# module-qualified keys (that would be a wholesale redesign, out of
# scope for this lane).
expect(rs_ft_lookup("helper")).to_equal(200)
```

</details>

#### distinct names across modules never collide

- distinct names across modules never collide
- Verify: distinct names across modules never collide
   - Expected: rs_ft_lookup("c_only_fn") equals `10`
   - Expected: rs_ft_lookup("d_only_fn") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("distinct names across modules never collide")
step("Verify: distinct names across modules never collide")
rs_tracker_reset()
rs_begin_module("mod_c")
rs_begin_module("mod_d")
rs_ft_register("c_only_fn", 10)
rs_track_func_owned("mod_c", "c_only_fn", 10)
rs_ft_register("d_only_fn", 20)
rs_track_func_owned("mod_d", "d_only_fn", 20)
expect(rs_ft_lookup("c_only_fn")).to_equal(10)
expect(rs_ft_lookup("d_only_fn")).to_equal(20)
```

</details>

### owner-guarded module unload (pure_interp_registry_2026-07-17 fix)

#### unloading the OVERWRITTEN module does not delete the survivor's live entry

- unloading the OVERWRITTEN module does not delete the survivor's live entry
- Verify: unloading the OVERWRITTEN module does not delete the survivor's live entry
   - Expected: rs_ft_lookup("helper") equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("unloading the OVERWRITTEN module does not delete the survivor's live entry")
step("Verify: unloading the OVERWRITTEN module does not delete the survivor's live entry")
rs_tracker_reset()
rs_begin_module("mod_a")
rs_begin_module("mod_b")
rs_ft_register("helper", 100)
rs_track_func_owned("mod_a", "helper", 100)
rs_ft_register("helper", 200)          # mod_b collides, now owns "helper"
rs_track_func_owned("mod_b", "helper", 200)
rs_unload_module_guarded("mod_a")
# mod_b's live registration must survive mod_a's unload.
expect(rs_ft_lookup("helper")).to_equal(200)
```

</details>

#### unloading the CURRENT owner still removes its own entry

- unloading the CURRENT owner still removes its own entry
- Verify: unloading the CURRENT owner still removes its own entry
   - Expected: removed equals `1`
   - Expected: rs_ft_lookup("solo_fn") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("unloading the CURRENT owner still removes its own entry")
step("Verify: unloading the CURRENT owner still removes its own entry")
rs_tracker_reset()
rs_begin_module("mod_e")
rs_ft_register("solo_fn", 300)
rs_track_func_owned("mod_e", "solo_fn", 300)
val removed = rs_unload_module_guarded("mod_e")
expect(removed).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(rs_ft_lookup("solo_fn")).to_equal(-1)
```

</details>

#### demonstrates the PRE-FIX corruption the guard prevents (regression proof)

- demonstrates the PRE-FIX corruption the guard prevents (regression proof)
- Verify: demonstrates the PRE-FIX corruption the guard prevents (regression proof)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("demonstrates the PRE-FIX corruption the guard prevents (regression proof)")
step("Verify: demonstrates the PRE-FIX corruption the guard prevents (regression proof)")
rs_tracker_reset()
rs_begin_module("mod_a")
rs_begin_module("mod_b")
rs_ft_register("helper", 100)
rs_track_func_owned("mod_a", "helper", 100)
rs_ft_register("helper", 200)
rs_track_func_owned("mod_b", "helper", 200)
rs_unload_module_unguarded("mod_a")
# Without the owner guard, unloading mod_a wrongly deletes mod_b's
# live "helper" registration — a cross-module corruption from an
# unrelated module's unload.
assert_equal(rs_ft_lookup("helper"), -1)
```

</details>

### partial registration does not shift or corrupt prior slots

#### a later module's partial registration leaves an earlier module's entries intact

- a later module's partial registration leaves an earlier module's entries intact
- Verify: a later module's partial registration leaves an earlier module's entries intact
   - Expected: rs_ft_lookup("x_fn_1") equals `10`
   - Expected: rs_ft_lookup("x_fn_2") equals `20`
   - Expected: rs_ft_lookup("y_fn_registered") equals `30`
   - Expected: rs_ft_lookup("y_fn_never_reached") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("a later module's partial registration leaves an earlier module's entries intact")
step("Verify: a later module's partial registration leaves an earlier module's entries intact")
rs_tracker_reset()
rs_begin_module("mod_x")
rs_ft_register("x_fn_1", 10)
rs_track_func_owned("mod_x", "x_fn_1", 10)
rs_ft_register("x_fn_2", 20)
rs_track_func_owned("mod_x", "x_fn_2", 20)

# mod_y registers only ONE of two intended functions (simulating a
# module whose registration pass aborts partway, e.g. an unresolved
# identifier later in the same file never reaches a second fn decl).
rs_begin_module("mod_y")
rs_ft_register("y_fn_registered", 30)
rs_track_func_owned("mod_y", "y_fn_registered", 30)
# y_fn_never_reached deliberately NOT registered.

# mod_x's earlier entries are untouched — no index shifting because
# the arena is append-based, not compacted.
expect(rs_ft_lookup("x_fn_1")).to_equal(10)
expect(rs_ft_lookup("x_fn_2")).to_equal(20)
expect(rs_ft_lookup("y_fn_registered")).to_equal(30)
expect(rs_ft_lookup("y_fn_never_reached")).to_equal(-1)
```

</details>

#### unloading the partially-registered module removes only what it actually registered

- unloading the partially-registered module removes only what it actually registered
- Verify: unloading the partially-registered module removes only what it actually registered
   - Expected: rs_ft_lookup("y_fn_registered") equals `-1`
   - Expected: rs_ft_lookup("x_fn_1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("unloading the partially-registered module removes only what it actually registered")
step("Verify: unloading the partially-registered module removes only what it actually registered")
rs_tracker_reset()
rs_begin_module("mod_x")
rs_ft_register("x_fn_1", 10)
rs_track_func_owned("mod_x", "x_fn_1", 10)

rs_begin_module("mod_y")
rs_ft_register("y_fn_registered", 30)
rs_track_func_owned("mod_y", "y_fn_registered", 30)

rs_unload_module_guarded("mod_y")
expect(rs_ft_lookup("y_fn_registered")).to_equal(-1)
# mod_x untouched by mod_y's unload.
expect(rs_ft_lookup("x_fn_1")).to_equal(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
- `REQ-COMPILER-CORE-INTERPRETER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `046dabe6945bbc64e3d9f6a6ddacfb334db448457b2b927f7f038c13820efc82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `046dabe6945bbc64e3d9f6a6ddacfb334db448457b2b927f7f038c13820efc82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `046dabe6945bbc64e3d9f6a6ddacfb334db448457b2b927f7f038c13820efc82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/interpreter/registry_scoping_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/interpreter/registry_scoping_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/interpreter/registry_scoping_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl:201:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two modules registering the same function name collide onto ONE global entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinct names across modules never collide' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unloading the OVERWRITTEN module does not delete the survivor's live entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
