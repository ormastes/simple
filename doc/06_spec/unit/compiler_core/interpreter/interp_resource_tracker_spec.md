# interp_resource_tracker_spec

> Purpose: Prove that func_table_remove.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# interp_resource_tracker_spec

Purpose: Prove that func_table_remove.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that func_table_remove.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### func_table_remove

#### removes a registered function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- removes a registered function
- Verify: removes a registered function
   - Expected: before equals `100`
   - Expected: removed is true
   - Expected: after equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a registered function")
step("Verify: removes a registered function")
# @req: REQ-COMPILER-CORE-INTERPRETER-001
ft_reset()
ft_register("test_remove_fn", 100)
val before = ft_lookup("test_remove_fn")
expect(before).to_equal(100)  # oracle: 100 — named expected value from the requirement
val removed = ft_remove("test_remove_fn")
expect(removed).to_equal(true)
val after = ft_lookup("test_remove_fn")
expect(after).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### returns false for unknown function

- returns false for unknown function
- Verify: returns false for unknown function
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown function")
step("Verify: returns false for unknown function")
ft_reset()
val removed = ft_remove("nonexistent_fn_xyz")
expect(removed).to_equal(false)
```

</details>

#### remove does not break other entries

- remove does not break other entries
- Verify: remove does not break other entries
   - Expected: ft_lookup("tr_keep_a") equals `200`
   - Expected: ft_lookup("tr_keep_c") equals `202`
   - Expected: ft_lookup("tr_remove_b") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove does not break other entries")
step("Verify: remove does not break other entries")
ft_reset()
ft_register("tr_keep_a", 200)
ft_register("tr_remove_b", 201)
ft_register("tr_keep_c", 202)
ft_remove("tr_remove_b")
expect(ft_lookup("tr_keep_a")).to_equal(200)
expect(ft_lookup("tr_keep_c")).to_equal(202)
expect(ft_lookup("tr_remove_b")).to_equal(-1)
```

</details>

### struct_table_remove

#### removes a registered struct

- removes a registered struct
- Verify: removes a registered struct
   - Expected: before equals `300`
   - Expected: removed is true
   - Expected: after equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a registered struct")
step("Verify: removes a registered struct")
st_reset()
st_register("TestRemoveStruct", 300)
val before = st_lookup("TestRemoveStruct")
expect(before).to_equal(300)  # oracle: 300 — named expected value from the requirement
val removed = st_remove("TestRemoveStruct")
expect(removed).to_equal(true)
val after = st_lookup("TestRemoveStruct")
expect(after).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### returns false for unknown struct

- returns false for unknown struct
- Verify: returns false for unknown struct
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown struct")
step("Verify: returns false for unknown struct")
st_reset()
val removed = st_remove("UnknownStructXYZ")
expect(removed).to_equal(false)
```

</details>

### env_remove_global

#### removes a global variable

- removes a global variable
- Verify: removes a global variable
   - Expected: before equals `500`
   - Expected: removed is true
   - Expected: after equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a global variable")
step("Verify: removes a global variable")
ge_reset()
ge_define("test_remove_global", 500)
val before = ge_lookup("test_remove_global")
expect(before).to_equal(500)  # oracle: 500 — named expected value from the requirement
val removed = ge_remove("test_remove_global")
expect(removed).to_equal(true)
val after = ge_lookup("test_remove_global")
expect(after).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### returns false for unknown global

- returns false for unknown global
- Verify: returns false for unknown global
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown global")
step("Verify: returns false for unknown global")
ge_reset()
val removed = ge_remove("nonexistent_global_xyz")
expect(removed).to_equal(false)
```

</details>

### InterpreterResourceTracker

### module tracking

#### begins tracking a module

- begins tracking a module
- Verify: begins tracking a module
   - Expected: mock_irt_is_tracked("test_module_a") is true
   - Expected: mock_irt_tracked_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("begins tracking a module")
step("Verify: begins tracking a module")
mock_irt_init()
mock_irt_begin_module("test_module_a")
expect(mock_irt_is_tracked("test_module_a")).to_equal(true)
expect(mock_irt_tracked_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### does not double-track

- does not double-track
- Verify: does not double-track
   - Expected: mock_irt_tracked_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not double-track")
step("Verify: does not double-track")
mock_irt_init()
mock_irt_begin_module("test_module_dup")
mock_irt_begin_module("test_module_dup")
expect(mock_irt_tracked_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### tracks multiple modules

- tracks multiple modules
- Verify: tracks multiple modules
   - Expected: mock_irt_tracked_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks multiple modules")
step("Verify: tracks multiple modules")
mock_irt_init()
mock_irt_begin_module("mod_x")
mock_irt_begin_module("mod_y")
expect(mock_irt_tracked_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### name registration

#### tracks function names

- tracks function names
- Verify: tracks function names
   - Expected: mock_irt_get_func_count("fn_mod") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks function names")
step("Verify: tracks function names")
mock_irt_init()
mock_irt_begin_module("fn_mod")
mock_irt_track_func("fn_mod", "func_a")
mock_irt_track_func("fn_mod", "func_b")
expect(mock_irt_get_func_count("fn_mod")).to_equal(2)
```

</details>

#### tracks struct names

- tracks struct names
- Verify: tracks struct names
   - Expected: mock_irt_get_struct_count("st_mod") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks struct names")
step("Verify: tracks struct names")
mock_irt_init()
mock_irt_begin_module("st_mod")
mock_irt_track_struct("st_mod", "Point")
expect(mock_irt_get_struct_count("st_mod")).to_equal(1)
```

</details>

#### ignores tracking for unregistered module

- ignores tracking for unregistered module
- Verify: ignores tracking for unregistered module
   - Expected: mock_irt_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores tracking for unregistered module")
step("Verify: ignores tracking for unregistered module")
mock_irt_init()
mock_irt_track_func("unknown_mod", "func_a")
expect(mock_irt_tracked_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### module unload

#### removes tracked functions from table

- removes tracked functions from table
- Verify: removes tracked functions from table
   - Expected: ft_lookup("irt_test_fn_1") equals `-1`
   - Expected: ft_lookup("irt_test_fn_2") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes tracked functions from table")
step("Verify: removes tracked functions from table")
mock_irt_init()
mock_irt_begin_module("unload_test_mod")
ft_register("irt_test_fn_1", 900)
ft_register("irt_test_fn_2", 901)
mock_irt_track_func("unload_test_mod", "irt_test_fn_1")
mock_irt_track_func("unload_test_mod", "irt_test_fn_2")
val removed = mock_irt_unload_module("unload_test_mod")
expect(removed).to_be_greater_than(0)
expect(ft_lookup("irt_test_fn_1")).to_equal(-1)
expect(ft_lookup("irt_test_fn_2")).to_equal(-1)
```

</details>

#### removes tracked globals from env

- removes tracked globals from env
- Verify: removes tracked globals from env
   - Expected: ge_lookup("irt_test_global") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes tracked globals from env")
step("Verify: removes tracked globals from env")
mock_irt_init()
mock_irt_begin_module("global_unload_mod")
ge_define("irt_test_global", 800)
mock_irt_track_global("global_unload_mod", "irt_test_global")
mock_irt_unload_module("global_unload_mod")
expect(ge_lookup("irt_test_global")).to_equal(-1)
```

</details>

#### tombstones tracker slot after unload

- tombstones tracker slot after unload
- Verify: tombstones tracker slot after unload
   - Expected: mock_irt_is_tracked("tombstone_mod") is false
   - Expected: mock_irt_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tombstones tracker slot after unload")
step("Verify: tombstones tracker slot after unload")
mock_irt_init()
mock_irt_begin_module("tombstone_mod")
mock_irt_track_func("tombstone_mod", "fn_x")
mock_irt_unload_module("tombstone_mod")
expect(mock_irt_is_tracked("tombstone_mod")).to_equal(false)
expect(mock_irt_tracked_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns 0 for untracked module

- returns 0 for untracked module
- Verify: returns 0 for untracked module
   - Expected: removed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for untracked module")
step("Verify: returns 0 for untracked module")
mock_irt_init()
val removed = mock_irt_unload_module("never_tracked")
expect(removed).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### init resets state

#### clears all tracking on init

- clears all tracking on init
- Verify: clears all tracking on init
   - Expected: mock_irt_tracked_count() equals `0`
   - Expected: mock_irt_is_tracked("pre_init_mod") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all tracking on init")
step("Verify: clears all tracking on init")
mock_irt_init()
mock_irt_begin_module("pre_init_mod")
mock_irt_track_func("pre_init_mod", "fn_pre")
mock_irt_init()
expect(mock_irt_tracked_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(mock_irt_is_tracked("pre_init_mod")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-CORE-INTERPRETER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2805598d9cef8df7bb755612c0edc35fc3d646420bfc6fc9e7b9df32b303a6c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2805598d9cef8df7bb755612c0edc35fc3d646420bfc6fc9e7b9df32b303a6c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2805598d9cef8df7bb755612c0edc35fc3d646420bfc6fc9e7b9df32b303a6c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl
mirror: doc/06_spec/unit/compiler_core/interpreter/interp_resource_tracker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/interpreter/interp_resource_tracker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/interpreter/interp_resource_tracker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl:342:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes a registered function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl:356:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for unknown function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl:364:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'remove does not break other entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
