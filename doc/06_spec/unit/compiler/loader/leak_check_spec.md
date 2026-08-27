# leak_check_spec

> Purpose: Prove that Load/Unload cycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# leak_check_spec

Purpose: Prove that Load/Unload cycle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/leak_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Load/Unload cycle.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Load/Unload cycle

#### module is tracked after load

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- module is tracked after load
- Verify: module is tracked after load
   - Expected: mock_registry_is_tracked("/lib/module_a.smf") is true
   - Expected: mock_registry_module_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module is tracked after load")
step("Verify: module is tracked after load")
# @req: REQ-COMPILER-LOADER-001
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
expect(mock_registry_is_tracked("/lib/module_a.smf")).to_equal(true)
expect(mock_registry_module_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### module is not tracked before load

- module is not tracked before load
- Verify: module is not tracked before load
   - Expected: mock_registry_is_tracked("/lib/not_loaded.smf") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module is not tracked before load")
step("Verify: module is not tracked before load")
mock_registry_reset()
expect(mock_registry_is_tracked("/lib/not_loaded.smf")).to_equal(false)
```

</details>

#### exec symbols tracked per module

- exec symbols tracked per module
- Verify: exec symbols tracked per module
   - Expected: mock_exec_mapped_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec symbols tracked per module")
step("Verify: exec symbols tracked per module")
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_foo")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_bar")
expect(mock_exec_mapped_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### unload frees all exec symbols

- unload frees all exec symbols
- Verify: unload frees all exec symbols
   - Expected: mock_exec_mapped_count() equals `0`
   - Expected: mock_exec_was_freed("fn_foo") is true
   - Expected: mock_exec_was_freed("fn_bar") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unload frees all exec symbols")
step("Verify: unload frees all exec symbols")
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_foo")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_bar")
mock_registry_unload("/lib/module_a.smf")
expect(mock_exec_mapped_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(mock_exec_was_freed("fn_foo")).to_equal(true)
expect(mock_exec_was_freed("fn_bar")).to_equal(true)
```

</details>

#### unload removes module from registry

- unload removes module from registry
- Verify: unload removes module from registry
   - Expected: mock_registry_is_tracked("/lib/module_a.smf") is false
   - Expected: mock_registry_module_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unload removes module from registry")
step("Verify: unload removes module from registry")
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
mock_registry_unload("/lib/module_a.smf")
expect(mock_registry_is_tracked("/lib/module_a.smf")).to_equal(false)
expect(mock_registry_module_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### unload of unknown module is safe (no crash)

- unload of unknown module is safe (no crash)
- Verify: unload of unknown module is safe (no crash)
   - Expected: mock_registry_module_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unload of unknown module is safe (no crash)")
step("Verify: unload of unknown module is safe (no crash)")
mock_registry_reset()
mock_registry_unload("/lib/nonexistent.smf")
expect(mock_registry_module_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### Hot-reload cycle

#### old symbols freed before new ones registered

- old symbols freed before new ones registered
- Verify: old symbols freed before new ones registered
   - Expected: mock_exec_was_freed("hot_fn") is false
   - Expected: mock_exec_was_freed("hot_fn") is true
   - Expected: mock_exec_mapped_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("old symbols freed before new ones registered")
step("Verify: old symbols freed before new ones registered")
mock_registry_reset()
# First load
mock_registry_register("/lib/module_hot.smf")
mock_registry_add_exec_symbol("/lib/module_hot.smf", "hot_fn")
expect(mock_exec_was_freed("hot_fn")).to_equal(false)
# Unload (simulates hot-reload)
mock_registry_unload("/lib/module_hot.smf")
expect(mock_exec_was_freed("hot_fn")).to_equal(true)
# Re-register (new load)
mock_exec_reset()
mock_registry_register("/lib/module_hot.smf")
mock_registry_add_exec_symbol("/lib/module_hot.smf", "hot_fn")
expect(mock_exec_mapped_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### multiple load/unload cycles clean up correctly

- multiple load/unload cycles clean up correctly
- Verify: multiple load/unload cycles clean up correctly
   - Expected: mock_registry_module_count() equals `0`
   - Expected: mock_exec_mapped_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple load/unload cycles clean up correctly")
step("Verify: multiple load/unload cycles clean up correctly")
mock_registry_reset()
var cycle = 0
while cycle < 3:
    mock_registry_register("/lib/cycle_mod.smf")
    mock_registry_add_exec_symbol("/lib/cycle_mod.smf", "cycle_fn")
    mock_registry_unload("/lib/cycle_mod.smf")
    cycle = cycle + 1
expect(mock_registry_module_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(mock_exec_mapped_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### JIT symbol attribution

#### JIT symbol attributed to triggering module

- JIT symbol attributed to triggering module
- Verify: JIT symbol attributed to triggering module
   - Expected: origin equals `/lib/caller.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JIT symbol attributed to triggering module")
step("Verify: JIT symbol attributed to triggering module")
mock_registry_reset()
mock_registry_register("/lib/caller.smf")
mock_registry_add_jit_symbol("/lib/caller.smf", "Vec$i64_push")
val origin = mock_registry_get_jit_origin("Vec$i64_push")
expect(origin).to_equal("/lib/caller.smf")
```

</details>

#### JIT symbol freed when originating module unloads

- JIT symbol freed when originating module unloads
- Verify: JIT symbol freed when originating module unloads
   - Expected: mock_exec_was_freed("Vec$i64_push") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JIT symbol freed when originating module unloads")
step("Verify: JIT symbol freed when originating module unloads")
mock_registry_reset()
mock_registry_register("/lib/caller.smf")
mock_registry_add_exec_symbol("/lib/caller.smf", "Vec$i64_push")
mock_registry_add_jit_symbol("/lib/caller.smf", "Vec$i64_push")
mock_registry_unload("/lib/caller.smf")
expect(mock_exec_was_freed("Vec$i64_push")).to_equal(true)
```

</details>

#### JIT origin removed after unload

- JIT origin removed after unload
- Verify: JIT origin removed after unload
   - Expected: origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JIT origin removed after unload")
step("Verify: JIT origin removed after unload")
mock_registry_reset()
mock_registry_register("/lib/caller.smf")
mock_registry_add_jit_symbol("/lib/caller.smf", "Map$text_i64_insert")
mock_registry_unload("/lib/caller.smf")
val origin = mock_registry_get_jit_origin("Map$text_i64_insert")
expect(origin).to_equal("")
```

</details>

#### JIT symbols from different modules tracked independently

- JIT symbols from different modules tracked independently
- Verify: JIT symbols from different modules tracked independently
   - Expected: mock_registry_get_jit_origin("jit_sym_a") equals ``
   - Expected: mock_registry_get_jit_origin("jit_sym_b") equals `/lib/mod_b.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JIT symbols from different modules tracked independently")
step("Verify: JIT symbols from different modules tracked independently")
mock_registry_reset()
mock_registry_register("/lib/mod_a.smf")
mock_registry_register("/lib/mod_b.smf")
mock_registry_add_jit_symbol("/lib/mod_a.smf", "jit_sym_a")
mock_registry_add_jit_symbol("/lib/mod_b.smf", "jit_sym_b")
mock_registry_unload("/lib/mod_a.smf")
# mod_a's JIT freed; mod_b's JIT still tracked
expect(mock_registry_get_jit_origin("jit_sym_a")).to_equal("")
expect(mock_registry_get_jit_origin("jit_sym_b")).to_equal("/lib/mod_b.smf")
```

</details>

### SMF cache ref counting

#### SMF ref count increases when module accesses it

- SMF ref count increases when module accesses it
- Verify: SMF ref count increases when module accesses it
   - Expected: mock_smf_get_count("/cache/std.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SMF ref count increases when module accesses it")
step("Verify: SMF ref count increases when module accesses it")
mock_smf_reset()
mock_smf_inc("/cache/std.smf")
expect(mock_smf_get_count("/cache/std.smf")).to_equal(1)
```

</details>

#### SMF not evicted while ref count > 0

- SMF not evicted while ref count > 0
- Verify: SMF not evicted while ref count > 0
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is false
   - Expected: mock_smf_get_count("/cache/shared.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SMF not evicted while ref count > 0")
step("Verify: SMF not evicted while ref count > 0")
mock_smf_reset()
mock_smf_inc("/cache/shared.smf")
mock_smf_inc("/cache/shared.smf")
mock_smf_dec("/cache/shared.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(false)
expect(mock_smf_get_count("/cache/shared.smf")).to_equal(1)
```

</details>

#### SMF evicted when last module unloads

- SMF evicted when last module unloads
- Verify: SMF evicted when last module unloads
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is true
   - Expected: mock_smf_get_count("/cache/shared.smf") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SMF evicted when last module unloads")
step("Verify: SMF evicted when last module unloads")
mock_smf_reset()
mock_smf_inc("/cache/shared.smf")
mock_smf_dec("/cache/shared.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(true)
expect(mock_smf_get_count("/cache/shared.smf")).to_equal(0)
```

</details>

#### multiple modules share SMF — eviction only on last unload

- multiple modules share SMF — eviction only on last unload
- Verify: multiple modules share SMF — eviction only on last unload
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is false
   - Expected: mock_smf_get_count("/cache/shared.smf") equals `1`
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple modules share SMF — eviction only on last unload")
step("Verify: multiple modules share SMF — eviction only on last unload")
mock_registry_reset()
mock_registry_register("/lib/mod_a.smf")
mock_registry_register("/lib/mod_b.smf")
mock_registry_add_smf("/lib/mod_a.smf", "/cache/shared.smf")
mock_registry_add_smf("/lib/mod_b.smf", "/cache/shared.smf")
# Unload first module — SMF still ref'd by mod_b
mock_registry_unload("/lib/mod_a.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(false)
expect(mock_smf_get_count("/cache/shared.smf")).to_equal(1)
# Unload second module — SMF now evicted
mock_registry_unload("/lib/mod_b.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(true)
```

</details>

### Full teardown

#### teardown frees all modules

- teardown frees all modules
- Verify: teardown frees all modules
   - Expected: mock_registry_module_count() equals `0`
   - Expected: mock_exec_mapped_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("teardown frees all modules")
step("Verify: teardown frees all modules")
mock_registry_reset()
mock_registry_register("/lib/mod_a.smf")
mock_registry_register("/lib/mod_b.smf")
mock_registry_register("/lib/mod_c.smf")
mock_registry_add_exec_symbol("/lib/mod_a.smf", "fn_a")
mock_registry_add_exec_symbol("/lib/mod_b.smf", "fn_b")
# Simulate destroy() — unload all
val paths_to_unload = ["/lib/mod_a.smf", "/lib/mod_b.smf", "/lib/mod_c.smf"]
for path in paths_to_unload:
    mock_registry_unload(path)
expect(mock_registry_module_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(mock_exec_mapped_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### teardown with zero modules is safe

- teardown with zero modules is safe
- Verify: teardown with zero modules is safe
   - Expected: mock_registry_module_count() equals `0`
   - Expected: mock_exec_mapped_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("teardown with zero modules is safe")
step("Verify: teardown with zero modules is safe")
mock_registry_reset()
# No modules loaded — teardown should be a no-op
expect(mock_registry_module_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(mock_exec_mapped_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### after teardown, re-registration works (REPL restart)

- after teardown, re-registration works (REPL restart)
- Verify: after teardown, re-registration works (REPL restart)
   - Expected: mock_registry_is_tracked("/lib/mod.smf") is true
   - Expected: mock_exec_mapped_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after teardown, re-registration works (REPL restart)")
step("Verify: after teardown, re-registration works (REPL restart)")
mock_registry_reset()
mock_registry_register("/lib/mod.smf")
mock_registry_add_exec_symbol("/lib/mod.smf", "fn_x")
mock_registry_unload("/lib/mod.smf")
mock_exec_reset()
# Re-register after teardown (simulates REPL restart)
mock_registry_register("/lib/mod.smf")
mock_registry_add_exec_symbol("/lib/mod.smf", "fn_x")
expect(mock_registry_is_tracked("/lib/mod.smf")).to_equal(true)
expect(mock_exec_mapped_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-LOADER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4cf6c315a2d4b9a71a7c34994d2e1d793a2190af7f18dfbb336d524ee604563a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cf6c315a2d4b9a71a7c34994d2e1d793a2190af7f18dfbb336d524ee604563a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cf6c315a2d4b9a71a7c34994d2e1d793a2190af7f18dfbb336d524ee604563a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/loader/leak_check_spec.spl
mirror: doc/06_spec/unit/compiler/loader/leak_check_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/leak_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/leak_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/leak_check_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/loader/leak_check_spec.spl:279:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module is tracked after load' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/leak_check_spec.spl:289:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module is not tracked before load' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/leak_check_spec.spl:296:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exec symbols tracked per module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
