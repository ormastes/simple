# AST arena harden — delayed retirement + slot poisoning (M2 index-based equivalent, 2026-07-29)

> Purpose: Prove that AST arena harden — delayed retirement + slot poisoning (M2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AST arena harden — delayed retirement + slot poisoning (M2 index-based equivalent, 2026-07-29)

Purpose: Prove that AST arena harden — delayed retirement + slot poisoning (M2).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Frontend / AST arena |
| Status | Active |
| Source | `test/01_unit/compiler/ast_arena_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AST arena harden — delayed retirement + slot poisoning (M2).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AST arena harden — delayed retirement + slot poisoning (M2)

#### gate off: retention is fully inert, identical to today

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gate off: retention is fully inert, identical to today
- Verify: gate off: retention is fully inert, identical to today
   - Expected: ast_harden_retired_window_depth() equals `0`
   - Expected: ast_harden_lookup_decl_tag(prior_gen, 0) equals `-1`
   - Expected: ast_harden_lookup_module_decl_slot(prior_gen, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gate off: retention is fully inert, identical to today")
step("Verify: gate off: retention is fully inert, identical to today")
# @req: REQ-COMP-AST-ARENA-HARDEN-DELAYED-RETIREMENT-SLOT-001
assert_true(rt_env_set("SIMPLE_AST_GEN_HARDEN", "0"))
ast_reset()
assert_false(ast_gen_harden_enabled())
val prior_gen = ast_generation() - 1
expect(ast_harden_retired_window_depth()).to_equal(0)
expect(ast_harden_lookup_decl_tag(prior_gen, 0)).to_equal(-1)
expect(ast_harden_lookup_module_decl_slot(prior_gen, 0)).to_equal(-1)
```

</details>

#### gate on: a stale (generation, idx) pair reads back the poison sentinel within the delay window

- gate on: a stale (generation, idx) pair reads back the poison sentinel within the delay window
- Verify: gate on: a stale (generation, idx) pair reads back the poison sentinel within the delay window
   - Expected: ast_harden_lookup_decl_tag(mint_gen, decl_idx) equals `-777`
   - Expected: ast_harden_lookup_module_decl_slot(mint_gen, 0) equals `-777`
   - Expected: ast_harden_lookup_decl_tag(mint_gen, 999) equals `-1`
   - Expected: ast_harden_lookup_decl_tag(999999999, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gate on: a stale (generation, idx) pair reads back the poison sentinel within the delay window")
step("Verify: gate on: a stale (generation, idx) pair reads back the poison sentinel within the delay window")
assert_true(rt_env_set("SIMPLE_AST_GEN_HARDEN", "1"))
assert_true(rt_env_set("SIMPLE_MEM_ARENA_DELAY_SLOTS", "4"))
ast_reset()
assert_true(ast_gen_harden_enabled())

# Mint a decl and a module-decl-slot entry at the live generation.
val mint_gen = ast_generation()
val decl_idx = decl_alloc(DECL_FN, -1)
module_add_decl(decl_idx)

# Reset -> retires mint_gen's (now stale) slots as a poisoned snapshot.
ast_reset()
expect(ast_harden_lookup_decl_tag(mint_gen, decl_idx)).to_equal(-777)
expect(ast_harden_lookup_module_decl_slot(mint_gen, 0)).to_equal(-777)

# Out-of-bounds index within a retained generation: outside the
# snapshot, not poison.
expect(ast_harden_lookup_decl_tag(mint_gen, 999)).to_equal(-1)
# A generation that was never retired: outside the window.
expect(ast_harden_lookup_decl_tag(999999999, 0)).to_equal(-1)
```

</details>

#### the L6 stale-generation diagnostic still fires with the harden gate on

- the L6 stale-generation diagnostic still fires with the harden gate on
- Verify: the L6 stale-generation diagnostic still fires with the harden gate on


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the L6 stale-generation diagnostic still fires with the harden gate on")
step("Verify: the L6 stale-generation diagnostic still fires with the harden gate on")
assert_true(rt_env_set("SIMPLE_AST_GEN_HARDEN", "1"))
assert_true(rt_env_set("SIMPLE_AST_GEN_CHECK", "1"))
ast_reset()
val cur = ast_generation()
assert_false(ast_gen_check_index("DeclId", 0, cur))
assert_true(ast_gen_check_index("DeclId", 0, cur - 1))
assert_true(rt_env_set("SIMPLE_AST_GEN_CHECK", "0"))
```

</details>

#### the delay window is bounded: shrinking it evicts older generations

- the delay window is bounded: shrinking it evicts older generations
- Verify: the delay window is bounded: shrinking it evicts older generations
   - Expected: ast_harden_lookup_decl_tag(mint_gen, decl_idx) equals `-777`
   - Expected: ast_harden_retired_window_depth() equals `1`
   - Expected: ast_harden_lookup_decl_tag(mint_gen, decl_idx) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the delay window is bounded: shrinking it evicts older generations")
step("Verify: the delay window is bounded: shrinking it evicts older generations")
assert_true(rt_env_set("SIMPLE_AST_GEN_HARDEN", "1"))
assert_true(rt_env_set("SIMPLE_MEM_ARENA_DELAY_SLOTS", "4"))
ast_reset()
val mint_gen = ast_generation()
val decl_idx = decl_alloc(DECL_FN, -1)
ast_reset()
# Still within a 4-deep window: retained and poisoned.
expect(ast_harden_lookup_decl_tag(mint_gen, decl_idx)).to_equal(-777)

# Shrink the window to 1 and force further resets: mint_gen's slot
# ages out and the query reports "outside the window" again.
assert_true(rt_env_set("SIMPLE_MEM_ARENA_DELAY_SLOTS", "1"))
ast_reset()
expect(ast_harden_retired_window_depth()).to_equal(1)
expect(ast_harden_lookup_decl_tag(mint_gen, decl_idx)).to_equal(-1)
assert_true(rt_env_set("SIMPLE_AST_GEN_HARDEN", "0"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-AST-ARENA-HARDEN-DELAYED-RETIREMENT-SLOT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e7be261035c039cb4d2f24d11b9e3aa41c015746ec7fce68b49f2e41f458ac9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e7be261035c039cb4d2f24d11b9e3aa41c015746ec7fce68b49f2e41f458ac9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e7be261035c039cb4d2f24d11b9e3aa41c015746ec7fce68b49f2e41f458ac9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/ast_arena_harden_spec.spl
mirror: doc/06_spec/01_unit/compiler/ast_arena_harden_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/ast_arena_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/ast_arena_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/ast_arena_harden_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/ast_arena_harden_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gate off: retention is fully inert, identical to today' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/ast_arena_harden_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gate on: a stale (generation, idx) pair reads back the poison sentinel within the delay window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/ast_arena_harden_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the L6 stale-generation diagnostic still fires with the harden gate on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
