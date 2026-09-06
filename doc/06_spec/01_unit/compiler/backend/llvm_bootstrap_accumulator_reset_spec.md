# llvm_bootstrap_accumulator_reset_spec

> Regression guard for the module-level-accumulator-never-reset defect family.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llvm_bootstrap_accumulator_reset_spec

Regression guard for the module-level-accumulator-never-reset defect family.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression guard for the module-level-accumulator-never-reset defect family.

Both members of this family were invisible to every single-unit test, because
the per-instance mirror was always correct. Only N>=2 units in ONE process
expose them, so every case below builds TWO translators and asserts unit two is
uncontaminated by unit one.

  1. _llvm_bootstrap_ir_text (llvm_ir_builder.spl) -- fixed d5c65c647922 by
     clearing it in LlvmIRBuilder.create(), symmetric with the fresh
     rt_string_builder_new() on the same line.
  2. _llvm_bootstrap_string_global_text (asm_constraints_helpers.spl) -- fixed
     by clearing it in MirToLlvm.create()/create_baremetal(), symmetric with
     the per-instance string_global_text/string_counter initialised there.
     translate_module() also resets it, but the bootstrap object emitters
     (bootstrap_emit_real_llvm_object / bootstrap_emit_real_llvm_module_object)
     never call translate_module.

Assertions are on positive artifacts -- the exact decl count and the exact
symbol name emitted for unit two -- never on the absence of an error.
See doc/08_tracking/bug/llvm_bootstrap_string_globals_not_reset_2026-08-01.md

## Scenarios

### LLVM bootstrap module-level accumulators reset per compilation unit

#### does not carry unit one's string constants into unit two

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not carry unit one's string constants into unit two
   - Expected: a_name equals `@.str.0`
   - Expected: b_name equals `@.str.0`
   - Expected: count_occurrences(after_a, DECL_MARKER) equals `1`
   - Expected: count_occurrences(after_b, DECL_MARKER) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not carry unit one's string constants into unit two")
rt_env_set("SIMPLE_BOOTSTRAP", "1")

var a = MirToLlvm.create("mod_a", CodegenTarget.X86_64, nil)
val a_name = a.add_string_global("AAA_UNIT_ONE")
val after_a = llvm_bootstrap_string_globals_text()

var b = MirToLlvm.create("mod_b", CodegenTarget.X86_64, nil)
val b_name = b.add_string_global("BBB_UNIT_TWO")
val after_b = llvm_bootstrap_string_globals_text()

# string_counter is per-instance, so BOTH units name their first
# constant @.str.0. If unit two inherits unit one's decl the emitted
# module defines @.str.0 twice and llc rejects it as a redefinition.
expect(a_name).to_equal("@.str.0")
expect(b_name).to_equal("@.str.0")

# Positive artifacts: unit one emitted exactly its own one decl, and
# unit two emitted exactly its own one decl naming its own constant.
expect(count_occurrences(after_a, DECL_MARKER)).to_equal(1)
expect(count_occurrences(after_b, DECL_MARKER)).to_equal(1)
expect(after_b).to_contain("BBB_UNIT_TWO")
expect(after_b).to_contain("@.str.0")
expect(after_b).to_not_contain("AAA_UNIT_ONE")
```

</details>

#### keeps the per-instance string_global_text mirror unit-local

- keeps the per-instance string_global_text mirror unit-local
   - Expected: count_occurrences(b.string_global_text, DECL_MARKER) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the per-instance string_global_text mirror unit-local")
rt_env_set("SIMPLE_BOOTSTRAP", "1")

var a = MirToLlvm.create("mod_a2", CodegenTarget.X86_64, nil)
a.add_string_global("AAA_UNIT_ONE")
var b = MirToLlvm.create("mod_b2", CodegenTarget.X86_64, nil)
b.add_string_global("BBB_UNIT_TWO")

# This mirror was always correct -- that is exactly why the defect was
# invisible. Pinned so a future "fix" cannot make the global right by
# making the instance field wrong.
expect(count_occurrences(b.string_global_text, DECL_MARKER)).to_equal(1)
expect(b.string_global_text).to_contain("BBB_UNIT_TWO")
expect(b.string_global_text).to_not_contain("AAA_UNIT_ONE")
```

</details>

#### does not carry unit one's IR text into unit two

- does not carry unit one's IR text into unit two
   - Expected: count_occurrences(ir_a, "source_filename") equals `1`
   - Expected: count_occurrences(ir_b, "source_filename") equals `1`
   - Expected: count_occurrences(ir_b, "target triple") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not carry unit one's IR text into unit two")
rt_env_set("SIMPLE_BOOTSTRAP", "1")

var a = MirToLlvm.create("mod_a3", CodegenTarget.X86_64, nil)
a.builder.emit_module_header()
val ir_a = a.builder.build()

var b = MirToLlvm.create("mod_b3", CodegenTarget.X86_64, nil)
b.builder.emit_module_header()
val ir_b = b.builder.build()

# Positive artifacts: unit two's IR carries exactly ONE module header
# and it is unit two's own. Duplicate source_filename/target triple
# lines mid-file are what llc reports as "expected top-level entity".
expect(count_occurrences(ir_a, "source_filename")).to_equal(1)
expect(count_occurrences(ir_b, "source_filename")).to_equal(1)
expect(count_occurrences(ir_b, "target triple")).to_equal(1)
expect(ir_b).to_contain("mod_b3")
expect(ir_b).to_not_contain("mod_a3")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `488b8dfb0f26cac5b36a47734553edfacfdbda55707a12255a30b74a978fdc99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `488b8dfb0f26cac5b36a47734553edfacfdbda55707a12255a30b74a978fdc99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `488b8dfb0f26cac5b36a47734553edfacfdbda55707a12255a30b74a978fdc99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not carry unit one's string constants into unit two' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the per-instance string_global_text mirror unit-local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not carry unit one's IR text into unit two' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
