# llvm_ir_builder_spec

> Verifies the llvm ir builder behaviour end to end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llvm_ir_builder_spec

Verifies the llvm ir builder behaviour end to end.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/llvm_ir_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llvm ir builder behaviour end to end.
Audience: engineers maintaining this component and its specs.

## Scenarios

### LLVM IR Builder

#### emits the module header from the selected target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: emits the module header from the selected target
   - Expected: lines.len() equals `5`
   - Expected: lines[0] equals `; ModuleID = 'demo.module'`
   - Expected: lines[1] equals `source_filename = "demo.module.spl"`
   - Expected: lines[4] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKEND-LlvmIrBuilder-001
step("Verify: emits the module header from the selected target")
val builder = new_builder()

builder.emit_module_header()

val lines = emitted_lines(builder)
expect(lines.len()).to_equal(5)  # oracle: value fixed by the spec contract
expect(lines[0]).to_equal("; ModuleID = 'demo.module'")
expect(lines[1]).to_equal("source_filename = \"demo.module.spl\"")
expect(lines[2]).to_contain("target datalayout = \"")
expect(lines[3]).to_contain("target triple = \"")
expect(lines[4]).to_equal("")
```

</details>

#### creates fresh locals and wraps a function body

- Verify: creates fresh locals and wraps a function body
   - Expected: local0 equals `%t0`
   - Expected: local1 equals `%t1`
   - Expected: lines[0] equals `define i64 @add_numbers(i64 %lhs, i64 %rhs) nounwind {`
   - Expected: lines[1] equals `  ret i64 %lhs`
   - Expected: lines[2] equals `}`
   - Expected: lines[3] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKEND-LlvmIrBuilder-001
step("Verify: creates fresh locals and wraps a function body")
val builder = new_builder()
val local0 = builder.fresh_local()
val local1 = builder.fresh_local()

# NAMED temporaries (`%tN`), not anonymous `%N`: llc rejects an
# anonymous `%0` interspersed with named `%lN` locals ("instruction
# expected to be numbered '%3' or greater"). See fresh_local's
# docstring in llvm_ir_builder.spl:258-270.
expect(local0).to_equal("%t0")
expect(local1).to_equal("%t1")

builder.start_function("add_numbers", ["i64 %lhs", "i64 %rhs"], "i64")
builder.emit_ret("i64", "%lhs")
builder.end_function()

val lines = emitted_lines(builder)
expect(lines[0]).to_equal("define i64 @add_numbers(i64 %lhs, i64 %rhs) nounwind {")
expect(lines[1]).to_equal("  ret i64 %lhs")
expect(lines[2]).to_equal("}")
expect(lines[3]).to_equal("")
```

</details>

#### emits direct arithmetic, memory, and comparison instructions

- Verify: emits direct arithmetic, memory, and comparison instructions
   - Expected: lines[0] equals `  %2 = add i64 %0, %1`
   - Expected: lines[1] equals `  %3 = load i64, ptr %ptr, align 8`
   - Expected: lines[2] equals `  store i64 %3, ptr %ptr, align 8`
   - Expected: lines[3] equals `  %4 = icmp eq i64 %3, %2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKEND-LlvmIrBuilder-001
step("Verify: emits direct arithmetic, memory, and comparison instructions")
val builder = new_builder()

builder.emit_add("%2", "i64", "%0", "%1")
builder.emit_load("%3", "i64", "%ptr")
builder.emit_store("i64", "%3", "%ptr")
builder.emit_icmp_eq("%4", "i64", "%3", "%2")

val lines = emitted_lines(builder)
expect(lines[0]).to_equal("  %2 = add i64 %0, %1")
expect(lines[1]).to_equal("  %3 = load i64, ptr %ptr, align 8")
expect(lines[2]).to_equal("  store i64 %3, ptr %ptr, align 8")
expect(lines[3]).to_equal("  %4 = icmp eq i64 %3, %2")
```

</details>

### LLVM IR Builder bootstrap per-instance parity

#### emits every function header before recording function state

- Verify: emits every function header before recording function state


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKEND-LlvmIrBuilder-001
step("Verify: emits every function header before recording function state")
val source = rt_file_read_text(
    "src/compiler/70.backend/backend/llvm_ir_builder.spl"
) ?? ""
val plain_start = source.find("    me start_function(name:")
val opt_start = source.find("    me start_function_opt(")
val attrs_start = source.find("    me start_function_with_attrs(")
val attrs_end = source.find("    me end_function():")
val plain_body = source.substring(plain_start, opt_start)
val opt_body = source.substring(opt_start, attrs_start)
val attrs_body = source.substring(attrs_start, attrs_end)

expect(plain_body.find("self.emit(\"define ")).to_be_less_than(
    plain_body.find("self.current_function = Some(name)")
)
expect(opt_body.find("self.emit(\"define ")).to_be_less_than(
    opt_body.find("self.current_function = Some(name)")
)
expect(attrs_body.find("self.emit(\"{prefix} ")).to_be_less_than(
    attrs_body.find("self.current_function = Some(name)")
)
```

</details>

#### does not prepend a previous module's IR to the next module

- Verify: does not prepend a previous module's IR to the next module
   - Expected: ir_a contains `ModuleID = 'mod_a'`
   - Expected: ir_b does not contain `mod_a`
   - Expected: ir_b contains `ModuleID = 'mod_b'`
   - Expected: ir_b.split("target triple").len() equals `2`
   - Expected: ir_b.split("source_filename").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKEND-LlvmIrBuilder-001
step("Verify: does not prepend a previous module's IR to the next module")
# SIMPLE_BOOTSTRAP must use the same per-instance runtime string
# builder as every other mode. Module B therefore cannot inherit any
# text from module A.
rt_env_set("SIMPLE_BOOTSTRAP", "1")

val triple = LlvmTargetTriple.from_target(CodegenTarget.X86_64)

val a = LlvmIRBuilder.create("mod_a", triple)
a.emit_module_header()
a.start_function("mod_a", [], "i64")
a.emit_ret("i64", "42")
a.end_function()
val ir_a = llvm_ir_builder_build(a)

val b = LlvmIRBuilder.create("mod_b", triple)
b.emit_module_header()
b.start_function("mod_b", [], "i64")
b.emit_ret("i64", "7")
b.end_function()
val ir_b = llvm_ir_builder_build(b)

rt_env_set("SIMPLE_BOOTSTRAP", "")

# Module A is well-formed on its own.
expect(ir_a.contains("ModuleID = 'mod_a'")).to_equal(true)

# Module B must be a STANDALONE module: no trace of module A.
expect(ir_b.contains("mod_a")).to_equal(false)
expect(ir_b.contains("ModuleID = 'mod_b'")).to_equal(true)

# Exactly one module header in B (split on N occurrences -> N+1 parts).
expect(ir_b.split("target triple").len()).to_equal(2)
expect(ir_b.split("source_filename").len()).to_equal(2)
```

</details>

#### does not let an incidental builder erase an active module

- Verify: does not let an incidental builder erase an active module
   - Expected: ir.split("ModuleID = 'top'").len() equals `2`
   - Expected: ir.split("define i64 @body()").len() equals `2`
   - Expected: ir.split("; retained tail").len() equals `2`
   - Expected: ir does not contain `incidental`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKEND-LlvmIrBuilder-001
step("Verify: does not let an incidental builder erase an active module")
rt_env_set("SIMPLE_BOOTSTRAP", "1")

val triple = LlvmTargetTriple.from_target(CodegenTarget.X86_64)
val top = LlvmIRBuilder.create("top", triple)
top.emit_module_header()
top.start_function("body", [], "i64")
top.emit_ret("i64", "42")
top.end_function()

# A second builder owns a distinct runtime string-builder handle, so
# merely constructing it cannot affect the active top-level builder.
val incidental = LlvmIRBuilder.create("incidental", triple)
val _ = incidental.local_counter

top.emit("; retained tail")
val ir = llvm_ir_builder_build(top)

rt_env_set("SIMPLE_BOOTSTRAP", "")

expect(ir.split("ModuleID = 'top'").len()).to_equal(2)
expect(ir.split("define i64 @body()").len()).to_equal(2)
expect(ir.split("; retained tail").len()).to_equal(2)
expect(ir.contains("incidental")).to_equal(false)
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

- `REQ-SSPEC-UNIT`
- `REQ-BACKEND-LlvmIrBuilder-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e607d3eafd88510275dd3c62f7f563cea4d9209f34a1cf2a9805cbd47426e25a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e607d3eafd88510275dd3c62f7f563cea4d9209f34a1cf2a9805cbd47426e25a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e607d3eafd88510275dd3c62f7f563cea4d9209f34a1cf2a9805cbd47426e25a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/backend/llvm_ir_builder_spec.spl
mirror: doc/06_spec/unit/compiler/backend/llvm_ir_builder_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/compiler/backend/llvm_ir_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/llvm_ir_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/llvm_ir_builder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/llvm_ir_builder_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/backend/llvm_ir_builder_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the module header from the selected target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/llvm_ir_builder_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates fresh locals and wraps a function body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/llvm_ir_builder_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits direct arithmetic, memory, and comparison instructions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
