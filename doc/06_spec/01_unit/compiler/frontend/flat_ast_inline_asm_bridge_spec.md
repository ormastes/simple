# Flat Ast Inline Asm Bridge Specification

> Tests covering Flat AST bridge inline asm fidelity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Ast Inline Asm Bridge Specification

## Scenarios

### Flat AST bridge inline asm fidelity

#### keeps the clobber and options dispatch as a canonical multiline if/elif chain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the clobber and options dispatch as a canonical multiline if/elif chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the clobber and options dispatch as a canonical multiline if/elif chain")
val source = read_file_text("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl")
expect(source).to_contain(
    "        if item.starts_with(\"clobber_abi:\"):\n" +
    "            clobber_abis.push(item[12..])\n" +
    "        elif item.starts_with(\"options:\"):\n"
)
expect(source).to_contain(
    "                if normalized_option != \"\":\n" +
    "                    asm_options.push(normalized_option)\n" +
    "        elif item.starts_with(\"clobber:\"):\n" +
    "            plain_clobbers.push(item[8..])\n"
)
expect(source.contains("if item.starts_with(\"clobber_abi:\"): clobber_abis.push")).to_be(false)
expect(source.contains("elif item.starts_with(\"clobber:\"): plain_clobbers.push")).to_be(false)
```

</details>

#### preserves inline asm as typed AsmBlock nodes

- preserves inline asm as typed AsmBlock nodes
   - Expected: first_asm_template(src) equals `cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves inline asm as typed AsmBlock nodes")
val src = "fn test():\n    asm(\"cli\")\n"
expect(first_asm_template(src)).to_equal("cli")
```

</details>

#### preserves volatile asm text

- preserves volatile asm text
   - Expected: first_asm_template(src) equals `bkpt #0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves volatile asm text")
val src = "fn test():\n    asm volatile(\"bkpt #0\")\n"
expect(first_asm_template(src)).to_equal("bkpt #0")
```

</details>

#### retains named RV64 register and immediate operands in the typed AST

- retains named RV64 register and immediate operands in the typed AST
   - Expected: first_asm_template(src) equals `addi {dst}, {src}, {shift}`
   - Expected: rv64_named_immediate_score(src) equals `173`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains named RV64 register and immediate operands in the typed AST")
val src = "fn test(src: i64):\n    var dst = 0\n    asm volatile(\"addi {dst}, {src}, {shift}\", dst = out(reg) dst, src = in(reg) src, shift = in(imm) 4)\n"
expect(first_asm_template(src)).to_equal("addi {dst}, {src}, {shift}")
expect(rv64_named_immediate_score(src)).to_equal(173)
```

</details>

#### retains clobbers ABI options and inout output through the typed bridge

- retains clobbers ABI options and inout output through the typed bridge
   - Expected: asm_metadata_score(src) equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains clobbers ABI options and inout output through the typed bridge")
val src = "fn test(input: i64):\n    var output = 0\n    asm volatile(\"add {0}, {0}, 1\", inout(reg) input => output, clobber_abi(\"C\"), options(nostack, readonly))\n"
expect(asm_metadata_score(src)).to_equal(190)
```

</details>

#### retains metadata and distinct inout expressions through MIR and LLVM backend

- retains metadata and distinct inout expressions through MIR and LLVM backend
   - Expected: mir_metadata_score(mir) equals `390`
   - Expected: llvm contains `asm sideeffect "add $0, $0, 1", "=r,0,~{rax}`
   - Expected: llvm contains ` = call i64 asm sideeffect`
   - Expected: llvm contains `memory(read)`
   - Expected: llvm does not contain `alignstack`
   - Expected: c_inline_asm_clause_score(c_source) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains metadata and distinct inout expressions through MIR and LLVM backend")
val src = "fn test(input: i64):\n    var output = 0\n    asm volatile(\"add {0}, {0}, 1\", inout(reg) input => output, clobber_abi(\"C\"), options(nostack, readonly))\n"
val mir = lower_inline_asm_mir(src)
expect(mir_metadata_score(mir)).to_equal(390)
val llvm = MirToLlvm.create("test.inline.asm.metadata", CodegenTarget.X86_64, nil).translate_module(mir)
expect(llvm.contains("asm sideeffect \"add $0, $0, 1\", \"=r,0,~{rax}")).to_equal(true)
expect(llvm.contains(" = call i64 asm sideeffect")).to_equal(true)
expect(llvm.contains("memory(read)")).to_equal(true)
expect(llvm.contains("alignstack")).to_equal(false)
val c_source = MirToC.create("test.inline.asm.metadata").translate_module(mir)
expect(c_inline_asm_clause_score(c_source)).to_equal(15)
```

</details>

#### pairs duplicate-named inout operands by stable source index

- pairs duplicate-named inout operands by stable source index
   - Expected: mir_pair_identity_score(lower_inline_asm_mir(src)) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pairs duplicate-named inout operands by stable source index")
val src = "fn test(left: i64, right: i64):\n    var first = 0\n    var second = 0\n    asm volatile(\"add {0}, {1}, 1\", io = inout(reg) left => first, io = inout(reg) right => second)\n"
expect(mir_pair_identity_score(lower_inline_asm_mir(src))).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Flat AST bridge inline asm fidelity.
- Flat AST bridge inline asm fidelity

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db5842c6e47959d7bccb81fd3096f4909d7bbbe6451ffea0d1d7e4043823f59e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db5842c6e47959d7bccb81fd3096f4909d7bbbe6451ffea0d1d7e4043823f59e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db5842c6e47959d7bccb81fd3096f4909d7bbbe6451ffea0d1d7e4043823f59e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the clobber and options dispatch as a canonical multiline if/elif chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves inline asm as typed AsmBlock nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves volatile asm text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
