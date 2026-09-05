# Mir Target Context Wiring Source Specification

> Tests covering MIR target context wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Target Context Wiring Source Specification

## Scenarios

### MIR target context wiring

#### keeps target state immutable below the driver boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps target state immutable below the driver boundary
   - Expected: asm_targets does not contain `"x86_64"\n\n    me get_target_os`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps target state immutable below the driver boundary")
val types = file_read("src/compiler/50.mir/mir_lowering_types.spl")
val lowering = file_read("src/compiler/50.mir/_MirLowering/module_lowering.spl")
val asm_targets = file_read("src/compiler/50.mir/_MirLowering/asm_and_targets.spl")

expect(types).to_contain("target_context: MirTargetContext")
expect(lowering).to_contain("static fn new_for_target(symbols: SymbolTable, target_context: MirTargetContext)")
expect(asm_targets).to_contain("self.target_context.arch")
expect(asm_targets).to_contain("self.target_context.os")
expect(asm_targets).to_contain("self.target_context.abi")
expect(asm_targets).to_contain("self.target_context.backend")
expect(asm_targets).to_contain("self.target_context.version")
expect(asm_targets.contains("\"x86_64\"\n\n    me get_target_os")).to_equal(false)
```

</details>

#### threads one context through normal, bootstrap, and nested lowerers

- threads one context through normal, bootstrap, and nested lowerers


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("threads one context through normal, bootstrap, and nested lowerers")
val pipeline = file_read(
    "src/compiler/80.driver/driver_pipeline_lowering.spl")
val bootstrap = file_read("src/compiler/80.driver/driver_bootstrap.spl")
val nested = file_read("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(pipeline).to_contain("val target_context = driver_mir_target_context(self.ctx.options)")
expect(pipeline).to_contain("MirLowering.new_for_target(bootstrap_hir.symbols, target_context)")
expect(pipeline).to_contain("MirLowering.new_for_target(SymbolTable.new(), target_context)")
expect(bootstrap).to_contain("bootstrap_lower_hir_globals_to_mir_module_for_target(target_context)")
expect(bootstrap).to_contain("bootstrap_lower_extra_hir_module_to_mir_for_target(extra_hir, target_context)")
expect(nested).to_contain("MirLowering.new_for_target(self.symbols, self.target_context)")
```

</details>

#### keeps LLVM default and Cranelift explicit

- keeps LLVM default and Cranelift explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps LLVM default and Cranelift explicit")
val backend = file_read("src/compiler/70.backend/backend/backend_helpers.spl")
val target = file_read("src/compiler/80.driver/driver_mir_target.spl")
val provider = file_read("src/compiler/70.backend/backend/mir_target_context_provider.spl")

expect(backend).to_contain("elif backend_name == \"auto\" or backend_name == \"\"")
expect(backend).to_contain("elif backend_name == \"cranelift\"")
expect(target).to_contain("backend_mir_target_context(effective_backend)")
expect(provider).to_contain("capabilities.llc.version.major")
expect(provider).to_contain("capabilities.libllvm.version.major")
expect(provider).to_contain("val known_version = if version > 0: version else: -1")
```

</details>

#### routes backend, JIT, C, and seed-core lowerers through real boundary contexts

- routes backend, JIT, C, and seed-core lowerers through real boundary contexts
   - Expected: compiler_backend does not contain `MirLowering.new(module.symbols)`
   - Expected: jit does not contain `MirLowering.new(module.symbols)`
   - Expected: c_entry does not contain `MirLowering.new(sym_table)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes backend, JIT, C, and seed-core lowerers through real boundary contexts")
val compiler_backend = file_read("src/compiler/70.backend/backend/compiler.spl")
val jit = file_read("src/compiler/70.backend/backend/jit_interpreter.spl")
val c_entry = file_read("src/compiler/70.backend/backend/compile_c_entry.spl")
val core = file_read("src/compiler/10.frontend/core/mir/lowering.spl")

expect(compiler_backend).to_contain("MirLowering.new_for_target(module.symbols, target_context)")
expect(jit).to_contain("MirLowering.new_for_target(module.symbols, target_context)")
expect(c_entry).to_contain("MirLowering.new_for_target(sym_table, target_context)")
expect(core).to_contain("bootstrap_lower_hir_globals_to_mir_module_for_target(target_context)")
expect(compiler_backend.contains("MirLowering.new(module.symbols)")).to_equal(false)
expect(jit.contains("MirLowering.new(module.symbols)")).to_equal(false)
expect(c_entry.contains("MirLowering.new(sym_table)")).to_equal(false)
```

</details>

#### fails closed when a selected backend version is unavailable

- fails closed when a selected backend version is unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a selected backend version is unavailable")
val asm_targets = file_read("src/compiler/50.mir/_MirLowering/asm_and_targets.spl")

expect(asm_targets).to_contain("if ver_ops.len() > 0 and target_backend_version < 0")
expect(asm_targets).to_contain("return \"unknown_version\"")
expect(asm_targets).to_contain("cannot evaluate asm target backend version")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_target_context_wiring_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR target context wiring.
- MIR target context wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `b34f8d8d8ecfb0b3166bde8795ecab403ed6f31c0422dfc8d4c3d1cba567d41b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b34f8d8d8ecfb0b3166bde8795ecab403ed6f31c0422dfc8d4c3d1cba567d41b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b34f8d8d8ecfb0b3166bde8795ecab403ed6f31c0422dfc8d4c3d1cba567d41b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/mir_target_context_wiring_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_target_context_wiring_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_target_context_wiring_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_target_context_wiring_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_target_context_wiring_source_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps target state immutable below the driver boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_target_context_wiring_source_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'threads one context through normal, bootstrap, and nested lowerers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_target_context_wiring_source_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps LLVM default and Cranelift explicit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
