# LLVM Backend Type Safety Lint Coverage

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend Type Safety Lint Coverage

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### LLVM backend type safety lint

#### flags raw return type metadata used for emitted result type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags raw return type metadata used for emitted result type
   - Expected: lint_has_code(source, "LLVM001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags raw return type metadata used for emitted result type")
val source = "fn emit(dest_id: i64):\n    val ret_ty = self.get_local_type(dest_id)\n"
expect(lint_has_code(source, "LLVM001")).to_equal(true)
```

</details>

#### flags raw phi type metadata used for emitted result type

- flags raw phi type metadata used for emitted result type
   - Expected: lint_has_code(source, "LLVM001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags raw phi type metadata used for emitted result type")
val source = "fn emit(dest_id: i64):\n    val phi_ty = self.get_local_type(dest_id)\n"
expect(lint_has_code(source, "LLVM001")).to_equal(true)
```

</details>

#### allows guarded result type metadata

- allows guarded result type metadata
   - Expected: lint_has_code(source, "LLVM001") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows guarded result type metadata")
val source = "fn emit(dest_id: i64):\n    val ret_ty = self.valid_llvm_type(self.get_local_type(dest_id))\n"
expect(lint_has_code(source, "LLVM001")).to_equal(false)
```

</details>

#### flags raw signature return type mapping

- flags raw signature return type mapping
   - Expected: lint_has_code(source, "LLVM001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags raw signature return type mapping")
val source = "fn emit(sig: MirSignature):\n    val ret_ty = self.llvm_type_text(sig.return_type)\n"
expect(lint_has_code(source, "LLVM001")).to_equal(true)
```

</details>

#### allows guarded signature return type mapping

- allows guarded signature return type mapping
   - Expected: lint_has_code(source, "LLVM001") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows guarded signature return type mapping")
val source = "fn emit(sig: MirSignature):\n    val ret_ty = if sig.return_type == nil: \"void\" else: self.valid_llvm_type(self.llvm_type_text(sig.return_type))\n"
expect(lint_has_code(source, "LLVM001")).to_equal(false)
```

</details>

#### flags raw llvm-lib signature return type mapping

- flags raw llvm-lib signature return type mapping
   - Expected: lint_has_code_at("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl", source, "LLVM001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags raw llvm-lib signature return type mapping")
val source = "fn emit(sig: MirSignature):\n    val ret_ty = tm.map_type(sig.return_type)\n"
expect(lint_has_code_at("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl", source, "LLVM001")).to_equal(true)
```

</details>

#### allows llvm-lib nil-to-void signature return mapping

- allows llvm-lib nil-to-void signature return mapping
   - Expected: lint_has_code_at("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl", source, "LLVM001") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows llvm-lib nil-to-void signature return mapping")
val source = "fn emit(sig: MirSignature):\n    val ret_ty = if sig.return_type == nil: llvm_void_type_in_context(ctx) else: tm.map_type(sig.return_type)\n"
expect(lint_has_code_at("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl", source, "LLVM001")).to_equal(false)
```

</details>

#### flags raw bootstrap function return type metadata

- flags raw bootstrap function return type metadata
   - Expected: lint_has_code_at("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl", source, "LLVM001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags raw bootstrap function return type metadata")
val source = "case Function(_, ret):\n    match value:\n        case Str(name):\n            if ret != nil:\n                self.remember_function_return_type(name, self.llvm_type_text(ret))\n"
expect(lint_has_code_at("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl", source, "LLVM001")).to_equal(true)
```

</details>

#### flags raw bootstrap signature return type metadata

- flags raw bootstrap signature return type metadata
   - Expected: lint_has_code_at("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl", source, "LLVM001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags raw bootstrap signature return type metadata")
val source = "case FuncPtr(signature):\n    match value:\n        case Str(name):\n            if signature.return_type != nil:\n                self.remember_function_return_type(name, self.llvm_type_text(signature.return_type))\n"
expect(lint_has_code_at("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl", source, "LLVM001")).to_equal(true)
```

</details>

#### does not flag non-LLVM backend files

- does not flag non-LLVM backend files
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag non-LLVM backend files")
var linter = Linter.new()
val results = linter.lint_source("src/compiler/70.backend/backend/_CBackendTranslate/sample.spl", "fn emit(dest_id: i64):\n    val ret_ty = self.get_local_type(dest_id)\n")
expect(results.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `9a321d03a5832b4a46d73e570c241b590215d6116a18f93a75419896b5641203`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a321d03a5832b4a46d73e570c241b590215d6116a18f93a75419896b5641203`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a321d03a5832b4a46d73e570c241b590215d6116a18f93a75419896b5641203`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/llvm_backend_type_safety_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/llvm_backend_type_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/llvm_backend_type_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags raw return type metadata used for emitted result type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags raw phi type metadata used for emitted result type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows guarded result type metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
