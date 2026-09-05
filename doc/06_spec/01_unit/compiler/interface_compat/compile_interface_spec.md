# CompileInterfaceDigest / ModuleIdentity Specification

> Acceptance properties for the first-slice interface extractor: body-only / comment-only / private-decl changes keep the compile_interface_digest stable; public signature changes and the implementation digest move; declaration insertion order never matters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CompileInterfaceDigest / ModuleIdentity Specification

Acceptance properties for the first-slice interface extractor: body-only / comment-only / private-decl changes keep the compile_interface_digest stable; public signature changes and the implementation digest move; declaration insertion order never matters.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Plan | doc/03_plan/compiler/build/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md (§7, §20) |
| Source | `test/01_unit/compiler/interface_compat/compile_interface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Acceptance properties for the first-slice interface extractor:
body-only / comment-only / private-decl changes keep the
compile_interface_digest stable; public signature changes and the
implementation digest move; declaration insertion order never matters.

Limitation (stated per plan): digests are computed over ApiSurface
structures directly, not by driving the full parse+semantic pipeline
from this unit spec.

## Scenarios

### compile_interface_digest acceptance properties

#### body-only change: same interface digest, different implementation digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- body-only change: same interface digest, different implementation digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("body-only change: same interface digest, different implementation digest")
val id1 = compute_module_identity(surface_a(), source_a)
val id2 = compute_module_identity(surface_a(), source_a_body_changed)
expect id1.compile_interface_digest == id2.compile_interface_digest
expect id1.implementation_digest != id2.implementation_digest
expect id1.source_digest != id2.source_digest
```

</details>

#### comment/formatting-only change: same interface AND implementation digest

- comment/formatting-only change: same interface AND implementation digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("comment/formatting-only change: same interface AND implementation digest")
val id1 = compute_module_identity(surface_a(), source_a)
val id2 = compute_module_identity(surface_a(), source_a_commented)
expect id1.compile_interface_digest == id2.compile_interface_digest
expect id1.implementation_digest == id2.implementation_digest
expect id1.source_digest != id2.source_digest
```

</details>

#### private declaration added: same interface digest

- private declaration added: same interface digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("private declaration added: same interface digest")
var with_private = surface_a()
with_private.add_function(fn_sig("helper", "i64", "i64", Some("private")))
expect compile_interface_digest(surface_a()) == compile_interface_digest(with_private)
```

</details>

#### public function signature change: different interface digest

- public function signature change: different interface digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("public function signature change: different interface digest")
var changed = ApiSurface.create("fixture.mod_a")
changed.add_function(fn_sig("alpha", "text", "i64", nil))  # param i64 -> text
changed.add_function(fn_sig("beta", "text", "bool", nil))
expect compile_interface_digest(surface_a()) != compile_interface_digest(changed)
```

</details>

#### public function return type change: different interface digest

- public function return type change: different interface digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("public function return type change: different interface digest")
var changed = ApiSurface.create("fixture.mod_a")
changed.add_function(fn_sig("alpha", "i64", "bool", nil))  # ret i64 -> bool
changed.add_function(fn_sig("beta", "text", "bool", nil))
expect compile_interface_digest(surface_a()) != compile_interface_digest(changed)
```

</details>

#### declaration iteration order does not change the digest

- declaration iteration order does not change the digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declaration iteration order does not change the digest")
var reversed = ApiSurface.create("fixture.mod_a")
reversed.add_function(fn_sig("beta", "text", "bool", nil))
reversed.add_function(fn_sig("alpha", "i64", "i64", nil))
expect compile_interface_digest(surface_a()) == compile_interface_digest(reversed)
```

</details>

#### hash inside a string literal is not treated as a comment start (no false collision)

- hash inside a string literal is not treated as a comment start (no false collision)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("hash inside a string literal is not treated as a comment start (no false collision)")
val id1 = compute_module_identity(surface_a(), source_a_hash_in_literal_1)
val id2 = compute_module_identity(surface_a(), source_a_hash_in_literal_2)
expect id1.compile_interface_digest == id2.compile_interface_digest
expect id1.implementation_digest != id2.implementation_digest
expect id1.source_digest != id2.source_digest
```

</details>

#### placeholder abi/semantic digests are domain-separated from compile digest

- placeholder abi/semantic digests are domain-separated from compile digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("placeholder abi/semantic digests are domain-separated from compile digest")
val id = compute_module_identity(surface_a(), source_a)
expect id.abi_interface_digest != id.compile_interface_digest
expect id.compile_semantic_digest != id.compile_interface_digest
expect id.link_export_digest != id.compile_interface_digest
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/compiler/build/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md (§7, §20)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7299bc9b5189671b58e6d16a9ab014811bc0f1ba199e6b3aebea8be16206e16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7299bc9b5189671b58e6d16a9ab014811bc0f1ba199e6b3aebea8be16206e16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7299bc9b5189671b58e6d16a9ab014811bc0f1ba199e6b3aebea8be16206e16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interface_compat/compile_interface_spec.spl
mirror: doc/06_spec/01_unit/compiler/interface_compat/compile_interface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interface_compat/compile_interface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interface_compat/compile_interface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interface_compat/compile_interface_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'body-only change: same interface digest, different implementation digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interface_compat/compile_interface_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'comment/formatting-only change: same interface AND implementation digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interface_compat/compile_interface_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'private declaration added: same interface digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
