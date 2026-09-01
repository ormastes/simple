# Contract spec: test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl` and a green Results line.

## Scenarios

### native entry closure gate

#### collects every export-use dependency from the driver facade

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects every export-use dependency from the driver facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects every export-use dependency from the driver facade")
val source = file_read("src/compiler/driver/__init__.spl")
val imports = _driver_entry_import_module_paths(source)
expect(imports.len()).to_be_greater_than(10)
expect(imports).to_contain("compiler.driver.driver")
expect(imports).to_contain("compiler.driver.driver_aot_output")
```

</details>

#### skips lazy, commented, and docstring imports

- skips lazy, commented, and docstring imports
   - Expected: imports.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips lazy, commented, and docstring imports")
val imports = _driver_entry_import_module_paths(
    "use real.one\nuse lazy ignored.one\n# use ignored.two\n\"\"\"\nuse ignored.three\n\"\"\"\nuse ../../ignored_four\nimport real.two\n"
)
expect(imports.len()).to_equal(2)
expect(imports).to_contain("real.one")
expect(imports).to_contain("real.two")
```

</details>

#### imports the concrete driver owner instead of the ambiguous facade

- imports the concrete driver owner instead of the ambiguous facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports the concrete driver owner instead of the ambiguous facade")
val source = file_read("src/compiler/80.driver/main.spl")
expect(source).to_contain(
    "use compiler.driver.driver.{compiler_driver_create, compiler_driver_run_compile}"
)
expect(source).to_not_contain("use driver.*")        expect(source).to_not_contain("use compiler.driver.{")
```

</details>

#### reads parsed facade modules without optional value transport

- reads parsed facade modules without optional value transport


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads parsed facade modules without optional value transport")
val output = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
expect(output).to_contain(
    "if ctx.modules.has(name) and driver_native_module_is_export_facade(ctx.mir_modules[name], ctx.modules[name]):"
)
expect(output).to_not_contain("ctx.modules.get(name)")
```

</details>

#### gates entry closure on errors added by the closure walk

- gates entry closure on errors added by the closure walk


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gates entry closure on errors added by the closure walk")
val driver = file_read("src/compiler/80.driver/driver.spl")
val branch_start = driver.find("if nb_entry_env != \"\" and not nb_entry_closure_pre") ?? -1
val branch_end = driver.find("# Add core source roots only when compiling project sources") ?? -1
val closure = driver.substring(branch_start, branch_end)
val snapshot = closure.find("val closure_error_count_before = self.ctx.errors.len()") ?? -1
val walk = closure.find("while closure_idx < all_sources.len():") ?? -1
val unresolved = closure.find("self.ctx.add_error(\"unresolved import '") ?? -1
val empty = closure.find("self.ctx.add_error(\"import '") ?? -1
val success = closure.find("if self.ctx.errors.len() == closure_error_count_before:") ?? -1
val enable = closure.find("rt_env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", \"1\")") ?? -1

expect(branch_start).to_be_greater_than(-1)
expect(branch_end).to_be_greater_than(branch_start)
expect(snapshot).to_be_greater_than(-1)
expect(walk).to_be_greater_than(snapshot)
expect(unresolved).to_be_greater_than(walk)
expect(empty).to_be_greater_than(unresolved)
expect(success).to_be_greater_than(empty)
expect(enable).to_be_greater_than(success)
expect(closure).to_not_contain("if self.ctx.errors.len() == 0:")
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3d78a19a8d4440c0819895af85735b839462ac8fd05b13e76f94ac90da31a91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3d78a19a8d4440c0819895af85735b839462ac8fd05b13e76f94ac90da31a91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3d78a19a8d4440c0819895af85735b839462ac8fd05b13e76f94ac90da31a91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/native_entry_closure_gate_source_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects every export-use dependency from the driver facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips lazy, commented, and docstring imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports the concrete driver owner instead of the ambiguous facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
