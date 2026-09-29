# Cross-Module Trait Default-Method Dispatch — Native Codegen Regression

> fixed un-overridden trait *default* methods dispatching correctly on the native-build path when the trait and its impl are declared in the **same** module. That fix seeds `HirLowering.lowered_traits` (the registry `lower_impl`'s default-method injection reads) from the module's own `for trait_ in module.traits: self.lower_trait(trait_)` loop, which only walks the CURRENTLY-lowered module's own declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross-Module Trait Default-Method Dispatch — Native Codegen Regression

fixed un-overridden trait *default* methods dispatching correctly on the native-build path when the trait and its impl are declared in the **same** module. That fix seeds `HirLowering.lowered_traits` (the registry `lower_impl`'s default-method injection reads) from the module's own `for trait_ in module.traits: self.lower_trait(trait_)` loop, which only walks the CURRENTLY-lowered module's own declarations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #190 |
| Category | Compiler / HIR Lowering / Native Codegen |
| Status | Regression |
| Research | repo task #190 (lane S49); prior fix `doc/09_report` / commit |
| Source | `test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

#157 (`fix(native): resolve trait default-method dispatch on native path`)
fixed un-overridden trait *default* methods dispatching correctly on the
native-build path when the trait and its impl are declared in the **same**
module. That fix seeds `HirLowering.lowered_traits` (the registry
`lower_impl`'s default-method injection reads) from the module's own
`for trait_ in module.traits: self.lower_trait(trait_)` loop, which only
walks the CURRENTLY-lowered module's own declarations.

When the trait lives in an **imported** module and the impl is in a
different (e.g. the entry) module, `register_imported_symbol`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`, the
`elif as_trait != nil:` arm) only defined a placeholder `Trait` symbol — it
never lowered the imported trait into `lowered_traits`. `lower_impl`'s
injection then found nothing to inject for a cross-module trait, so calling
an un-overridden default died at MIR time with `unresolved method call`
(interpreter mode was unaffected: it resolves defaults dynamically, not via
this HIR-time table).

Fix: `register_imported_symbol`'s trait arm now lowers the imported trait
on demand (guarded by `lowered_traits.contains_key`, so a repeated/glob
use std.spec.step

import does not re-lower it) the moment a named-item `use` import of the
trait resolves it, before this module's own impls are lowered (import resolution
already runs before impl lowering, task #55). Deliberately NOT an eager
import-graph walk over every imported module's traits — only traits actually
named in a `use` get lowered here.

This spec probes the case #157's own smoke coverage (case `trait_default`,
`scripts/check/native-smoke-matrix.shs`) cannot: the harness writes one
single-file probe per case, so a genuinely cross-module (two-file) scenario
needs its own harness. Both files are written fresh at spec run and compiled
with the default self-hosted toolchain (not `--source src/...` bulk compile),
mirroring how a real user's multi-file project builds via `native-build
--entry`.

## Research

**Research:** repo task #190 (lane S49); prior fix `doc/09_report` / commit
`06ee58b010e` (#157, same-module).

## Syntax

```sh
bin/simple test test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl
```

## Scenarios

### cross-module trait default-method dispatch (#190)

#### writes the two-file cross-module trait probe

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes the two-file cross-module trait probe
   - Expected: mkdir_code equals `0`
   - Expected: mkdir_out equals ``
   - Expected: trait_write_code equals `0`
   - Expected: trait_write_out equals ``
   - Expected: entry_write_code equals `0`
   - Expected: entry_write_out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes the two-file cross-module trait probe")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_code).to_equal(0)
expect(mkdir_out).to_equal("")

val (trait_write_out, trait_write_code) = shell("cat > " + TRAIT_SOURCE_PATH + " <<'EOF'\n" + trait_module_source() + "EOF")
expect(trait_write_code).to_equal(0)
expect(trait_write_out).to_equal("")

val (entry_write_out, entry_write_code) = shell("cat > " + ENTRY_SOURCE_PATH + " <<'EOF'\n" + entry_module_source() + "EOF")
expect(entry_write_code).to_equal(0)
expect(entry_write_out).to_equal("")
```

</details>

#### interpreter oracle: un-overridden cross-module default dispatches to 42

- interpreter oracle: un-overridden cross-module default dispatches to 42
- bin/simple run must reach the default body via dynamic dispatch
   - Expected: run_code equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpreter oracle: un-overridden cross-module default dispatches to 42")
step("bin/simple run must reach the default body via dynamic dispatch")
val (run_out, run_code) = shell("env -u SIMPLE_BOOTSTRAP bin/simple run " + ENTRY_SOURCE_PATH)
expect(run_code).to_equal(42)
```

</details>

#### native-build: un-overridden cross-module default must dispatch to 42, not fail loudly

- native-build: un-overridden cross-module default must dispatch to 42, not fail loudly
- Native compile of the two-file probe must succeed (regressed: 'MIR lowering error: unresolved method call: greet')
   - Expected: compile_out does not contain `unresolved method call`
   - Expected: compile_code equals `0`
- The standalone native binary exits 42 (matches the interpreter oracle)
   - Expected: native_code equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native-build: un-overridden cross-module default must dispatch to 42, not fail loudly")
step("Native compile of the two-file probe must succeed (regressed: 'MIR lowering error: unresolved method call: greet')")
val (compile_out, compile_code) = shell("env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build --entry " + ENTRY_SOURCE_PATH + " -o " + NATIVE_PATH + " --clean")
expect(compile_out.contains("unresolved method call")).to_equal(false)
expect(compile_code).to_equal(0)

step("The standalone native binary exits 42 (matches the interpreter oracle)")
val (native_out, native_code) = shell(NATIVE_PATH)
expect(native_code).to_equal(42)
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


## Related Documentation

- **Research:** `repo task #190 (lane S49); prior fix `doc/09_report` / commit`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37808e67040d845242081717cc155b7eef27421cfb9370023292b14c1b86538b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37808e67040d845242081717cc155b7eef27421cfb9370023292b14c1b86538b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37808e67040d845242081717cc155b7eef27421cfb9370023292b14c1b86538b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl
mirror: doc/06_spec/03_system/compiler/trait_default_cross_module_codegen_regression_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/03_system/compiler/trait_default_cross_module_codegen_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/trait_default_cross_module_codegen_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
