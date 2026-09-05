# `use lazy M.{sym}` named-import entry-closure contract

> Purpose: Prove that use lazy named-import entry closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `use lazy M.{sym}` named-import entry-closure contract

Purpose: Prove that use lazy named-import entry closure.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that use lazy named-import entry closure.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### use lazy named-import entry closure

#### collects the module of a named lazy import

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects the module of a named lazy import
- Verify: collects the module of a named lazy import
   - Expected: imports.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects the module of a named lazy import")
step("Verify: collects the module of a named lazy import")
# @req: REQ-COMPILER-DRIVER-001
val imports = _driver_entry_import_module_paths(
    "use lazy zqx.named." + LB + "Zqxsym" + RB + "\n")
expect(imports.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(imports).to_contain("zqx.named")
```

</details>

#### collects the module of a paren-form named lazy import

- collects the module of a paren-form named lazy import
- Verify: collects the module of a paren-form named lazy import
   - Expected: imports.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects the module of a paren-form named lazy import")
step("Verify: collects the module of a paren-form named lazy import")
val imports = _driver_entry_import_module_paths("use lazy zqx.parend (Zqxsym)\n")
expect(imports.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(imports).to_contain("zqx.parend")
```

</details>

#### collects the module of an aliased named lazy import

- collects the module of an aliased named lazy import
- Verify: collects the module of an aliased named lazy import
   - Expected: imports.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects the module of an aliased named lazy import")
step("Verify: collects the module of an aliased named lazy import")
val imports = _driver_entry_import_module_paths(
    "use lazy zqx.aliasing." + LB + "Zqxsym as Zqxalias" + RB + "\n")
expect(imports.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(imports).to_contain("zqx.aliasing")
```

</details>

#### keeps name-less lazy imports deferred

- keeps name-less lazy imports deferred
- Verify: keeps name-less lazy imports deferred
   - Expected: _driver_entry_import_module_paths("use lazy zqx.bare\n").len() equals `0`
   - Expected: _driver_entry_import_module_paths("use lazy zqx.globby.*\n").len() equals `0`
   - Expected: _driver_entry_import_module_paths("use lazy zqx.mod as zq\n").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps name-less lazy imports deferred")
step("Verify: keeps name-less lazy imports deferred")
expect(_driver_entry_import_module_paths("use lazy zqx.bare\n").len()).to_equal(0)
expect(_driver_entry_import_module_paths("use lazy zqx.globby.*\n").len()).to_equal(0)
expect(_driver_entry_import_module_paths("use lazy zqx.mod as zq\n").len()).to_equal(0)
```

</details>

#### resolves the real module for export-use, pub-use and import lazy forms

- resolves the real module for export-use, pub-use and import lazy forms
- Verify: resolves the real module for export-use, pub-use and import lazy forms
   - Expected: exported does not contain `lazy`
   - Expected: published does not contain `lazy`
   - Expected: imported does not contain `lazy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the real module for export-use, pub-use and import lazy forms")
step("Verify: resolves the real module for export-use, pub-use and import lazy forms")
val exported = _driver_entry_import_module_paths(
    "export use lazy zqx.exp." + LB + "Zqxsym" + RB + "\n")
expect(exported).to_contain("zqx.exp")
expect(exported.contains("lazy")).to_equal(false)
val published = _driver_entry_import_module_paths(
    "pub use lazy zqx.pubm." + LB + "Zqxsym" + RB + "\n")
expect(published).to_contain("zqx.pubm")
expect(published.contains("lazy")).to_equal(false)
val imported = _driver_entry_import_module_paths(
    "import lazy zqx.impm." + LB + "Zqxsym" + RB + "\n")
expect(imported).to_contain("zqx.impm")
expect(imported.contains("lazy")).to_equal(false)
```

</details>

#### does not mistake a module whose first segment starts with lazy

- does not mistake a module whose first segment starts with lazy
- Verify: does not mistake a module whose first segment starts with lazy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not mistake a module whose first segment starts with lazy")
step("Verify: does not mistake a module whose first segment starts with lazy")
val imports = _driver_entry_import_module_paths(
    "use lazy_thing.mod." + LB + "Zqxsym" + RB + "\n")
expect(imports).to_contain("lazy_thing.mod")
```

</details>

### in-tree lazy import sites

#### puts the driver's lazy interpreter backend in its entry closure

- puts the driver's lazy interpreter backend in its entry closure
- Verify: puts the driver's lazy interpreter backend in its entry closure
   - Expected: driver does not contain `lazy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("puts the driver's lazy interpreter backend in its entry closure")
step("Verify: puts the driver's lazy interpreter backend in its entry closure")
val driver = _driver_entry_import_module_paths(
    file_read("src/compiler/80.driver/driver.spl"))
expect(driver).to_contain("compiler.backend.backend.interpreter")
expect(driver).to_contain("compiler.backend.backend_types")
expect(driver.contains("lazy")).to_equal(false)
```

</details>

#### puts driver_types' lazy interpreter backend in its entry closure

- puts driver_types' lazy interpreter backend in its entry closure
- Verify: puts driver_types' lazy interpreter backend in its entry closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("puts driver_types' lazy interpreter backend in its entry closure")
step("Verify: puts driver_types' lazy interpreter backend in its entry closure")
val types = _driver_entry_import_module_paths(
    file_read("src/compiler/80.driver/driver_types.spl"))
expect(types).to_contain("compiler.backend.backend.interpreter")
```

</details>

#### keeps the MCP lazy tool modules out of the entry closure

- keeps the MCP lazy tool modules out of the entry closure
- Verify: keeps the MCP lazy tool modules out of the entry closure
   - Expected: mcp does not contain `std.nogc_async_mut.mcp.main_lazy_diag_tools`
   - Expected: mcp does not contain `std.nogc_async_mut.mcp.main_lazy_debug_tools`
   - Expected: mcp does not contain `std.nogc_async_mut.mcp.main_lazy_power_tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the MCP lazy tool modules out of the entry closure")
step("Verify: keeps the MCP lazy tool modules out of the entry closure")
val mcp = _driver_entry_import_module_paths(
    file_read("src/lib/nogc_async_mut/mcp/main_lazy.spl"))
expect(mcp.contains("std.nogc_async_mut.mcp.main_lazy_diag_tools")).to_equal(false)
expect(mcp.contains("std.nogc_async_mut.mcp.main_lazy_debug_tools")).to_equal(false)
expect(mcp.contains("std.nogc_async_mut.mcp.main_lazy_power_tools")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-DRIVER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `abe91989030f33aa8c441a558fdb18f6bfa8dcc48aa9f35602bcf1fc8dda049c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abe91989030f33aa8c441a558fdb18f6bfa8dcc48aa9f35602bcf1fc8dda049c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abe91989030f33aa8c441a558fdb18f6bfa8dcc48aa9f35602bcf1fc8dda049c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/lazy_named_import_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/lazy_named_import_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/lazy_named_import_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects the module of a named lazy import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects the module of a paren-form named lazy import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects the module of an aliased named lazy import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
