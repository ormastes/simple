# Module Surface Glob Export Origin Unit Spec

> Verifies that a facade's explicit glob import routes plain exports through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Surface Glob Export Origin Unit Spec

Verifies that a facade's explicit glob import routes plain exports through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that a facade's explicit glob import routes plain exports through the
glob owner before same-package sibling inference.

## Scenarios

### module surface explicit glob export origins

<details>
<summary>Advanced: keeps loop-carried route selection scalar for native Stage 3</summary>

#### keeps loop-carried route selection scalar for native Stage 3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps loop-carried route selection scalar for native Stage 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps loop-carried route selection scalar for native Stage 3")
val source = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/module_surface_export_index.spl") ?? ""

expect(source).to_contain("var selected_owner_module = \"\"")
expect(source).to_contain("var candidate_owner_module = \"\"")
expect(source).to_not_contain("var selected = ModuleSurfaceExportOrigin(")
expect(source).to_not_contain("var candidate = ModuleSurfaceExportOrigin(")
```

</details>


</details>

#### routes the exact Stage 4 parser_expr export through parser_primary

- routes the exact Stage 4 parser_expr export through parser_primary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes the exact Stage 4 parser_expr export through parser_primary")
expect_exact_glob_chain(false)
```

</details>

#### routes the same delayed glob chain in reverse discovery order

- routes the same delayed glob chain in reverse discovery order


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes the same delayed glob chain in reverse discovery order")
expect_exact_glob_chain(true)
```

</details>

#### fails closed when two explicit globs expose distinct terminals

- fails closed when two explicit globs expose distinct terminals


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when two explicit globs expose distinct terminals")
val log = glob_origin_logger()
val first_source = "pub fn shared_value() -> i64:\n    1"
val second_source = "pub fn shared_value() -> i64:\n    2"
val facade_source = "use glob.first.*\nuse glob.second.*\nexport shared_value"
var modules: Dict<text, Module> = {}
modules["glob.first"] = parse_full_frontend(
    first_source, "glob.first", "glob.first", log)
modules["glob.second"] = parse_full_frontend(
    second_source, "glob.second", "glob.second", log)
modules["glob.facade"] = parse_full_frontend(
    facade_source, "glob.facade", "glob.facade", log)
val result = module_surfaces_from_modules(modules, [
    SourceFile(path: "glob/facade.spl", content: facade_source, module_name: "glob.facade"),
    SourceFile(path: "glob/second.spl", content: second_source, module_name: "glob.second"),
    SourceFile(path: "glob/first.spl", content: first_source, module_name: "glob.first")
])
expect(result.is_err()).to_be(true)
if result.is_err():
    expect(result.unwrap_err()).to_contain("ambiguous explicit facade export")
```

</details>

#### keeps a missing named import owner as an unresolved export

- keeps a missing named import owner as an unresolved export


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a missing named import owner as an unresolved export")
val log = glob_origin_logger()
val facade_source = "use missing.owner.{missing_value}\nexport missing_value"
var modules: Dict<text, Module> = {}
modules["missing.facade"] = parse_full_frontend(
    facade_source, "missing.facade", "missing.facade", log)
val result = module_surfaces_from_modules(modules, [
    SourceFile(
        path: "missing/facade.spl", content: facade_source,
        module_name: "missing.facade")
])
expect(result.is_ok()).to_be(true)
if result.is_ok():
    val surfaces = result.unwrap()
    val facade = surfaces.surfaces[surfaces.index_by_name["missing.facade"]]
    expect(facade.export_origins.contains_key("missing_value")).to_be(false)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c98ea2b2f5d47cbf1fab74e1fc563db6132ea36200f9001bb13fd9bc9a18eb00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c98ea2b2f5d47cbf1fab74e1fc563db6132ea36200f9001bb13fd9bc9a18eb00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c98ea2b2f5d47cbf1fab74e1fc563db6132ea36200f9001bb13fd9bc9a18eb00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_surface_glob_export_origin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/module_surface_glob_export_origin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_surface_glob_export_origin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps loop-carried route selection scalar for native Stage 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes the exact Stage 4 parser_expr export through parser_primary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes the same delayed glob chain in reverse discovery order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
