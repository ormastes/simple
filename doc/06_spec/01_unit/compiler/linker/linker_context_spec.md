# linker_context_spec

> Linker compilation context specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# linker_context_spec

Linker compilation context specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/linker_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Linker compilation context specification tests.

## Scenarios

### Linker Context

#### loads templates from the provided object map

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads templates from the provided object map
   - Expected: ctx.has_template("Array") is true
   - Expected: ctx.has_template("Vec") is false
   - Expected: loaded.is_ok() is true
   - Expected: loaded.unwrap().name equals `Array`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads templates from the provided object map")
var templates: Dict<text, GenericTemplate> = {}
templates["Array"] = GenericTemplate(name: "Array", type_params: ["T"], ast_data: nil)

val ctx = _ctx(templates)
expect(ctx.has_template("Array")).to_equal(true)
expect(ctx.has_template("Vec")).to_equal(false)

val loaded = ctx.load_template("Array")
expect(loaded.is_ok()).to_equal(true)
expect(loaded.unwrap().name).to_equal("Array")
```

</details>

#### reports linker-specific modes

- reports linker-specific modes
   - Expected: ctx.contract_mode() equals `ContractMode.All`
   - Expected: ctx.coverage_enabled() is false
   - Expected: ctx.instantiation_mode() equals `InstantiationMode.LinkTime`
   - Expected: ctx.recorded.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports linker-specific modes")
val ctx = _ctx({})
expect(ctx.contract_mode()).to_equal(ContractMode.All)
expect(ctx.coverage_enabled()).to_equal(false)
expect(ctx.instantiation_mode()).to_equal(InstantiationMode.LinkTime)
expect(ctx.recorded.len()).to_equal(0)
```

</details>

#### returns an error for missing templates

- returns an error for missing templates
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns an error for missing templates")
val ctx = _ctx({})
val result = ctx.load_template("Missing")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("Template not in objects")
```

</details>

#### records instantiation metadata entries

- records instantiation metadata entries
   - Expected: ctx.recorded.len() equals `1`
   - Expected: ctx.recorded[0].mangled_name equals `Vec$i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records instantiation metadata entries")
var ctx = _ctx({})
ctx.record_instantiation(InstantiationEntry(
    id: 0,
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "Vec$i64",
    from_file: "main.spl",
    from_loc: "1:1",
    to_obj: "main.smf",
    status: "completed"
))

expect(ctx.recorded.len()).to_equal(1)
expect(ctx.recorded[0].mangled_name).to_equal("Vec$i64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `70e0252ea5df7dc5aca5f991bee5e5babfd1cc5d7e475185dcb8317ec13b0ec4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70e0252ea5df7dc5aca5f991bee5e5babfd1cc5d7e475185dcb8317ec13b0ec4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70e0252ea5df7dc5aca5f991bee5e5babfd1cc5d7e475185dcb8317ec13b0ec4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/linker/linker_context_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/linker_context_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/linker_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/linker_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/linker_context_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/linker_context_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads templates from the provided object map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/linker_context_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports linker-specific modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/linker_context_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an error for missing templates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
