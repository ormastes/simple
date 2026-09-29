# HIR marks unmonomorphized generic declarations as templates (#158 Phase B, HIR half)

> The parse -> HIR pipeline is inlined in each `it` block on purpose, mirroring

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR marks unmonomorphized generic declarations as templates (#158 Phase B, HIR half)

The parse -> HIR pipeline is inlined in each `it` block on purpose, mirroring

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/generic_template_marking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Harness landmine
The parse -> HIR pipeline is inlined in each `it` block on purpose, mirroring
`test/01_unit/compiler/borrow/iso_parse_pipeline_spec.spl`: running the
identical code inside a module-level helper fn loses recorded lowering state
when read back afterward.

## Scenarios

### HIR generic template marking (#158 Phase B, HIR half)

#### marks a generic struct as a template and still reports the Phase A gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- marks a generic struct as a template and still reports the Phase A gate
   - Expected: marked equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks a generic struct as a template and still reports the Phase A gate")
val src = "struct Box<T>:\n" +
    "    v: T\n"
val parsed = parse_full_frontend(src, "testdata/fixture_generic_struct.spl", "fixture_generic_struct", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/fixture_generic_struct.spl")
val hir = hir_lowering.lower_module(parsed)
var marked = 0
var total = 0
for key in hir.structs.keys():
    val s = hir.structs[key]
    if s.name == "Box":
        total = total + 1
        if s.is_generic_template:
            marked = marked + 1
expect(total).to_be_greater_than(0)
expect(marked).to_equal(total)
# Phase A must still be loud: marking is not monomorphizing.
var gated = 0
for msg in hir_lowering.diagnostic_messages:
    if msg.contains("generic structs are not supported"):
        gated = gated + 1
expect(gated).to_be_greater_than(0)
```

</details>

#### marks a generic class as a template and still reports the Phase A gate

- marks a generic class as a template and still reports the Phase A gate
   - Expected: marked equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks a generic class as a template and still reports the Phase A gate")
val src = "class Holder<T>:\n" +
    "    v: T\n"
val parsed = parse_full_frontend(src, "testdata/fixture_generic_class.spl", "fixture_generic_class", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/fixture_generic_class.spl")
val hir = hir_lowering.lower_module(parsed)
var marked = 0
var total = 0
for key in hir.classes.keys():
    val c = hir.classes[key]
    if c.name == "Holder":
        total = total + 1
        if c.is_generic_template:
            marked = marked + 1
expect(total).to_be_greater_than(0)
expect(marked).to_equal(total)
var gated = 0
for msg in hir_lowering.diagnostic_messages:
    if msg.contains("generic classes are not supported"):
        gated = gated + 1
expect(gated).to_be_greater_than(0)
```

</details>

#### marks a generic free fn as a template (HirFunction tier)

- marks a generic free fn as a template (HirFunction tier)
   - Expected: marked equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks a generic free fn as a template (HirFunction tier)")
val src = "fn ident<T>(v: T) -> T:\n" +
    "    v\n"
val parsed = parse_full_frontend(src, "testdata/fixture_generic_fn.spl", "fixture_generic_fn", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/fixture_generic_fn.spl")
val hir = hir_lowering.lower_module(parsed)
var marked = 0
var total = 0
for key in hir.functions.keys():
    val f = hir.functions[key]
    if f.name == "ident":
        total = total + 1
        if f.is_generic_template:
            marked = marked + 1
expect(total).to_be_greater_than(0)
expect(marked).to_equal(total)
```

</details>

#### does NOT mark a concrete free fn as a template

- does NOT mark a concrete free fn as a template
   - Expected: marked equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does NOT mark a concrete free fn as a template")
val src = "fn twice(v: i64) -> i64:\n" +
    "    v + v\n"
val parsed = parse_full_frontend(src, "testdata/fixture_concrete_fn.spl", "fixture_concrete_fn", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/fixture_concrete_fn.spl")
val hir = hir_lowering.lower_module(parsed)
var marked = 0
var total = 0
for key in hir.functions.keys():
    val f = hir.functions[key]
    if f.name == "twice":
        total = total + 1
        if f.is_generic_template:
            marked = marked + 1
expect(total).to_be_greater_than(0)
expect(marked).to_equal(0)
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

- Canonical SPipe generation for source `01f75956cc9cee12178651acf10f8d6687146cea3bf0aeb6d3a2bb22466d6ca2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01f75956cc9cee12178651acf10f8d6687146cea3bf0aeb6d3a2bb22466d6ca2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01f75956cc9cee12178651acf10f8d6687146cea3bf0aeb6d3a2bb22466d6ca2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/generic_template_marking_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/generic_template_marking_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/generic_template_marking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/generic_template_marking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/generic_template_marking_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/generic_template_marking_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks a generic struct as a template and still reports the Phase A gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/generic_template_marking_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks a generic class as a template and still reports the Phase A gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/generic_template_marking_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks a generic free fn as a template (HirFunction tier)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
