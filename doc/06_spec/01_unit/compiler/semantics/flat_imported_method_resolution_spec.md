# flat_imported_method_resolution_spec

> Flat entry-closure method resolution preserves canonical imported owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# flat_imported_method_resolution_spec

Flat entry-closure method resolution preserves canonical imported owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/flat_imported_method_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Flat entry-closure method resolution preserves canonical imported owners.

## Scenarios

### flat imported method resolution

#### keeps owner identity across parameters constructors factories traits and aliases

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps owner identity across parameters constructors factories traits and aliases
   - Expected: lowering.errors.len() equals `0`
   - Expected: errors.len() equals `0`
   - Expected: fimr_resolution_name(hir.symbols, functions, "param_a") equals `owner_a.Shared::cleanup`
   - Expected: fimr_resolution_name(hir.symbols, functions, "param_b") equals `owner_b.Shared::cleanup`
   - Expected: fimr_resolution_name(hir.symbols, functions, "static_a") equals `owner_a.Shared::open`
   - Expected: fimr_resolution_name(hir.symbols, functions, "static_b") equals `owner_b.Shared::open`
   - Expected: fimr_resolution_name(hir.symbols, functions, "constructor_a") equals `owner_a.Shared::cleanup`
   - Expected: fimr_resolution_name(hir.symbols, functions, "factory_a") equals `owner_a.Shared::cleanup`
   - Expected: fimr_resolution_name(hir.symbols, functions, "factory_b") equals `owner_b.Shared::cleanup`
   - Expected: fimr_resolution_name(hir.symbols, functions, "default_a") equals `owner_a.Shared::inherited`
   - Expected: fimr_resolution_name(hir.symbols, functions, "imported_field_index") equals `owner_a.Cell::to_text`
   - Expected: fimr_resolution_name(hir.symbols, functions, "imported_enum") equals `owner_a.TextCell::to_text`
   - Expected: fimr_function_tail_marker(functions, "no_tail") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps owner identity across parameters constructors factories traits and aliases")
val trait_source = "pub trait SharedTrait:\n    fn inherited(self) -> i64: 41\n"
val owner_a_source = r"use trait_owner.{SharedTrait}" + "\n" +
    "pub struct Cell:\n    value: text\n" +
    "pub struct Shared:\n    handle: i64\n" +
    "pub struct Row:\n    values: [Cell]\n" +
    "pub enum TextCell:\n    Text(value: text)\n" +
    "impl Cell:\n    fn to_text(self) -> text: self.value\n" +
    "impl TextCell:\n    fn to_text(self) -> text:\n        match self:\n            TextCell.Text(value): value\n" +
    "impl Shared:\n    fn cleanup(self) -> i64: 17\n    static fn open() -> Shared: Shared(handle: 1)\n" +
    "impl SharedTrait for Shared:\n    pass_dn\n" +
    "pub fn make() -> Shared: Shared(handle: 2)\n"
val owner_b_source = "pub struct Shared:\n    handle: i64\n" +
    "impl Shared:\n    fn cleanup(self) -> i64: 99\n    static fn open() -> Shared: Shared(handle: 3)\n" +
    "pub fn make() -> Shared: Shared(handle: 4)\n"
val consumer_source = r"use owner_a.{Shared as A, Row, Cell, TextCell, make as make_a}" + "\n" +
    r"use owner_b.{Shared as B, make as make_b}" + "\n" +
    "fn param_a(value: A) -> i64: value.cleanup()\n" +
    "fn param_b(value: B) -> i64: value.cleanup()\n" +
    "fn static_a() -> A: A.open()\n" +
    "fn static_b() -> B: B.open()\n" +
    "fn constructor_a() -> i64: A(handle: 5).cleanup()\n" +
    "fn factory_a() -> i64: make_a().cleanup()\n" +
    "fn factory_b() -> i64: make_b().cleanup()\n" +
    "fn default_a(value: A) -> i64: value.inherited()\n" +
    "fn imported_field_index(row: Row) -> text: row.values[0].to_text()\n" +
    "fn imported_enum(value: TextCell) -> text: value.to_text()\n" +
    "fn no_tail():\n    pass_dn\n"
val logger = Logger(level: 0)
val trait_module = parse_full_frontend(trait_source, "trait_owner.spl", "trait_owner", logger)
val owner_a = parse_full_frontend(owner_a_source, "owner_a.spl", "owner_a", logger)
val owner_b = parse_full_frontend(owner_b_source, "owner_b.spl", "owner_b", logger)
val consumer = parse_full_frontend(consumer_source, "consumer.spl", "consumer", logger)
var modules: Dict<text, Module> = {}
modules["trait_owner"] = trait_module
modules["owner_a"] = owner_a
modules["owner_b"] = owner_b
modules["consumer"] = consumer
val sources = [
    SourceFile(path: "trait_owner.spl", content: trait_source, module_name: "trait_owner"),
    SourceFile(path: "owner_a.spl", content: owner_a_source, module_name: "owner_a"),
    SourceFile(path: "owner_b.spl", content: owner_b_source, module_name: "owner_b"),
    SourceFile(path: "consumer.spl", content: consumer_source, module_name: "consumer")
]
val surfaces = fimr_surfaces(modules, sources)
var lowering = hirlowering_for_module("consumer.spl", surfaces)
val hir = lowering.lower_module(consumer)
val (functions, errors) = resolve_flat_methods(hir.symbols, hir.functions.values(), hir.impls)
expect(lowering.errors.len()).to_equal(0)
expect(errors.len()).to_equal(0)
expect(fimr_resolution_name(hir.symbols, functions, "param_a")).to_equal("owner_a.Shared::cleanup")
expect(fimr_resolution_name(hir.symbols, functions, "param_b")).to_equal("owner_b.Shared::cleanup")
expect(fimr_resolution_name(hir.symbols, functions, "static_a")).to_equal("owner_a.Shared::open")
expect(fimr_resolution_name(hir.symbols, functions, "static_b")).to_equal("owner_b.Shared::open")
expect(fimr_resolution_name(hir.symbols, functions, "constructor_a")).to_equal("owner_a.Shared::cleanup")
expect(fimr_resolution_name(hir.symbols, functions, "factory_a")).to_equal("owner_a.Shared::cleanup")
expect(fimr_resolution_name(hir.symbols, functions, "factory_b")).to_equal("owner_b.Shared::cleanup")
expect(fimr_resolution_name(hir.symbols, functions, "default_a")).to_equal("owner_a.Shared::inherited")
expect(fimr_resolution_name(hir.symbols, functions, "imported_field_index")).to_equal("owner_a.Cell::to_text")
expect(fimr_resolution_name(hir.symbols, functions, "imported_enum")).to_equal("owner_a.TextCell::to_text")
expect(fimr_function_tail_marker(functions, "no_tail")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `01b478ece2a6b98644be5a977df2e702f1463de9fcf03c3b6df92a3fceb69844`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01b478ece2a6b98644be5a977df2e702f1463de9fcf03c3b6df92a3fceb69844`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01b478ece2a6b98644be5a977df2e702f1463de9fcf03c3b6df92a3fceb69844`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/semantics/flat_imported_method_resolution_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/flat_imported_method_resolution_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/flat_imported_method_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/flat_imported_method_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/flat_imported_method_resolution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/flat_imported_method_resolution_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps owner identity across parameters constructors factories traits and aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
