# imported_callable_materialization_cardinality_spec

> Repeated import roots materialize one callable symbol and one signature.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# imported_callable_materialization_cardinality_spec

Repeated import roots materialize one callable symbol and one signature.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Repeated import roots materialize one callable symbol and one signature.

## Scenarios

### imported callable materialization cardinality

#### materializes one callable for repeated glob roots of one physical surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- materializes one callable for repeated glob roots of one physical surface
   - Expected: surfaces.surfaces.len() equals `1`
   - Expected: lowering.errors.len() equals `0`
   - Expected: materialize_id.is_valid() is true
   - Expected: materialize_rows equals `1`
   - Expected: signature_param_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("materializes one callable for repeated glob roots of one physical surface")
val logger = Logger(level: 0)
val owner_source = "pub struct Token:\n" +
    "    value: i64\n" +
    "pub fn materialize(a: Token, b: [Token], c: text, d: i64) -> Token:\n" +
    "    a\n"
val owner = parse_full_frontend(
    owner_source, "card.owner", "card.owner", logger)
val owner_alias = parse_full_frontend(
    owner_source, "card.owner_alias", "card.owner_alias", logger)
var modules: Dict<text, Module> = {}
modules["card.owner"] = owner
modules["card.owner_alias"] = owner_alias
val surfaces = callable_cardinality_surfaces(modules, [
    SourceFile(
        path: "card/owner.spl", content: owner_source,
        module_name: "card.owner"),
    SourceFile(
        path: "card\\owner.spl", content: owner_source,
        module_name: "card.owner_alias")
])
expect(surfaces.surfaces.len()).to_equal(1)
expect(surfaces.index_by_name["card.owner"]).to_equal(
    surfaces.index_by_name["card.owner_alias"])

val consumer_source = "use card.owner.*\n" +
    "use card.owner_alias.*\n" +
    "use card.owner.*\n" +
    "use card.owner_alias.*\n" +
    "fn main() -> i64:\n" +
    "    0\n"
val consumer = parse_full_frontend(
    consumer_source, "card.consumer", "card.consumer", logger)
var lowering = hirlowering_for_module("card.consumer", surfaces)
val hir = lowering.lower_module(consumer)
expect(lowering.errors.len()).to_equal(0)

val materialize_id = hir.symbols.lookup_or_invalid("materialize")
expect(materialize_id.is_valid()).to_equal(true)
var materialize_rows = 0
for symbol in hir.symbols.symbols.values():
    if (symbol.kind == SymbolKind.Function and
            (symbol.name == "materialize" or
             symbol.name.ends_with(".materialize"))):
        if val defining_module = symbol.defining_module:
            if (defining_module == "card.owner" or
                    defining_module == "card.owner_alias"):
                materialize_rows = materialize_rows + 1
expect(materialize_rows).to_equal(1)

var signature_param_count = -1
if val materialize_symbol = hir.symbols.get_symbol_raw(materialize_id.id):
    if val materialize_type = materialize_symbol.type_:
        match materialize_type.kind:
            case HirTypeKind.Function(params, _, _):
                signature_param_count = params.len()
            case _: pass
expect(signature_param_count).to_equal(4)
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

- Canonical SPipe generation for source `2f5689b15853d35dc5f82aad725ab65260f22b7d61d39aff75902ffb155e2bfb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f5689b15853d35dc5f82aad725ab65260f22b7d61d39aff75902ffb155e2bfb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f5689b15853d35dc5f82aad725ab65260f22b7d61d39aff75902ffb155e2bfb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes one callable for repeated glob roots of one physical surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
