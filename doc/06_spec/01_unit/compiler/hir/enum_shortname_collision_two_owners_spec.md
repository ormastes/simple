# Enum Short-Name Collision Across Two Owners — Unit Spec

> Regression guard for the Stage-1 HIR fatal

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Short-Name Collision Across Two Owners — Unit Spec

Regression guard for the Stage-1 HIR fatal

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

```simple
Regression guard for the Stage-1 HIR fatal

    HIR lowering error in src/compiler/driver/driver.spl:
    enum payload dependency `AdviceForm` conflicts:
    `compiler.frontend.core.aop::AdviceForm::enum`
    vs `compiler.mdsoc.weaving.advice_form::AdviceForm::enum`

Two GENUINELY DISTINCT enums are declared under one short name —
`enum AdviceForm` in `src/compiler/10.frontend/core/aop.spl` and another
`enum AdviceForm` in `src/compiler/85.mdsoc/weaving/advice_form.spl`. Neither
is a duplicate of the other and neither is dead. A module that transitively
reaches both (`src/compiler/80.driver/driver.spl`) must import both.

`materialized_payload_bindings` is keyed on the LOCAL SHORT NAME, so the second
claimant could only ever lose that slot. Losing it used to be a hard
`self.error(...)` plus a bare `return` — so the second enum got no symbol at all
AND the whole module failed to lower. A short-name collision is not a defect; it
only means the unqualified spelling is already taken. The loser is now
re-registered under `{owner_module}::{name}`, which `register_imported_symbol`
also `bind_qualified_type`s, exactly as
`materialize_imported_callable_declared_dependency` already did for signature
dependencies.

```
## Scenarios

### two distinct enums sharing one short name

#### lowers a module that imports both without a conflict error

- lowers a module that imports both without a conflict error
   - Expected: conflicts equals `0`
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a module that imports both without a conflict error")
val log = dual_enum_spec_logger()
# Two unrelated owners, each declaring its own `AdviceForm`. The
# variants differ so the two terminal identities genuinely disagree.
val aop_source = "enum AdviceForm:\n    Before\n    After"
val weave_source = "enum AdviceForm:\n    Around\n    Wrap"
val consumer_source =
    "use dual.aop.\{AdviceForm\}\nuse dual.weave.\{AdviceForm\}\n\nfn pick() -> i64:\n    1"
val aop = parse_full_frontend(aop_source, "dual.aop", "dual.aop", log)
val weave = parse_full_frontend(weave_source, "dual.weave", "dual.weave", log)
val consumer = parse_full_frontend(consumer_source, "dual.consumer", "dual.consumer", log)

var modules: Dict<text, Module> = {}
modules["dual.aop"] = aop
modules["dual.weave"] = weave
val sources = [
    SourceFile(path: "dual/aop.spl", content: aop_source, module_name: "dual.aop"),
    SourceFile(path: "dual/weave.spl", content: weave_source, module_name: "dual.weave")
]
val surfaces = dual_enum_spec_surfaces(modules, sources)
var lowering = hirlowering_for_module("dual.consumer", surfaces)
val hir = lowering.lower_module(consumer)
# Pre-fix: one `enum payload dependency `AdviceForm` conflicts:
# `dual.aop::AdviceForm::enum` vs `dual.weave::AdviceForm::enum``,
# attributed to the CONSUMER.
var conflicts: i64 = 0
for error in lowering.errors:
    if error.message.contains("conflicts"):
        conflicts = conflicts + 1
expect(conflicts).to_equal(0)
expect(lowering.errors.len()).to_equal(0)
```

</details>

#### keeps both enums reachable, the loser under its qualified name

- keeps both enums reachable, the loser under its qualified name


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps both enums reachable, the loser under its qualified name")
val log = dual_enum_spec_logger()
val aop_source = "enum AdviceForm:\n    Before\n    After"
val weave_source = "enum AdviceForm:\n    Around\n    Wrap"
val consumer_source =
    "use dual.aop.\{AdviceForm\}\nuse dual.weave.\{AdviceForm\}\n\nfn pick() -> i64:\n    1"
val aop = parse_full_frontend(aop_source, "dual.aop", "dual.aop", log)
val weave = parse_full_frontend(weave_source, "dual.weave", "dual.weave", log)
val consumer = parse_full_frontend(consumer_source, "dual.consumer", "dual.consumer", log)

var modules: Dict<text, Module> = {}
modules["dual.aop"] = aop
modules["dual.weave"] = weave
val sources = [
    SourceFile(path: "dual/aop.spl", content: aop_source, module_name: "dual.aop"),
    SourceFile(path: "dual/weave.spl", content: weave_source, module_name: "dual.weave")
]
val surfaces = dual_enum_spec_surfaces(modules, sources)
var lowering = hirlowering_for_module("dual.consumer", surfaces)
val hir = lowering.lower_module(consumer)
# Both owners keep a qualified binding; the short name resolves to
# whichever claimed it first, and the other stays addressable.
expect(lowering.symbols.lookup_qualified_type_raw("dual.aop", "AdviceForm") >= 0).to_be_true()
expect(lowering.symbols.lookup_qualified_type_raw("dual.weave", "AdviceForm") >= 0).to_be_true()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `287c6cbb2f3e36311eceb7fcd27d0a3a2cebde13f819adac32152a27703e470f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `287c6cbb2f3e36311eceb7fcd27d0a3a2cebde13f819adac32152a27703e470f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `287c6cbb2f3e36311eceb7fcd27d0a3a2cebde13f819adac32152a27703e470f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a module that imports both without a conflict error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps both enums reachable, the loser under its qualified name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
