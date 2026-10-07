# Resolved static generic factories

> Static factories with method type parameters must enter the same specialization worklist as generic free functions. These cases lower real source and distinguish successful inference from a missing type argument.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resolved static generic factories

Static factories with method type parameters must enter the same specialization worklist as generic free functions. These cases lower real source and distinguish successful inference from a missing type argument.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/08_tracking/bug/static_generic_factory_specialization_missing_2026-10-06.md |
| Research | doc/08_tracking/bug/static_generic_factory_specialization_missing_2026-10-06.md |
| Source | `test/01_unit/compiler/mono/mono_static_generic_factory_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Static factories with method type parameters must enter the same specialization worklist as generic free functions. These cases lower real source and distinguish successful inference from a missing type argument.

## Examples
`Factory.injected(7)` creates exactly one concrete i64 function. A factory whose parameter T appears in no argument or return type produces an unresolved diagnostic instead of a guessed specialization.

**Requirements:** N/A
**Plan:** N/A
**Design:** doc/08_tracking/bug/static_generic_factory_specialization_missing_2026-10-06.md
**Research:** doc/08_tracking/bug/static_generic_factory_specialization_missing_2026-10-06.md

Bootstrap harness: set SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 when SIMPLE_BOOTSTRAP=1 so testdata paths are parsed rather than deliberately filtered. HIR qualification does not replace native emitted-object and executable qualification.

## Scenarios

### resolved static generic factory specialization

#### creates a concrete factory from its resolved method symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class Factory:\n    static fn injected<T>(value: T) -> T:\n        value\n\nfn main() -> i64:\n    Factory.injected(7)\n"
val parsed = parse_full_frontend(src, "testdata/static_factory.spl", "static_factory", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/static_factory.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats) = run_monomorphization(mods)
expect(stats.specializations_created).to_equal(1)
expect(stats.unresolved_generic_calls).to_equal(0)
var concrete = 0
val om: HirModule = out["m"]
for key in om.functions.keys():
    val f: HirFunction = om.functions[key]
    if f.name.contains("$i64"):
        concrete = concrete + 1
        expect(f.type_params.len()).to_equal(0)
expect(concrete).to_equal(1)
```

</details>

#### does not invent a specialization when the method type cannot be inferred

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class Factory:\n    static fn missing<T>() -> i64:\n        3\n\nfn main() -> i64:\n    Factory.missing()\n"
val parsed = parse_full_frontend(src, "testdata/static_missing.spl", "static_missing", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/static_missing.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats) = run_monomorphization(mods)
expect(stats.specializations_created).to_equal(0)
expect(stats.unresolved_generic_calls).to_equal(1)
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


## Related Documentation

- **Design:** `doc/08_tracking/bug/static_generic_factory_specialization_missing_2026-10-06.md`
- **Research:** `doc/08_tracking/bug/static_generic_factory_specialization_missing_2026-10-06.md`


</details>
