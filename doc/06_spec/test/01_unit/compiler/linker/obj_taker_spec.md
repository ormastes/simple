# Obj Taker Specification

> <details>

<!-- sdn-diagram:id=obj_taker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=obj_taker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

obj_taker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=obj_taker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Obj Taker Specification

## Scenarios

### Obj Taker

#### builds the default configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = objtakerconfig_default()
expect(config.enable_caching).to_equal(true)
expect(config.max_cache_size).to_equal(10000)
expect(config.verbose).to_equal(false)
expect(config.allow_deferred).to_equal(true)
```

</details>

#### starts with empty caches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj_taker = objtaker_with_defaults()
val stats = objtaker_cache_stats(obj_taker)
expect(stats.template_count).to_equal(0)
expect(stats.instance_count).to_equal(0)
expect(stats.metadata_count).to_equal(0)
```

</details>

#### mangles names and substitutes type arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = make_template("Result", 2)
val type_args = [make_int_type(64, true), make_string_type()]
val substituted = template_substitute(tmpl, type_args)

expect(mangle_name("Vec", [])).to_equal("Vec")
expect(mangle_name("Vec", [make_int_type(64, true)])).to_equal("Vec$i64")
expect(substituted.tmpl.name).to_equal("Result")
expect(substituted.type_args.len()).to_equal(2)
expect(substituted.mangled_name).to_equal("Result$i64_string")
```

</details>

#### constructs result variants with the expected payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = make_symbol("generic_fn", true, 1)
val tmpl = make_template("generic_fn", 1)
val hints = DeferredHints(symbol: "deferred_fn", type_vars: [], constraints: [], usage_sites: [])

val code_result = ObjTakeResult.Code(bytes: [1, 2, 3], symbol: symbol, ty: nil)
val template_result = ObjTakeResult.Template(tmpl: tmpl, symbol: symbol)
val deferred_result = ObjTakeResult.Deferred(symbol: "deferred_fn", hints: hints)
val not_found = ObjTakeResult.NotFound(symbol: "missing")
val error_result = ObjTakeResult.Error(message: "bad")

match code_result:
    case Code(bytes, found_symbol, ty):
        expect(bytes).to_equal([1, 2, 3])
        expect(found_symbol.name).to_equal("generic_fn")
    case _:
        expect("wrong").to_equal("code")

match template_result:
    case Template(found_tmpl, found_symbol):
        expect(found_tmpl.name).to_equal("generic_fn")
        expect(found_symbol.is_generic_template).to_equal(true)
    case _:
        expect("wrong").to_equal("template")

match deferred_result:
    case Deferred(name, found_hints):
        expect(name).to_equal("deferred_fn")
        expect(found_hints.symbol).to_equal("deferred_fn")
    case _:
        expect("wrong").to_equal("deferred")

match not_found:
    case NotFound(name):
        expect(name).to_equal("missing")
    case _:
        expect("wrong").to_equal("not_found")

match error_result:
    case Error(message):
        expect(message).to_equal("bad")
    case _:
        expect("wrong").to_equal("error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/obj_taker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Obj Taker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
