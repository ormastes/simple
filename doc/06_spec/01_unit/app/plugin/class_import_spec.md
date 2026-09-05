# Class Import Specification

> <details>

<!-- sdn-diagram:id=class_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=class_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

class_import_spec -> std
class_import_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=class_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class Import Specification

## Scenarios

### class-level plugin import

### parse_plugin_manifest_text with classes

#### parses a manifest with class entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_text = "plugins:\n    -\n        name: test_lib\n        library: libtest.so\n        classes:\n            Calculator:\n                constructor: spl_Calculator_create\n                destructor: spl_Calculator_destroy\n                methods:\n                    add:\n                        symbol: spl_Calculator_add\n                        params: [handle, i64]\n                        return: i64"
val result = parse_plugin_manifest_text(manifest_text)
expect(result.len()).to_equal(1)
expect(result[0].classes.len()).to_equal(1)
expect(result[0].classes[0].name).to_equal("Calculator")
expect(result[0].classes[0].constructor_symbol).to_equal("spl_Calculator_create")
expect(result[0].classes[0].destructor_symbol).to_equal("spl_Calculator_destroy")
expect(result[0].classes[0].methods.len()).to_equal(1)
expect(result[0].classes[0].methods[0].name).to_equal("add")
expect(result[0].classes[0].methods[0].symbol).to_equal("spl_Calculator_add")
expect(result[0].classes[0].methods[0].params.len()).to_equal(2)
expect(result[0].classes[0].methods[0].return_type).to_equal("i64")
```

</details>

#### handles manifest with both functions and classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_text = "plugins:\n    -\n        name: mixed_lib\n        library: libmixed.so\n        version: \"1.0.0\"\n        functions: [rt_init, rt_cleanup]\n        classes:\n            Widget:\n                constructor: spl_Widget_new\n                destructor: spl_Widget_free\n                methods:\n                    resize:\n                        symbol: spl_Widget_resize\n                        params: [handle, i64, i64]\n                        return: i64"
val result = parse_plugin_manifest_text(manifest_text)
expect(result.len()).to_equal(1)
expect(result[0].name).to_equal("mixed_lib")
expect(result[0].functions.len()).to_equal(2)
expect(result[0].functions[0]).to_equal("rt_init")
expect(result[0].classes.len()).to_equal(1)
expect(result[0].classes[0].name).to_equal("Widget")
```

</details>

#### handles manifest with empty classes block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_text = "plugins:\n    -\n        name: empty_cls\n        library: libempty.so\n        functions: [rt_do_stuff]\n        classes:"
val result = parse_plugin_manifest_text(manifest_text)
expect(result.len()).to_equal(1)
expect(result[0].functions.len()).to_equal(1)
expect(result[0].classes.len()).to_equal(0)
```

</details>

#### handles manifest without classes block

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_text = "plugins:\n    -\n        name: no_cls\n        library: libnocls.so\n        functions: [rt_hello]"
val result = parse_plugin_manifest_text(manifest_text)
expect(result.len()).to_equal(1)
expect(result[0].name).to_equal("no_cls")
expect(result[0].functions.len()).to_equal(1)
expect(result[0].classes.len()).to_equal(0)
```

</details>

#### parses multiple methods in a class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_text = "plugins:\n    -\n        name: multi_method\n        library: libmm.so\n        classes:\n            Counter:\n                constructor: spl_Counter_new\n                destructor: spl_Counter_free\n                methods:\n                    increment:\n                        symbol: spl_Counter_inc\n                        params: [handle]\n                        return: i64\n                    get_value:\n                        symbol: spl_Counter_get\n                        params: [handle]\n                        return: i64\n                    reset:\n                        symbol: spl_Counter_reset\n                        params: [handle]\n                        return: i64"
val result = parse_plugin_manifest_text(manifest_text)
expect(result[0].classes[0].methods.len()).to_equal(3)
expect(result[0].classes[0].methods[0].name).to_equal("increment")
expect(result[0].classes[0].methods[1].name).to_equal("get_value")
expect(result[0].classes[0].methods[2].name).to_equal("reset")
```

</details>

#### parses multiple classes in one plugin

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_text = "plugins:\n    -\n        name: multi_cls\n        library: libmc.so\n        classes:\n            Foo:\n                constructor: spl_Foo_new\n                destructor: spl_Foo_free\n                methods:\n                    bar:\n                        symbol: spl_Foo_bar\n                        params: [handle]\n                        return: i64\n            Baz:\n                constructor: spl_Baz_new\n                destructor: spl_Baz_free\n                methods:\n                    qux:\n                        symbol: spl_Baz_qux\n                        params: [handle, i64]\n                        return: i64"
val result = parse_plugin_manifest_text(manifest_text)
expect(result[0].classes.len()).to_equal(2)
expect(result[0].classes[0].name).to_equal("Foo")
expect(result[0].classes[1].name).to_equal("Baz")
expect(result[0].classes[1].methods[0].symbol).to_equal("spl_Baz_qux")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/plugin/class_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- class-level plugin import
- parse_plugin_manifest_text with classes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
