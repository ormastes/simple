# Config Specification

> <details>

<!-- sdn-diagram:id=config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Specification

## Scenarios

### parse_mdsoc_sdn basics

#### empty string returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_mdsoc_sdn("")
expect(result).to_be_nil()
```

</details>

#### whitespace-only returns manifest with empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser only returns nil for empty string; whitespace-only
# produces a manifest with empty capsule name
val result = parse_mdsoc_sdn("   \n\n  ")
val manifest = result ?? MdsocManifest.new("")
expect(manifest.name).to_equal("")
```

</details>

#### minimal valid config returns manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: my-project\n  version: 0.1.0"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.name).to_equal("my-project")
expect(manifest.version).to_equal("0.1.0")
```

</details>

### parse_mdsoc_sdn capsule section

#### parses capsule name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: web-app\n  version: 1.0.0"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.name).to_equal("web-app")
```

</details>

#### parses capsule version

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 2.3.1"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.version).to_equal("2.3.1")
```

</details>

#### handles missing version gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.name).to_equal("proj")
# version defaults to "0.1.0" when not specified
expect(manifest.version).to_equal("0.1.0")
```

</details>

### parse_mdsoc_sdn roots section

#### parses single root

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nroots:\n  - name: core\n    path: src/core"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.carets.len()).to_equal(1)
val caret = manifest.carets[0]
expect(caret.name).to_equal("core")
expect(caret.path).to_equal("src/core")
```

</details>

#### parses multiple roots

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nroots:\n  - name: core\n    path: src/core"
sdn = sdn + "\n  - name: ui\n    path: src/ui"
sdn = sdn + "\n  - name: infra\n    path: src/infra"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.carets.len()).to_equal(3)
```

</details>

#### root name field maps to CaretId name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nroots:\n  - name: backend\n    path: src/backend"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val caret = manifest.carets[0]
expect(caret.name).to_equal("backend")
```

</details>

#### root path field maps to CaretId path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nroots:\n  - name: api\n    path: src/api/v2"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val caret = manifest.carets[0]
expect(caret.path).to_equal("src/api/v2")
```

</details>

### parse_mdsoc_sdn dimension section

#### parses dimension name and key_template

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.dimensions.len()).to_equal(1)
val dim = manifest.dimensions[0]
expect(dim.name).to_equal("feature")
expect(dim.key_template).to_equal("feature/" + r"{name}")
```

</details>

#### parses dimension surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n  surface: surface.spl"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.surface_file).to_equal("surface.spl")
```

</details>

#### parses dimension participation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n  participation: auto_bind"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.participation).to_equal("auto_bind")
```

</details>

#### parses dimension dependency_cycles

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n  dependency_cycles: allow"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.dep_cycles).to_equal("allow")
```

</details>

#### dimension without explicit surface uses default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.surface_file).to_equal("__init__.spl")
```

</details>

### parse_mdsoc_sdn dimension map

#### parses caret-to-pattern mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  map:\n    - caret: core\n      match: feature/**"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.mappings.len()).to_be_greater_than(0)
```

</details>

#### mapping has correct caret_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  map:\n    - caret: ui\n      match: ui_feature/**"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
val mapping = dim.mappings[0]
expect(mapping.caret_name).to_equal("ui")
```

</details>

#### mapping has correct match_pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  map:\n    - caret: core\n      match: feature/**"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
val mapping = dim.mappings[0]
expect(mapping.match_pattern).to_equal("feature/**")
```

</details>

#### parses multiple map entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  map:\n    - caret: core\n      match: feature/**"
sdn = sdn + "\n    - caret: ui\n      match: ui_feature/**"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.mappings.len()).to_equal(2)
expect(dim.mappings[0].caret_name).to_equal("core")
expect(dim.mappings[1].caret_name).to_equal("ui")
```

</details>

### parse_mdsoc_sdn dimension layering

#### parses layer order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  layering:\n    order: [api, app, domain, infra]"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.layer.order.len()).to_equal(4)
```

</details>

#### parses layer direction upper_to_lower

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  layering:\n    order: [api, domain]\n    direction: upper_to_lower"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.layer.direction.to_text()).to_equal("upper_to_lower")
```

</details>

#### parses layer direction lower_to_upper

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  layering:\n    order: [api, domain]\n    direction: lower_to_upper"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.layer.direction.to_text()).to_equal("lower_to_upper")
```

</details>

#### parses allow_same_layer flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  layering:\n    order: [api, domain]\n    allow_same_layer: false"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.layer.allow_same_layer).to_equal(false)
```

</details>

#### parses allow_adjacent_only flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  layering:\n    order: [api, app, domain]\n    allow_adjacent_only: true"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.layer.allow_adjacent_only).to_equal(true)
```

</details>

### parse_mdsoc_sdn rules section

#### parses all four boolean flags (strict)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nrules:\n  enforce_layering: true\n  reject_cycles: true"
sdn = sdn + "\n  forbid_implicit_merge: true\n  require_explicit_bind: true"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.rules.enforce_layering).to_equal(true)
expect(manifest.rules.reject_cycles).to_equal(true)
expect(manifest.rules.forbid_implicit_merge).to_equal(true)
expect(manifest.rules.require_explicit_bind).to_equal(true)
```

</details>

#### parses permissive rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nrules:\n  enforce_layering: false\n  reject_cycles: false"
sdn = sdn + "\n  forbid_implicit_merge: false\n  require_explicit_bind: false"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.rules.enforce_layering).to_equal(false)
expect(manifest.rules.reject_cycles).to_equal(false)
expect(manifest.rules.forbid_implicit_merge).to_equal(false)
expect(manifest.rules.require_explicit_bind).to_equal(false)
```

</details>

#### parses mixed rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nrules:\n  enforce_layering: true\n  reject_cycles: false"
sdn = sdn + "\n  forbid_implicit_merge: true\n  require_explicit_bind: false"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
expect(manifest.rules.enforce_layering).to_equal(true)
expect(manifest.rules.reject_cycles).to_equal(false)
expect(manifest.rules.forbid_implicit_merge).to_equal(true)
expect(manifest.rules.require_explicit_bind).to_equal(false)
```

</details>

### parse_mdsoc_sdn full config

#### parses complete capsule.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: my-project\n  version: 1.2.0\n"
sdn = sdn + "\nroots:\n  - name: core\n    path: src/core"
sdn = sdn + "\n  - name: ui\n    path: src/ui\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}" + "\n"
sdn = sdn + "  layering:\n    order: [api, app, domain, infra]\n    direction: upper_to_lower\n"
sdn = sdn + "\nrules:\n  enforce_layering: true\n  reject_cycles: true"
sdn = sdn + "\n  forbid_implicit_merge: true\n  require_explicit_bind: true"

val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")

# capsule section
expect(manifest.name).to_equal("my-project")
expect(manifest.version).to_equal("1.2.0")

# roots section
expect(manifest.carets.len()).to_equal(2)

# dimensions section
expect(manifest.dimensions.len()).to_equal(1)
val dim = manifest.dimensions[0]
expect(dim.name).to_equal("feature")
expect(dim.layer.order.len()).to_equal(4)

# rules section
expect(manifest.rules.enforce_layering).to_equal(true)
```

</details>

#### carets are accessible by name after parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\nroots:\n  - name: core\n    path: src/core"
sdn = sdn + "\n  - name: ui\n    path: src/ui"

val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val core_caret = manifest.get_caret("core")
val core = core_caret ?? CaretId.new("", "")
expect(core.name).to_equal("core")
expect(core.path).to_equal("src/core")
```

</details>

#### dimensions support expand_key after parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sdn = "capsule:\n  name: proj\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: feature\n  key_template: feature/" + r"{name}"

val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("")
val dim = manifest.dimensions[0]
expect(dim.expand_key("auth")).to_equal("feature/auth")
```

</details>

### parse_mdsoc_sdn error cases

#### missing capsule section returns manifest with empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Input has roots but no capsule section; parser returns a manifest
# with empty name (nil only for empty source)
var sdn = "roots:\n  - name: core\n    path: src/core"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("fallback")
expect(manifest.name).to_equal("")
```

</details>

#### missing capsule name returns manifest with empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# capsule section exists but has no name field
var sdn = "capsule:\n  version: 0.1.0"
val result = parse_mdsoc_sdn(sdn)
val manifest = result ?? MdsocManifest.new("fallback")
expect(manifest.name).to_equal("")
```

</details>

#### random text returns manifest with empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Non-empty text without valid sections still returns a manifest
val result = parse_mdsoc_sdn("this is not valid SDN at all")
val manifest = result ?? MdsocManifest.new("fallback")
expect(manifest.name).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_mdsoc_sdn basics
- parse_mdsoc_sdn capsule section
- parse_mdsoc_sdn roots section
- parse_mdsoc_sdn dimension section
- parse_mdsoc_sdn dimension map
- parse_mdsoc_sdn dimension layering
- parse_mdsoc_sdn rules section
- parse_mdsoc_sdn full config
- parse_mdsoc_sdn error cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
