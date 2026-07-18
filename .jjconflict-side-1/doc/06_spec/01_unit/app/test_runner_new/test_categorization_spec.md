# Test Categorization Specification

> <details>

<!-- sdn-diagram:id=test_categorization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_categorization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_categorization_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_categorization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Categorization Specification

## Scenarios

### TestCategory Auto-Detection

#### detects platform from baremetal path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/feature/baremetal/boot_spec.spl"
var cat = "other"
if path.contains("/baremetal/") or path.contains("/qemu/") or path.contains("/cuda/") or path.contains("/gpu/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from cuda path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/lib/gc_async_mut/cuda/gc_cuda_spec.spl"
var cat = "other"
if path.contains("/cuda/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from gpu path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/lib/gc_async_mut/gpu/driver_spec.spl"
var cat = "other"
if path.contains("/gpu/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from qemu path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/feature/baremetal/riscv32/collections_qemu_spec.spl"
var cat = "other"
if path.contains("/qemu/") or path.contains("/baremetal/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from non-all platform tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @platform: baremetal(riscv32)\ndescribe \"boot\":"
val lines = content.split("\n")
var cat = "other"
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @platform:"):
        val tag = trimmed[12:].trim()
        if tag != "" and tag != "all" and tag != "host":
            cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### does not detect platform from all platform tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @platform: all\ndescribe \"shared\":"
val lines = content.split("\n")
var cat = "not_platform"
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @platform:"):
        val tag = trimmed[12:].trim()
        if tag != "" and tag != "all" and tag != "host":
            cat = "platform"
expect(cat).to_equal("not_platform")
```

</details>

#### treats shared path as canonical unit-level cross-platform tier

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/shared/core/primitives_spec.spl"
var level = "other"
if path.contains("/unit/") or path.contains("/shared/"):
    level = "unit"
elif path.contains("/integration/"):
    level = "integration"
elif path.contains("/system/") or path.contains("/feature/"):
    level = "system"
expect(level).to_equal("unit")
```

</details>

#### detects standalone when no use statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "describe \"basics\":\n    it \"works\":\n        expect(1).to_equal(1)"
val lines = content.split("\n")
var has_use = false
for line in lines:
    if line.trim().starts_with("use "):
        has_use = true
var cat = "other"
if not has_use:
    cat = "standalone"
expect(cat).to_equal("standalone")
```

</details>

#### detects standalone when only spec import

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use std.spec\ndescribe \"x\":\n    it \"y\":\n        pass"
val lines = content.split("\n")
var has_use = false
var only_spec = true
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("use "):
        has_use = true
        val module = trimmed[4:].trim()
        val is_spec = module.starts_with("std.spec") or module.starts_with("nogc_sync_mut.spec")
        if not is_spec:
            only_spec = false
var cat = "other"
if not has_use or only_spec:
    cat = "standalone"
expect(cat).to_equal("standalone")
```

</details>

#### detects lib when has non-spec imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use std.spec\nuse app.io.file_ops\ndescribe \"x\":"
val lines = content.split("\n")
var has_use = false
var only_spec = true
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("use "):
        has_use = true
        val module = trimmed[4:].trim()
        val is_spec = module.starts_with("std.spec") or module.starts_with("nogc_sync_mut.spec")
        if not is_spec:
            only_spec = false
var cat = "other"
if has_use and not only_spec:
    cat = "lib"
expect(cat).to_equal("lib")
```

</details>

### Explicit Category Annotation

#### extracts category from annotation

1. cat = trimmed[12:] trim
   - Expected: cat equals `standalone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @category: standalone\ndescribe \"core\":"
val lines = content.split("\n")
var cat = ""
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @category:"):
        cat = trimmed[12:].trim()
expect(cat).to_equal("standalone")
```

</details>

#### extracts platform category

1. cat = trimmed[12:] trim
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @category: platform\n# @platform: baremetal"
val lines = content.split("\n")
var cat = ""
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @category:"):
        cat = trimmed[12:].trim()
expect(cat).to_equal("platform")
```

</details>

#### explicit category overrides auto-detection

1. explicit cat = trimmed[12:] trim
   - Expected: final_cat equals `lib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @category: lib\ndescribe \"x\":"
val path = "test/feature/baremetal/boot_spec.spl"
val lines = content.split("\n")
var explicit_cat = ""
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @category:"):
        explicit_cat = trimmed[12:].trim()
var auto_cat = "other"
if path.contains("/baremetal/"):
    auto_cat = "platform"
var final_cat = auto_cat
if explicit_cat != "":
    final_cat = explicit_cat
expect(final_cat).to_equal("lib")
```

</details>

### Speed Annotation Parsing

#### extracts default speed

1. speed = trimmed[9:] trim
   - Expected: speed equals `long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @speed: long\ndescribe \"x\":"
val lines = content.split("\n")
var speed = ""
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @speed:"):
        speed = trimmed[9:].trim()
expect(speed).to_equal("long")
```

</details>

#### extracts contextual speed

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line1 = "# @speed(baremetal): short"
expect(line1.starts_with("# @speed(")).to_equal(true)
val rest1 = line1[9:]
expect(rest1.contains(")")).to_equal(true)
val ctx1 = rest1.split(")")[0].trim()
expect(ctx1).to_equal("baremetal")
val after1 = rest1.split(")")[1]
expect(after1.starts_with(":")).to_equal(true)
val spd1 = after1[1:].trim()
expect(spd1).to_equal("short")

val line2 = "# @speed(native): medium"
val rest2 = line2[9:]
val ctx2 = rest2.split(")")[0].trim()
expect(ctx2).to_equal("native")
val spd2 = rest2.split(")")[1][1:].trim()
expect(spd2).to_equal("medium")
```

</details>

#### does not confuse contextual speed with default speed

1. default speed = trimmed[9:] trim
   - Expected: default_speed equals `long`
   - Expected: contextual_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @speed: long\n# @speed(baremetal): short"
val lines = content.split("\n")
var default_speed = ""
var contextual_count = 0
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @speed("):
        contextual_count = contextual_count + 1
    if trimmed.starts_with("# @speed:"):
        default_speed = trimmed[9:].trim()
expect(default_speed).to_equal("long")
expect(contextual_count).to_equal(1)
```

</details>

### Speed Resolution

#### resolves contextual speed when context matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val speed_contexts = "baremetal=short,native=medium"
val context = "baremetal"
var resolved = ""
val pairs = speed_contexts.split(",")
for pair in pairs:
    val kv = pair.split("=")
    if kv.len() == 2:
        val ctx = kv[0].trim()
        val spd = kv[1].trim()
        if ctx == context:
            resolved = spd
expect(resolved).to_equal("short")
```

</details>

#### falls back to default speed when no context match

1. resolved = kv[1] trim
   - Expected: resolved equals `long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val speed_contexts = "baremetal=short"
val speed_default = "long"
val context = "native"
var resolved = ""
val pairs = speed_contexts.split(",")
for pair in pairs:
    val kv = pair.split("=")
    if kv.len() == 2:
        if kv[0].trim() == context:
            resolved = kv[1].trim()
if resolved == "":
    resolved = speed_default
expect(resolved).to_equal("long")
```

</details>

#### falls back to long when has_slow and no annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val speed_contexts = ""
val speed_default = ""
val has_slow = true
var resolved = "unknown"
if speed_default != "":
    resolved = speed_default
if resolved == "unknown" and has_slow:
    resolved = "long"
expect(resolved).to_equal("long")
```

</details>

#### resolves to unknown when no info

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val speed_default = ""
val has_slow = false
var resolved = ""
if speed_default != "":
    resolved = speed_default
elif has_slow:
    resolved = "long"
else:
    resolved = "unknown"
expect(resolved).to_equal("unknown")
```

</details>

### Speed Filter Matching

#### only-short allows only short

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_short = true
expect("short" == "short").to_equal(true)
expect("medium" == "short").to_equal(false)
expect("long" == "short").to_equal(false)
```

</details>

#### speed=medium allows short and medium

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filter = "medium"
var short_ok = false
var medium_ok = false
var long_ok = false
if filter == "medium":
    short_ok = true
    medium_ok = true
expect(short_ok).to_equal(true)
expect(medium_ok).to_equal(true)
expect(long_ok).to_equal(false)
```

</details>

#### speed=long allows everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filter = "long"
var all_pass = false
if filter == "long":
    all_pass = true
expect(all_pass).to_equal(true)
```

</details>

#### empty filter allows everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filter = ""
var all_pass = true
if filter != "":
    all_pass = false
expect(all_pass).to_equal(true)
```

</details>

### Manifest V3 Entry Serialization

#### includes category speed_default speed_contexts in pipe format

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/feature/baremetal/boot_spec.spl"
val category = "platform"
val speed_default = "long"
val speed_contexts = "baremetal=short,native=medium"
val line = "{path}|1000|200|3|1|0|0||baremetal|0|0|0|0|1|native|{category}|{speed_default}|{speed_contexts}"
val parts = line.split("|")
expect(parts.len()).to_equal(18)
expect(parts[15]).to_equal("platform")
expect(parts[16]).to_equal("long")
expect(parts[17]).to_equal("baremetal=short,native=medium")
```

</details>

#### handles empty new fields for backward compat

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "test/unit/x_spec.spl|500|100|1|0|0|0|tag1|linux|0|0|0|0|0|interp"
val parts = line.split("|")
expect(parts.len()).to_equal(15)
var category = ""
var speed_default = ""
var speed_contexts = ""
if parts.len() >= 16:
    category = parts[15]
if parts.len() >= 17:
    speed_default = parts[16]
if parts.len() >= 18:
    speed_contexts = parts[17]
expect(category).to_equal("")
expect(speed_default).to_equal("")
expect(speed_contexts).to_equal("")
```

</details>

### CLI Flag Parsing

#### category flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--category"
expect(flag).to_equal("--category")
```

</details>

#### context flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--context"
expect(flag).to_equal("--context")
```

</details>

#### only-short flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--only-short"
expect(flag).to_equal("--only-short")
```

</details>

#### speed flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--speed"
expect(flag).to_equal("--speed")
```

</details>

#### parses --category=standalone from equals format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--category=standalone"
var category = ""
if arg.starts_with("--category="):
    category = arg[11:]
expect(category).to_equal("standalone")
```

</details>

#### parses --context=baremetal from equals format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--context=baremetal"
var context = ""
if arg.starts_with("--context="):
    context = arg[10:]
expect(context).to_equal("baremetal")
```

</details>

#### parses --speed=medium from equals format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--speed=medium"
var speed = ""
if arg.starts_with("--speed="):
    speed = arg[8:]
expect(speed).to_equal("medium")
```

</details>

### Decorator Annotation Parsing

#### detects @short_test decorator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@short_test(baremetal)"
expect(line.starts_with("@short_test")).to_equal(true)
```

</details>

#### extracts context from @short_test(baremetal)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trimmed = "@short_test(baremetal)"
var ctx = ""
if trimmed.contains("(") and trimmed.contains(")"):
    val after_paren = trimmed.split("(")
    if after_paren.len() >= 2:
        val inside = after_paren[1].split(")")[0].trim()
        ctx = inside
expect(ctx).to_equal("baremetal")
```

</details>

#### handles @long_test without context

1. ctx = after paren[1] split
   - Expected: ctx equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trimmed = "@long_test"
var ctx = ""
if trimmed.contains("(") and trimmed.contains(")"):
    val after_paren = trimmed.split("(")
    if after_paren.len() >= 2:
        ctx = after_paren[1].split(")")[0].trim()
expect(ctx).to_equal("")
```

</details>

#### detects @medium_test decorator

1. ctx = after paren[1] split
   - Expected: ctx equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@medium_test(native)"
expect(line.starts_with("@medium_test")).to_equal(true)
var ctx = ""
if line.contains("(") and line.contains(")"):
    val after_paren = line.split("(")
    if after_paren.len() >= 2:
        ctx = after_paren[1].split(")")[0].trim()
expect(ctx).to_equal("native")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_categorization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestCategory Auto-Detection
- Explicit Category Annotation
- Speed Annotation Parsing
- Speed Resolution
- Speed Filter Matching
- Manifest V3 Entry Serialization
- CLI Flag Parsing
- Decorator Annotation Parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
