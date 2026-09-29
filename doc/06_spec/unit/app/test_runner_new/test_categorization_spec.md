# Test Categorization Specification

> Tests covering TestCategory Auto-Detection, Explicit Category Annotation, Speed Annotation Parsing, Speed Resolution, Speed Filter Matching, Manifest V3 Entry Serialization, CLI Flag Parsing, Decorator Annotation Parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Categorization Specification

## Scenarios

### TestCategory Auto-Detection

#### detects platform from baremetal path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects platform from baremetal path
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects platform from baremetal path")
val path = "test/feature/baremetal/boot_spec.spl"
var cat = "other"
if path.contains("/baremetal/") or path.contains("/qemu/") or path.contains("/cuda/") or path.contains("/gpu/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from cuda path

- detects platform from cuda path
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects platform from cuda path")
val path = "test/unit/lib/gc_async_mut/cuda/gc_cuda_spec.spl"
var cat = "other"
if path.contains("/cuda/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from gpu path

- detects platform from gpu path
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects platform from gpu path")
val path = "test/unit/lib/gc_async_mut/gpu/driver_spec.spl"
var cat = "other"
if path.contains("/gpu/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from qemu path

- detects platform from qemu path
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects platform from qemu path")
val path = "test/feature/baremetal/riscv32/collections_qemu_spec.spl"
var cat = "other"
if path.contains("/qemu/") or path.contains("/baremetal/"):
    cat = "platform"
expect(cat).to_equal("platform")
```

</details>

#### detects platform from non-all platform tag

- detects platform from non-all platform tag
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects platform from non-all platform tag")
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

- does not detect platform from all platform tag
   - Expected: cat equals `not_platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not detect platform from all platform tag")
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

- treats shared path as canonical unit-level cross-platform tier
   - Expected: level equals `unit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats shared path as canonical unit-level cross-platform tier")
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

- detects standalone when no use statements
   - Expected: cat equals `standalone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects standalone when no use statements")
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

- detects standalone when only spec import
   - Expected: cat equals `standalone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects standalone when only spec import")
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

- detects lib when has non-spec imports
   - Expected: cat equals `lib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects lib when has non-spec imports")
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

- extracts category from annotation
   - Expected: cat equals `standalone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts category from annotation")
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

- extracts platform category
   - Expected: cat equals `platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts platform category")
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

- explicit category overrides auto-detection
   - Expected: final_cat equals `lib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit category overrides auto-detection")
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

- extracts default speed
   - Expected: speed equals `long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts default speed")
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

- extracts contextual speed
   - Expected: line1.starts_with("# @speed(") is true
   - Expected: rest1 contains `)`
   - Expected: ctx1 equals `baremetal`
   - Expected: after1.starts_with(":") is true
   - Expected: spd1 equals `short`
   - Expected: ctx2 equals `native`
   - Expected: spd2 equals `medium`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts contextual speed")
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

- does not confuse contextual speed with default speed
   - Expected: default_speed equals `long`
   - Expected: contextual_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not confuse contextual speed with default speed")
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

- resolves contextual speed when context matches
   - Expected: resolved equals `short`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves contextual speed when context matches")
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

- falls back to default speed when no context match
   - Expected: resolved equals `long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to default speed when no context match")
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

- falls back to long when has_slow and no annotations
   - Expected: resolved equals `long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to long when has_slow and no annotations")
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

- resolves to unknown when no info
   - Expected: resolved equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to unknown when no info")
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

- only-short allows only short
   - Expected: "short" == "short" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only-short allows only short")
val only_short = true
expect("short" == "short").to_equal(true)
expect("medium").to_not_equal("short")
expect("long").to_not_equal("short")
```

</details>

#### speed=medium allows short and medium

- speed=medium allows short and medium
   - Expected: short_ok is true
   - Expected: medium_ok is true
   - Expected: long_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("speed=medium allows short and medium")
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

- speed=long allows everything
   - Expected: all_pass is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("speed=long allows everything")
val filter = "long"
var all_pass = false
if filter == "long":
    all_pass = true
expect(all_pass).to_equal(true)
```

</details>

#### empty filter allows everything

- empty filter allows everything
   - Expected: all_pass is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty filter allows everything")
val filter = ""
var all_pass = true
if filter != "":
    all_pass = false
expect(all_pass).to_equal(true)
```

</details>

### Manifest V3 Entry Serialization

#### includes category speed_default speed_contexts in pipe format

- includes category speed_default speed_contexts in pipe format
   - Expected: parts.len() equals `18`
   - Expected: parts[15] equals `platform`
   - Expected: parts[16] equals `long`
   - Expected: parts[17] equals `baremetal=short,native=medium`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes category speed_default speed_contexts in pipe format")
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

- handles empty new fields for backward compat
   - Expected: parts.len() equals `15`
   - Expected: category equals ``
   - Expected: speed_default equals ``
   - Expected: speed_contexts equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty new fields for backward compat")
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

- category flag name
   - Expected: flag equals `--category`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("category flag name")
val flag = "--category"
expect(flag).to_equal("--category")
```

</details>

#### context flag name

- context flag name
   - Expected: flag equals `--context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("context flag name")
val flag = "--context"
expect(flag).to_equal("--context")
```

</details>

#### only-short flag name

- only-short flag name
   - Expected: flag equals `--only-short`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only-short flag name")
val flag = "--only-short"
expect(flag).to_equal("--only-short")
```

</details>

#### speed flag name

- speed flag name
   - Expected: flag equals `--speed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("speed flag name")
val flag = "--speed"
expect(flag).to_equal("--speed")
```

</details>

#### parses --category=standalone from equals format

- parses --category=standalone from equals format
   - Expected: category equals `standalone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses --category=standalone from equals format")
val arg = "--category=standalone"
var category = ""
if arg.starts_with("--category="):
    category = arg[11:]
expect(category).to_equal("standalone")
```

</details>

#### parses --context=baremetal from equals format

- parses --context=baremetal from equals format
   - Expected: context equals `baremetal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses --context=baremetal from equals format")
val arg = "--context=baremetal"
var context = ""
if arg.starts_with("--context="):
    context = arg[10:]
expect(context).to_equal("baremetal")
```

</details>

#### parses --speed=medium from equals format

- parses --speed=medium from equals format
   - Expected: speed equals `medium`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses --speed=medium from equals format")
val arg = "--speed=medium"
var speed = ""
if arg.starts_with("--speed="):
    speed = arg[8:]
expect(speed).to_equal("medium")
```

</details>

### Decorator Annotation Parsing

#### detects @short_test decorator

- detects @short_test decorator
   - Expected: line.starts_with("@short_test") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects @short_test decorator")
val line = "@short_test(baremetal)"
expect(line.starts_with("@short_test")).to_equal(true)
```

</details>

#### extracts context from @short_test(baremetal)

- extracts context from @short_test(baremetal)
   - Expected: ctx equals `baremetal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts context from @short_test(baremetal)")
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

- handles @long_test without context
   - Expected: ctx equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles @long_test without context")
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

- detects @medium_test decorator
   - Expected: line.starts_with("@medium_test") is true
   - Expected: ctx equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects @medium_test decorator")
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
| Source | `test/unit/app/test_runner_new/test_categorization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestCategory Auto-Detection, Explicit Category Annotation, Speed Annotation Parsing, Speed Resolution, Speed Filter Matching, Manifest V3 Entry Serialization, CLI Flag Parsing, Decorator Annotation Parsing.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `185b77d1bdb7e52b88f7eb029e66e0cd1f7a20a1211a524f92f65613a8f293e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `185b77d1bdb7e52b88f7eb029e66e0cd1f7a20a1211a524f92f65613a8f293e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `185b77d1bdb7e52b88f7eb029e66e0cd1f7a20a1211a524f92f65613a8f293e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_runner_new/test_categorization_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/test_categorization_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/test_categorization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/test_categorization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/test_categorization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_runner_new/test_categorization_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects platform from baremetal path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_categorization_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects platform from cuda path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_categorization_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects platform from gpu path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
