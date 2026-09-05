# Dummy-Accessor Auto-Fix

> The `dummy_accessor` / ACC001 lint warns about trivial `get_*`/`set_*`/`is_*` methods that only forward a backing field. This spec covers the auto-fix that rewrites such call sites to direct field access and deletes the wrappers:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dummy-Accessor Auto-Fix

The `dummy_accessor` / ACC001 lint warns about trivial `get_*`/`set_*`/`is_*` methods that only forward a backing field. This spec covers the auto-fix that rewrites such call sites to direct field access and deletes the wrappers:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `dummy_accessor` / ACC001 lint warns about trivial `get_*`/`set_*`/`is_*`
methods that only forward a backing field. This spec covers the auto-fix that
rewrites such call sites to direct field access and deletes the wrappers:

    obj.get_x()   -> obj.x        # getter / predicate -> varname access
    obj.set_x(v)  -> obj.x = v    # setter             -> assignment

## Key Concepts

| Concept | Description |
|---------|-------------|
| tier-1  | Globally-unambiguous name (only ever a dummy): rewrite every call site, delete wrappers. |
| tier-2  | Ambiguous name (a real method shares it): rewrite only `self.`/`me.` calls in the defining class; keep the wrapper. |
| cache invalidation | Both the wrapper-owning file and caller files change content, so the content-hashed compile cache misses stale entries. |

## Scenarios

### dummy accessor detection

#### flags single-statement forwarders as dummy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### does not flag accessors with real behaviour

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classes = parse_accessor_classes(user_source())
expect(classes.len()).to_equal(1)
for m in classes[0].methods:
    expect(m.is_dummy).to_be(false)
```

</details>

### tier-1 cross-file rewrite (unambiguous names)

#### rewrites getters to varname access and setters to assignment, and deletes wrappers

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<text, text> = {}
sources["box.spl"] = box_source()
sources["caller.spl"] = caller_source()
var (out, stats) = apply_accessor_fixes(sources, true)

val box = out["box.spl"]
val caller = out["caller.spl"]

# wrappers deleted
expect(box.contains("fn get_value")).to_be(false)
expect(box.contains("set_value(")).to_be(false)
# backing field and real method survive (class not emptied)
expect(box.contains("value: i64")).to_be(true)
expect(box.contains("me bump():")).to_be(true)
# internal call rewritten
expect(box.contains("self.value = self.value + 1")).to_be(true)
# external calls rewritten
expect(caller.contains("b.value = 10")).to_be(true)
expect(caller.contains("b.value")).to_be(true)
expect(caller.contains("get_value(")).to_be(false)

expect(stats.defs_removed).to_equal(2)
expect(stats.calls_rewritten).to_be_greater_than(2)
```

</details>

### tier-2 same-file rewrite (ambiguous names)

#### keeps the wrapper and only touches self/me calls when a real same-named method exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# second file defines REAL get_value/set_value -> both names ambiguous
var real = "class Other:\n"
real = real + "    cache: i64\n"
real = real + "    fn get_value() -> i64:\n"
real = real + "        self.cache + 1\n"
real = real + "    me set_value(v: i64):\n"
real = real + "        self.cache = v + 1\n"

var sources: Dict<text, text> = {}
sources["box.spl"] = box_source()
sources["caller.spl"] = caller_source()
sources["other.spl"] = real
var (out, stats) = apply_accessor_fixes(sources, true)

val box = out["box.spl"]
val caller = out["caller.spl"]

# ambiguous: wrapper kept, external untyped call NOT rewritten
expect(box.contains("fn get_value")).to_be(true)
expect(caller.contains("b.get_value()")).to_be(true)
# but internal self. call inside the dummy's own class IS simplified
expect(box.contains("self.value")).to_be(true)
expect(stats.defs_removed).to_equal(0)
```

</details>

### expression-context setter safety

#### never rewrites a setter used as an expression, and keeps its wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# set_visible returns/forwards but is used in builder position
var n = "class Node:\n"
n = n + "    visible: bool\n"
n = n + "    me set_visible(v: bool):\n"
n = n + "        self.visible = v\n"
var caller = "fn build(node: Node) -> Node:\n"
caller = caller + "    node.set_visible(true)\n"
caller = caller + "    node = node.set_visible(false)\n"
caller = caller + "    node\n"

var sources: Dict<text, text> = {}
sources["node.spl"] = n
sources["build.spl"] = caller
var (out, stats) = apply_accessor_fixes(sources, true)

val body = out["build.spl"]
# statement-position call simplified
expect(body.contains("node.visible = true")).to_be(true)
# expression-position call left intact (no invalid `node = node.visible = false`)
expect(body.contains("node = node.set_visible(false)")).to_be(true)
expect(body.contains("node.visible = false")).to_be(false)
# wrapper kept because an unrewritable call remains
expect(out["node.spl"].contains("me set_visible")).to_be(true)
expect(stats.defs_removed).to_equal(0)
```

</details>

### impl-block and multi-arg safety

#### does not rewrite a name that has a real method in an impl block

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# class-block dummy get_visible, but a real impl-block method of the same
# name exists elsewhere -> the name must be treated as ambiguous
var dummy = "class Flag:\n    visible: bool\n    fn get_visible() -> bool:\n        self.visible\n"
var impl_real = "struct Canvas:\n    items: i64\nimpl Canvas:\n    fn get_visible(idx: i32) -> bool:\n        idx > 0\n"
var caller = "fn use_it(c: Canvas) -> bool:\n    c.get_visible(1)\n"
var sources: Dict<text, text> = {}
sources["flag.spl"] = dummy
sources["canvas.spl"] = impl_real
sources["caller.spl"] = caller
var (out, stats) = apply_accessor_fixes(sources, true)
# ambiguous: wrapper kept, call untouched
expect(out["flag.spl"].contains("fn get_visible")).to_be(true)
expect(out["caller.spl"].contains("c.get_visible(1)")).to_be(true)
expect(stats.defs_removed).to_equal(0)
```

</details>

#### never rewrites a multi-argument setter call

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snap = "class Mixer:\n    volume: f64\n    me set_volume(v: f64):\n        self.volume = v\n"
var other = "struct Snap:\n    n: i64\nimpl Snap:\n    me set_volume(name: text, level: f64):\n        self.n = level\n"
var caller = "fn drive(s: Snap):\n    s.set_volume(\"music\", 0.3)\n"
var sources: Dict<text, text> = {}
sources["mixer.spl"] = snap
sources["snap.spl"] = other
sources["caller.spl"] = caller
var (out, stats) = apply_accessor_fixes(sources, true)
# set_volume is ambiguous (real 2-arg impl) -> no invalid `s.volume = "music", 0.3`
expect(out["caller.spl"].contains("s.set_volume(\"music\", 0.3)")).to_be(true)
expect(out["caller.spl"].contains("volume = \"music\"")).to_be(false)
```

</details>

### cache invalidation invariant

#### changes content of both wrapper-owning and caller files so hashed cache misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<text, text> = {}
sources["box.spl"] = box_source()
sources["caller.spl"] = caller_source()
var (out, stats) = apply_accessor_fixes(sources, true)
expect(out["box.spl"] == box_source()).to_be(false)
expect(out["caller.spl"] == caller_source()).to_be(false)
expect(stats.files_changed).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c3cecfa4d177f297a0b5672f550ca28a3e3ecc03d5bd89a72be37ff37fa80dd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3cecfa4d177f297a0b5672f550ca28a3e3ecc03d5bd89a72be37ff37fa80dd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3cecfa4d177f297a0b5672f550ca28a3e3ecc03d5bd89a72be37ff37fa80dd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl
mirror: doc/06_spec/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'flags single-statement forwarders as dummy' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl:82:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not flag accessors with real behaviour' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl:89:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rewrites getters to varname access and setters to assignment, and deletes wrappers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl:115:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps the wrapper and only touches self/me calls when a real same-named method exists' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
