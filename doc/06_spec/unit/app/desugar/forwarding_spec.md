# Forwarding Specification

> Tests covering desugar_forwarding - Phase 2 alias fn/me, desugar_forwarding - Phase 3 alias Trait, desugar_forwarding - DEPRECATED fn name = target, desugar_forwarding - Phase 4 blanket alias.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Forwarding Specification

## Scenarios

### desugar_forwarding - Phase 2 alias fn/me

#### generates fn forwarding for no-arg method

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates fn forwarding for no-arg method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates fn forwarding for no-arg method")
var src = "class Wrapper:" + "\n"
src = src + "    inner: Inner" + "\n"
src = src + "    alias fn len = inner.len" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn len():")
expect(out).to_contain("self.inner.len()")
```

</details>

#### generates fn forwarding with args

- generates fn forwarding with args


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates fn forwarding with args")
var src = "class Wrapper:" + "\n"
src = src + "    inner: Inner" + "\n"
src = src + "    alias fn get(key, default) = inner.get" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn get(key, default):")
expect(out).to_contain("self.inner.get(key, default)")
```

</details>

#### generates me forwarding

- generates me forwarding


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates me forwarding")
var src = "class Wrapper:" + "\n"
src = src + "    inner: Inner" + "\n"
src = src + "    alias me push(item) = inner.push" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("me push(item):")
expect(out).to_contain("self.inner.push(item)")
```

</details>

#### preserves non-alias lines

- preserves non-alias lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves non-alias lines")
var src = "class Wrapper:" + "\n"
src = src + "    inner: Inner" + "\n"
src = src + "    fn own_method() -> i64:" + "\n"
src = src + "        42" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn own_method() -> i64:")
expect(out).to_contain("42")
```

</details>

### desugar_forwarding - Phase 3 alias Trait

#### generates forwarding for trait fn methods

- generates forwarding for trait fn methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates forwarding for trait fn methods")
var src = "trait Sizeable:" + "\n"
src = src + "    fn size() -> i64" + "\n"
src = src + "    fn is_empty() -> bool" + "\n"
src = src + "\n"
src = src + "class MyList:" + "\n"
src = src + "    items: Storage" + "\n"
src = src + "    alias Sizeable = items" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn size():")
expect(out).to_contain("self.items.size()")
expect(out).to_contain("fn is_empty():")
expect(out).to_contain("self.items.is_empty()")
```

</details>

#### generates forwarding for trait me methods

- generates forwarding for trait me methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates forwarding for trait me methods")
var src = "trait Writable:" + "\n"
src = src + "    me write(data: text)" + "\n"
src = src + "    me clear()" + "\n"
src = src + "\n"
src = src + "class Stream:" + "\n"
src = src + "    buf: Buffer" + "\n"
src = src + "    alias Writable = buf" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("me write(data):")
expect(out).to_contain("self.buf.write(data)")
expect(out).to_contain("me clear():")
expect(out).to_contain("self.buf.clear()")
```

</details>

#### skips default methods

- skips default methods
   - Expected: has_ne_forward is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips default methods")
var src = "trait Eq:" + "\n"
src = src + "    fn eq(other: Self) -> bool" + "\n"
src = src + "    fn ne(other: Self) -> bool:" + "\n"
src = src + "        not self.eq(other)" + "\n"
src = src + "\n"
src = src + "class Point:" + "\n"
src = src + "    inner: Coord" + "\n"
src = src + "    alias Eq = inner" + "\n"
val out = desugar_forwarding(src)
# eq is abstract (no default) - should be forwarded
expect(out).to_contain("fn eq(other):")
expect(out).to_contain("self.inner.eq(other)")
# ne has a default - should NOT be forwarded
val has_ne_forward = out.contains("self.inner.ne(")
expect(has_ne_forward).to_equal(false)
```

</details>

#### handles multiple trait aliases on same class

- handles multiple trait aliases on same class


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple trait aliases on same class")
var src = "trait Readable:" + "\n"
src = src + "    fn read() -> text" + "\n"
src = src + "\n"
src = src + "trait Closeable:" + "\n"
src = src + "    me close()" + "\n"
src = src + "\n"
src = src + "class FileStream:" + "\n"
src = src + "    reader: Reader" + "\n"
src = src + "    handle: Handle" + "\n"
src = src + "    alias Readable = reader" + "\n"
src = src + "    alias Closeable = handle" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn read():")
expect(out).to_contain("self.reader.read()")
expect(out).to_contain("me close():")
expect(out).to_contain("self.handle.close()")
```

</details>

#### generates nothing for unknown trait

- generates nothing for unknown trait
   - Expected: has_self_inner is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates nothing for unknown trait")
var src = "class Wrapper:" + "\n"
src = src + "    inner: Inner" + "\n"
src = src + "    alias UnknownTrait = inner" + "\n"
val out = desugar_forwarding(src)
# Should not contain any forwarding methods (trait not found in source)
val has_self_inner = out.contains("self.inner.")
expect(has_self_inner).to_equal(false)
```

</details>

### desugar_forwarding - DEPRECATED fn name = target

#### generates delegation for fn alias with known target

- generates delegation for fn alias with known target


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates delegation for fn alias with known target")
var src = "fn greet(name: text) -> text:" + "\n"
src = src + "    \"Hello, \" + name" + "\n"
src = src + "\n"
src = src + "fn hello = greet" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("DEPRECATED")
expect(out).to_contain("fn hello(name):")
expect(out).to_contain("greet(name)")
```

</details>

#### generates no-arg delegation when target has no params

- generates no-arg delegation when target has no params


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates no-arg delegation when target has no params")
var src = "fn get_value() -> i64:" + "\n"
src = src + "    42" + "\n"
src = src + "\n"
src = src + "fn fetch = get_value" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn fetch():")
expect(out).to_contain("get_value()")
```

</details>

#### does not treat normal functions as aliases

- does not treat normal functions as aliases
   - Expected: has_deprecated is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat normal functions as aliases")
var src = "fn normal(x: i64) -> i64:" + "\n"
src = src + "    x + 1" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn normal(x: i64) -> i64:")
val has_deprecated = out.contains("DEPRECATED")
expect(has_deprecated).to_equal(false)
```

</details>

### desugar_forwarding - Phase 4 blanket alias

#### forwards all methods from field type

- forwards all methods from field type


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards all methods from field type")
var src = "class Storage:" + "\n"
src = src + "    fn size() -> i64:" + "\n"
src = src + "        0" + "\n"
src = src + "    me clear():" + "\n"
src = src + "        0" + "\n"
src = src + "\n"
src = src + "class Wrapper:" + "\n"
src = src + "    store: Storage" + "\n"
src = src + "    alias store" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn size():")
expect(out).to_contain("self.store.size()")
expect(out).to_contain("me clear():")
expect(out).to_contain("self.store.clear()")
```

</details>

#### forwards methods with parameters

- forwards methods with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards methods with parameters")
var src = "class Engine:" + "\n"
src = src + "    fn power(rpm: i64) -> i64:" + "\n"
src = src + "        rpm * 2" + "\n"
src = src + "\n"
src = src + "class Car:" + "\n"
src = src + "    engine: Engine" + "\n"
src = src + "    alias engine" + "\n"
val out = desugar_forwarding(src)
expect(out).to_contain("fn power(rpm):")
expect(out).to_contain("self.engine.power(rpm)")
```

</details>

#### generates nothing for unknown field type

- generates nothing for unknown field type
   - Expected: has_self_inner is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates nothing for unknown field type")
var src = "class Wrapper:" + "\n"
src = src + "    inner: UnknownType" + "\n"
src = src + "    alias inner" + "\n"
val out = desugar_forwarding(src)
# UnknownType not defined in source, so no methods to forward
val has_self_inner = out.contains("self.inner.")
expect(has_self_inner).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/forwarding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering desugar_forwarding - Phase 2 alias fn/me, desugar_forwarding - Phase 3 alias Trait, desugar_forwarding - DEPRECATED fn name = target, desugar_forwarding - Phase 4 blanket alias.
- desugar_forwarding - Phase 2 alias fn/me
- desugar_forwarding - Phase 3 alias Trait
- desugar_forwarding - DEPRECATED fn name = target
- desugar_forwarding - Phase 4 blanket alias

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `9cb51b7b4292efbfa6e30689d54b29da317d9dba75f47d3772a8021bf587aa35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cb51b7b4292efbfa6e30689d54b29da317d9dba75f47d3772a8021bf587aa35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cb51b7b4292efbfa6e30689d54b29da317d9dba75f47d3772a8021bf587aa35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/forwarding_spec.spl
mirror: doc/06_spec/unit/app/desugar/forwarding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/forwarding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/forwarding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/forwarding_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates fn forwarding for no-arg method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/forwarding_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates fn forwarding with args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/forwarding_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates me forwarding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
