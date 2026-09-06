# Capability-Based Effects Specification

> This spec covers Simple's capability-based effect system, which statically tracks and enforces which effects (I/O, network, filesystem, pure computation) a function can perform. Capabilities are granted by callers and threaded through the call graph.

<!-- sdn-diagram:id=capability_effects_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_effects_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_effects_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_effects_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability-Based Effects Specification

This spec covers Simple's capability-based effect system, which statically tracks and enforces which effects (I/O, network, filesystem, pure computation) a function can perform. Capabilities are granted by callers and threaded through the call graph.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #140-165 |
| Category | Other |
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | capability_effects.md |
| Source | `test/03_system/feature/language/capability_effects_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec covers Simple's capability-based effect system, which statically
tracks and enforces which effects (I/O, network, filesystem, pure computation)
a function can perform. Capabilities are granted by callers and threaded
through the call graph.

Tests use local doubles to model capability grant/revoke, effect requirement
checking, propagation rules, and the distinction between pure and effectful
functions.

## Syntax

Declare effects a function requires:

    fn read_file(path: text) -> text requires fs:
        ...

    fn fetch_url(url: text) -> text requires net:
        ...

    fn add(a: i64, b: i64) -> i64:   # pure — no annotation needed
        a + b

Grant capabilities at a call site:

    with capabilities [io, net]:
        val page = fetch_url("http://example.com")

## Examples

    # Each effect type maps to a required capability
    required_capability("io")   # => "io"
    required_capability("net")  # => "net"
    required_capability("fs")   # => "fs"
    required_capability("pure") # => ""  (pure needs no grant)

    # Grant, check, revoke
    val cap = Capability.new("io")
    cap.grant()
    cap.is_granted()  # => true
    cap.revoke()
    cap.is_granted()  # => false

    # Effect set composition
    val effects = EffectSet.new()
    effects.add("io")
    effects.add("net")
    effects.requires("io")  # => true
    effects.is_pure()        # => false

## Key Concepts

**Capability** — an unforgeable token that grants permission to perform a
specific effect. Only code that holds the capability can invoke the effect.

**Effect** — a named category of side effect: `io`, `net`, `fs`, `alloc`,
`gpu`, or `pure`. Effect annotations appear in function signatures and are
checked at call sites.

**Propagation** — effects propagate transitively. If `f` calls `g` which
requires `net`, then `f` also requires `net` unless it holds or attenuates
the capability internally.

**Attenuation** — a holder can pass a restricted sub-capability to a callee
(e.g., read-only `fs` from a read-write `fs` capability).

**Pure functions** — functions with no effect annotations are pure; they
can be called anywhere including `const` contexts and spec evaluations.

**Effect polymorphism** — generic functions can quantify over effects:

    fn run<E>(action: fn() -> T requires E) -> T requires E:
        action()

This lets higher-order functions remain effect-transparent.

## Common Patterns

Effect-safe resource acquisition (capability required only inside scope):

    fn read_config() -> Config requires fs:
        val text = fs.read("config.sdn")
        Config.parse(text)

Effect-stripping via sandbox (drop to pure after consuming effect):

    fn cached_read(key: text) -> text:
        val raw = sandbox(fs) { fs.read(key) }
        raw.trim()

Checking effect membership at compile time:

    fn send_report(data: Report) requires io + net:
        net.post("/api/report", data.to_json())
        io.println("sent")

## Scenarios

### Capability Effects Spec

#### features_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = CapabilityContext.with_caps(["io"])
expect(module.can_call("io")).to_equal(true)
expect(module.can_call("net")).to_equal(false)
```

</details>

#### features_capability_inheritance

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CapabilityContext.with_caps(["io", "fs"])
val child = CapabilityContext.with_caps(["net"])
val merged = child.inherit_from(parent)
expect(merged.has("io")).to_equal(true)
expect(merged.has("fs")).to_equal(true)
expect(merged.has("net")).to_equal(true)
```

</details>

#### features_effect_annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure = EffectSignature.pure("parse")
val io = EffectSignature.io("read")
expect(pure.is_pure()).to_equal(true)
expect(io.is_pure()).to_equal(false)
expect(io.required_capability()).to_equal("io")
```

</details>

#### features_effect_inference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inferred = infer_effect(["pure", "io", "pure"])
expect(inferred).to_equal("io")
```

</details>

#### features_pure_by_default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inferred = normalize_effect("")
expect(inferred).to_equal("pure")
```

</details>

#### features_effect_propagation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure_module = CapabilityContext.new()
expect(pure_module.can_call("pure")).to_equal(true)
expect(pure_module.can_call("io")).to_equal(false)
```

</details>

#### features_capability_requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = CapabilityContext.with_caps(["io", "net"])
expect(generic_bound_allows(module, "io")).to_equal(true)
expect(generic_bound_allows(module, "fs")).to_equal(false)
```

</details>

#### features_generic_effect_constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = CapabilityContext.with_caps(["net"])
expect(generic_bound_allows(module, "net")).to_equal(true)
expect(generic_bound_allows(module, "io")).to_equal(false)
```

</details>

#### features_error_messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val message = missing_capability_message("net")
expect(message).to_equal("missing capability: net")
```

</details>

#### features_effect_mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure = EffectSignature.pure("render")
val io = EffectSignature.io("read")
expect(pure.can_run_in(CapabilityContext.new())).to_equal(true)
expect(io.can_run_in(CapabilityContext.new())).to_equal(false)
```

</details>

#### features_11

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = CapabilityContext.new()
expect(module.can_call("fs")).to_equal(false)
expect(module.can_call("pure")).to_equal(true)
```

</details>

#### features_stdlib_effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val io_module = CapabilityContext.with_caps(["io"])
val pure_module = CapabilityContext.new()
expect(stdlib_read(io_module)).to_equal(true)
expect(stdlib_format(pure_module)).to_equal(true)
```

</details>

#### examples_pure_module

1. report record
2. report record
   - Expected: report.pure_calls equals `1`
   - Expected: report.impure_calls equals `1`
   - Expected: report.mismatches equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = CapabilityReport.new()
report.record("pure", true)
report.record("io", false)
expect(report.pure_calls).to_equal(1)
expect(report.impure_calls).to_equal(1)
expect(report.mismatches).to_equal(1)
```

</details>

#### examples_io_boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val io_module = CapabilityContext.with_caps(["io"])
expect(boundary_roundtrip(io_module)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
