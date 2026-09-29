# Option Router Specification

> Tests covering stage0 option router — exact routes, stage0 option router — --x extension split, stage0 option router — argv routing with hard -- boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Router Specification

## Scenarios

### stage0 option router — exact routes

#### routes a flag spelling to its handler route

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes a flag spelling to its handler route


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a flag spelling to its handler route")
val t = _table()
val d = option_router_dispatch_token_v1(t, "--verbose", false)
expect(d.kind).to_be(ROUTER_DISPATCH_EXACT)
expect(d.option_id).to_be("core.verbose")
expect(d.route_index).to_be(0)
expect(d.has_value).to_be(false)
```

</details>

#### routes a valued spelling with =value to the right handler

- routes a valued spelling with =value to the right handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a valued spelling with =value to the right handler")
val t = _table()
val d = option_router_dispatch_token_v1(t, "--opt-level=2", false)
expect(d.kind).to_be(ROUTER_DISPATCH_EXACT)
expect(d.option_id).to_be("core.opt_level")
expect(d.has_value).to_be(true)
expect(d.value).to_be("2")
```

</details>

#### value-mode is enforced: required without = is an error, flag with = is an error

- value-mode is enforced: required without = is an error, flag with = is an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value-mode is enforced: required without = is an error, flag with = is an error")
val t = _table()
expect(option_router_dispatch_token_v1(t, "--opt-level", false).kind).to_be(ROUTER_DISPATCH_ERROR)
expect(option_router_dispatch_token_v1(t, "--verbose=1", false).kind).to_be(ROUTER_DISPATCH_ERROR)
```

</details>

#### unknown exact option is a fail-closed error

- unknown exact option is a fail-closed error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown exact option is a fail-closed error")
val t = _table()
expect(option_router_dispatch_token_v1(t, "--nope", false).kind).to_be(ROUTER_DISPATCH_ERROR)
```

</details>

#### reserved spellings cannot be registered

- reserved spellings cannot be registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reserved spellings cannot be registered")
val t = _table()
val (_, d) = option_router_register_route_v1(t, OptionRouterRouteV1(option_id: "bad", spelling: "--help", value_mode: CLI_VALUE_MODE_FLAG, provider_id: ""))
expect(d.ok).to_be(false)
expect(d.code).to_be(CLI_ROUTE_ERR_RESERVED_SPELLING)
```

</details>

### stage0 option router — --x extension split

#### splits --x<ns>-<key>=<value> into namespace/key/value

- splits --x<ns>-<key>=<value> into namespace/key/value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits --x<ns>-<key>=<value> into namespace/key/value")
val t = _table()
val d = option_router_dispatch_token_v1(t, "--xlog-level=debug", false)
expect(d.kind).to_be(ROUTER_DISPATCH_EXTENSION)
expect(d.namespace).to_be("log")
expect(d.key).to_be("level")
expect(d.value).to_be("debug")
expect(d.has_value).to_be(true)
expect(d.ns_index).to_be(0)
```

</details>

#### flag form --x<ns>-<key> has no value; key may contain dashes

- flag form --x<ns>-<key> has no value; key may contain dashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flag form --x<ns>-<key> has no value; key may contain dashes")
val t = _table()
val d = option_router_dispatch_token_v1(t, "--xlog-color-mode", false)
expect(d.kind).to_be(ROUTER_DISPATCH_EXTENSION)
expect(d.namespace).to_be("log")
expect(d.key).to_be("color-mode")
expect(d.has_value).to_be(false)
```

</details>

#### unknown namespace and malformed --x tokens are fail-closed errors

- unknown namespace and malformed --x tokens are fail-closed errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown namespace and malformed --x tokens are fail-closed errors")
val t = _table()
val d1 = option_router_dispatch_token_v1(t, "--xzz-key", false)
expect(d1.kind).to_be(ROUTER_DISPATCH_ERROR)
expect(d1.error_code).to_be(CLI_ROUTE_ERR_UNKNOWN_NAMESPACE)
val d2 = option_router_dispatch_token_v1(t, "--xlog", false)
expect(d2.kind).to_be(ROUTER_DISPATCH_ERROR)
expect(d2.error_code).to_be(CLI_ROUTE_ERR_BAD_NAMESPACE_SHAPE)
val d3 = option_router_dispatch_token_v1(t, "--x-key", false)
expect(d3.kind).to_be(ROUTER_DISPATCH_ERROR)
```

</details>

### stage0 option router — argv routing with hard -- boundary

#### routes a mixed argv and stops intercepting after --

- routes a mixed argv and stops intercepting after --


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a mixed argv and stops intercepting after --")
val t = _table()
match option_router_route_argv_v1(t, ["--verbose", "--xlog-level=info", "input.spl", "--", "--xlog-level=late"]):
    case Ok(ds):
        expect(ds.len()).to_be(5)
        expect(ds[0].kind).to_be(ROUTER_DISPATCH_EXACT)
        expect(ds[1].kind).to_be(ROUTER_DISPATCH_EXTENSION)
        expect(ds[2].kind).to_be(ROUTER_DISPATCH_POSITIONAL)
        expect(ds[3].kind).to_be(ROUTER_DISPATCH_TERMINATOR)
        expect(ds[4].kind).to_be(ROUTER_DISPATCH_PROGRAM_ARG)
    case Err(e):
        expect(e).to_be("")
```

</details>

#### argv routing is fail-closed on the first bad token

- argv routing is fail-closed on the first bad token


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("argv routing is fail-closed on the first bad token")
val t = _table()
match option_router_route_argv_v1(t, ["--verbose", "--xzz-key"]):
    case Ok(_): expect(true).to_be(false)
    case Err(e): expect(e.contains("unknown namespace")).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/option_router_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stage0 option router — exact routes, stage0 option router — --x extension split, stage0 option router — argv routing with hard -- boundary.
- stage0 option router — exact routes
- stage0 option router — --x extension split
- stage0 option router — argv routing with hard -- boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `c4327906394ac2b8e7fc30aedb375a5b7706778317b5675bd31c3ff355118bb0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4327906394ac2b8e7fc30aedb375a5b7706778317b5675bd31c3ff355118bb0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4327906394ac2b8e7fc30aedb375a5b7706778317b5675bd31c3ff355118bb0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/option_router_spec.spl
mirror: doc/06_spec/01_unit/app/startup/option_router_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/option_router_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/option_router_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/option_router_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a flag spelling to its handler route' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/option_router_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a valued spelling with =value to the right handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/option_router_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'value-mode is enforced: required without = is an error, flag with = is an error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
