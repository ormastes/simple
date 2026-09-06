# Custom Literals Specification

> Tests covering Custom String Literal Suffixes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Literals Specification

## Scenarios

### Custom String Literal Suffixes

#### default suffix-to-type mapping

#### maps _ip to IP.from() when IP class is defined

- maps _ip to IP.from() when IP class is defined


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps _ip to IP.from() when IP class is defined")
class IP:
    value: text

    static fn from(s: text) -> IP:
        IP(value: s)

val addr = "192.168.1.1"_ip
expect addr.value == "192.168.1.1"
```

</details>

#### maps snake_case suffix to PascalCase type

- maps snake_case suffix to PascalCase type


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps snake_case suffix to PascalCase type")
class MyType:
    data: text

    static fn from(s: text) -> MyType:
        MyType(data: s)

val obj = "hello"_my_type
expect obj.data == "hello"
```

</details>

#### maps short suffix to UPPERCASE first (common acronyms)

- maps short suffix to UPPERCASE first (common acronyms)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps short suffix to UPPERCASE first (common acronyms)")
class URL:
    link: text

    static fn from(s: text) -> URL:
        URL(link: s)

val link = "https://example.com"_url
expect link.link == "https://example.com"
```

</details>

#### maps longer suffix to PascalCase

- maps longer suffix to PascalCase


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps longer suffix to PascalCase")
class Regex:
    pattern: text

    static fn from(s: text) -> Regex:
        Regex(pattern: s)

val r = "test.*"_regex
expect r.pattern == "test.*"
```

</details>

#### multiple type name candidates

#### tries UPPERCASE before PascalCase for 2-letter suffix

- tries UPPERCASE before PascalCase for 2-letter suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tries UPPERCASE before PascalCase for 2-letter suffix")
class IP:
    v: text
    static fn from(s: text) -> IP:
        IP(v: "IP:" + s)

val addr = "127.0.0.1"_ip
expect addr.v == "IP:127.0.0.1"
```

</details>

#### tries UPPERCASE before PascalCase for 3-letter suffix

- tries UPPERCASE before PascalCase for 3-letter suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tries UPPERCASE before PascalCase for 3-letter suffix")
class XML:
    content: text
    static fn from(s: text) -> XML:
        XML(content: s)

val doc = "<root/>"_xml
expect doc.content == "<root/>"
```

</details>

#### uses PascalCase for 4+ letter suffix

- uses PascalCase for 4+ letter suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses PascalCase for 4+ letter suffix")
class Json:
    data: text
    static fn from(s: text) -> Json:
        Json(data: s)

val j = '{"key": "value"}'_json
expect j.data == '{"key": "value"}'
```

</details>

#### suffix matching is case-sensitive

#### ip maps to IP not Ip

- ip maps to IP not Ip


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ip maps to IP not Ip")
class IP:
    v: text
    static fn from(s: text) -> IP:
        IP(v: s)

val a = "test"_ip
expect a.v == "test"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/custom_literals_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Custom String Literal Suffixes.
- Custom String Literal Suffixes

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

- Canonical SPipe generation for source `437a64d8de2f40f2c7bb82e8c99a164c30e174cbba6925661ef7c62cf52eb881`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `437a64d8de2f40f2c7bb82e8c99a164c30e174cbba6925661ef7c62cf52eb881`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `437a64d8de2f40f2c7bb82e8c99a164c30e174cbba6925661ef7c62cf52eb881`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/custom_literals_spec.spl
mirror: doc/06_spec/unit/lib/common/custom_literals_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/custom_literals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/custom_literals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/custom_literals_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps _ip to IP.from() when IP class is defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/custom_literals_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps snake_case suffix to PascalCase type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/custom_literals_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps short suffix to UPPERCASE first (common acronyms)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
