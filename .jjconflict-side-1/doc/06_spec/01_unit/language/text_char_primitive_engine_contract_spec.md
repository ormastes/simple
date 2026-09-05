# text_char_primitive_engine_contract_spec

> As a Simple developer walking text by codepoint,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text_char_primitive_engine_contract_spec

As a Simple developer walking text by codepoint,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/text_char_primitive_engine_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a Simple developer walking text by codepoint,
    I want `.chr()`, `char_at` over-run and single-character integer casts
    to mean the same thing whichever engine runs my program,
    so that a loop that terminates under the interpreter does not run past
    the end of the string once it is compiled.

## Scenarios

### text codepoint primitives agree across engines

#### chr builds an ASCII character from its code point

- chr builds an ASCII character from its code point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chr builds an ASCII character from its code point")
assert_equal((97).chr(), "a")
```

</details>

#### chr builds a 2-byte character from its code point

- chr builds a 2-byte character from its code point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chr builds a 2-byte character from its code point")
assert_equal((233).chr(), "é")
```

</details>

#### to_char is the same builtin as chr and handles 3-byte code points

- to_char is the same builtin as chr and handles 3-byte code points


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_char is the same builtin as chr and handles 3-byte code points")
assert_equal((8364).to_char(), "€")
```

</details>

#### char_at past the byte length yields empty text

- char_at past the byte length yields empty text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("char_at past the byte length yields empty text")
val s = "Café"
assert_equal(s.char_at(99), "")
```

</details>

#### char_at past the codepoint count yields empty text

- char_at past the codepoint count yields empty text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("char_at past the codepoint count yields empty text")
# "Café" is 5 bytes but 4 codepoints, so index 4 clears the byte-length
# fast reject and lands on the real character bound.
val s = "Café"
assert_equal(s.char_at(4), "")
```

</details>

#### the empty-text break idiom terminates on the first over-run index

- the empty-text break idiom terminates on the first over-run index


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the empty-text break idiom terminates on the first over-run index")
val s = "Café"
var seen = 0
var i = 0
while i < 99:
    val ch = s.char_at(i)
    if ch == "":
        break
    seen = seen + 1
    i = i + 1
assert_equal(seen, 4)
```

</details>

#### casting a 1-byte character to i64 gives its code point

- casting a 1-byte character to i64 gives its code point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("casting a 1-byte character to i64 gives its code point")
val s = "Café"
assert_equal(s.char_at(0) as i64, 67)
```

</details>

#### casting a 2-byte character to i64 gives its code point

- casting a 2-byte character to i64 gives its code point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("casting a 2-byte character to i64 gives its code point")
val s = "Café"
assert_equal(s.char_at(3) as i64, 233)
```

</details>

#### casting a 3-byte character to i64 gives its code point

- casting a 3-byte character to i64 gives its code point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("casting a 3-byte character to i64 gives its code point")
val e = "€"
assert_equal(e.char_at(0) as i64, 8364)
```

</details>

#### chr and the integer cast round-trip

- chr and the integer cast round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chr and the integer cast round-trip")
assert_equal((233).chr().char_at(0) as i64, 233)
```

</details>

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

- Canonical SPipe generation for source `f0f54eb55df2036cd2e1f66538099dfc49a0bba2900316f9d08fc733609aa17a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0f54eb55df2036cd2e1f66538099dfc49a0bba2900316f9d08fc733609aa17a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0f54eb55df2036cd2e1f66538099dfc49a0bba2900316f9d08fc733609aa17a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/text_char_primitive_engine_contract_spec.spl
mirror: doc/06_spec/01_unit/language/text_char_primitive_engine_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/text_char_primitive_engine_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/text_char_primitive_engine_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/text_char_primitive_engine_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chr builds an ASCII character from its code point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/text_char_primitive_engine_contract_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chr builds a 2-byte character from its code point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/text_char_primitive_engine_contract_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'to_char is the same builtin as chr and handles 3-byte code points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
