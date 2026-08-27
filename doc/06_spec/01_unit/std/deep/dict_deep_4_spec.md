# @manual: primary

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STDLIB Deep-Dive Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STDLIB-DEEP |
| Category | Standard Library Deep Coverage |
| Status | Implemented |
| Source | `test/01_unit/std/deep/dict_deep_4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Dict Deep Coverage

#### reads back a value stored under a key

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads back a value stored under a key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads back a value stored under a key")
val d = {"a": 1}
check(d["a"] == 1)
```

</details>

#### keeps distinct keys distinct

- keeps distinct keys distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps distinct keys distinct")
val d = {"a": 1, "b": 2}
check(d["a"] == 1 and d["b"] == 2)
```

</details>

#### reports key presence and absence

- reports key presence and absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports key presence and absence")
val d = {"a": 1, "b": 2}
check(d.contains_key("a"))
check(not d.contains_key("zzz"))
```

</details>

#### counts keys via keys().len()

- counts keys via keys().len()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts keys via keys().len()")
val d = {"a": 1, "b": 2, "c": 3}
check(d.keys().len() == 3)
```

</details>

#### an empty dict has no keys and reports no membership

- an empty dict has no keys and reports no membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty dict has no keys and reports no membership")
val d = {}
check(d.keys().len() == 0)
check(not d.contains_key("a"))
```

</details>

#### a later duplicate key overwrites the earlier value

- a later duplicate key overwrites the earlier value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a later duplicate key overwrites the earlier value")
val d = {"k": 1, "k": 2}
check(d["k"] == 2)
check(d.keys().len() == 1)
```

</details>

#### distinguishes a stored zero from an absent key

- distinguishes a stored zero from an absent key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes a stored zero from an absent key")
val d = {"z": 0}
check(d["z"] == 0)
check(d.contains_key("z"))
check(not d.contains_key("missing"))
```

</details>

#### keys are case sensitive

- keys are case sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys are case sensitive")
val d = {"a": 1, "A": 2}
check(d["a"] == 1)
check(d["A"] == 2)
check(d.keys().len() == 2)
```

</details>

#### handles an empty-string key

- handles an empty-string key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles an empty-string key")
val d = {"": 7}
check(d[""] == 7)
check(d.contains_key(""))
```

</details>

#### stores text values, not just integers

- stores text values, not just integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores text values, not just integers")
val d = {"name": "simple"}
check(d["name"] == "simple")
```

</details>

#### every inserted key appears in keys()

- every inserted key appears in keys()


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every inserted key appears in keys()")
val d = {"a": 1, "b": 2, "c": 3}
var seen = 0
for k in d.keys():
    if d.contains_key(k):
        seen = seen + 1
check(seen == 3)
```

</details>

#### arr 1

- arr 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arr 1")

val a = [1,2,3]
check(a.len() == 3)
```

</details>

#### arr 2

- arr 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arr 2")
val a = []
check(a.len() == 0)
```

</details>

#### arr 3

- arr 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arr 3")
val a = [1, 2, 3]
check(a.len() == 3)
```

</details>

#### arr 4

- arr 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arr 4")
val a = [1,2,3]
check(a.len() == 3)
```

</details>

#### arr 5

- arr 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arr 5")
var a = [1,2]
val b = a.append(3)
check(b.len() == 3)
```

</details>

#### str 1

- str 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("str 1")

check("".len() == 0)
```

</details>

#### str 2

- str 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("str 2")
check("a".len() == 1)
```

</details>

#### str 3

- str 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("str 3")
check("test".len() == 4)
```

</details>

#### str 4

- str 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("str 4")
check("hello".contains("ell"))
```

</details>

#### str 5

- str 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("str 5")
check("test".starts_with("te"))
```

</details>

#### str 6

- str 6


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("str 6")
check("test".ends_with("st"))
```

</details>

#### opt 1

- opt 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opt 1")

val o = Some(1)
check(o.?)
```

</details>

#### opt 2

- opt 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opt 2")
val o = nil
check(not o.?)
```

</details>

#### opt 3

- opt 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opt 3")
val o = Some(42)
check(o? == 42)
```

</details>

#### opt 4

- opt 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opt 4")
val o = nil
check((o ?? 99) == 99)
```

</details>

#### dict 1

- dict 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict 1")

val d = {"a": 1}
check(d["a"] == 1)
```

</details>

#### dict 2

- dict 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict 2")
# was: `val d = {}` then `check(true)` — bound the dict and then
# ignored it, asserting a constant instead.
val d = {}
check(d.keys().len() == 0)
```

</details>

#### dict 3

- dict 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict 3")
val d = {"a": 1, "b": 2}
check(d["a"] == 1)
```

</details>

#### if 1

- if 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if 1")

if true:
    check(true)
else:
    check(false)
```

</details>

#### if 2

- if 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if 2")
if false:
    check(false)
else:
    check(true)
```

</details>

#### if 3

- if 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if 3")
val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### for 1

- for 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for 1")

var c = 0
for i in 0..5:
    c = c + 1
check(c == 5)
```

</details>

#### for 2

- for 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for 2")

var s = 0
for i in 0..10:
    s = s + i
check(s == 45)
```

</details>

#### match 1

- match 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match 1")

match Some(1):
    Some(x): check(x == 1)
    nil: check(false)
```

</details>

#### match 2

- match 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match 2")

match nil:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### nested 1

- nested 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested 1")

# was: `check(true)` in the inner loop — the loops ran but nothing
# about them was observed. Now the iteration count is the assertion.
var n = 0
for i in 0..3:
    for j in 0..3:
        n = n + 1
check(n == 9)
```

</details>

#### complex 1

- complex 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex 1")

</details>

#### text concat slice reverse

- Verify: text concat slice reverse
   - Expected: "abc" + "def" equals `abcdef`
   - Expected: "abc".slice(1) equals `bc`
   - Expected: "abc".reverse() equals `cba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DICT-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-DICT-DEEP-c958
step("Verify: text concat slice reverse")
# oracle: "abcdef"/"bc"/"cba" — concat, slice from index 1, reverse
expect("abc" + "def").to_equal("abcdef")
expect("abc".slice(1)).to_equal("bc")
expect("abc".reverse()).to_equal("cba")
```

</details>

#### array sort

- Verify: array sort
   - Expected: [3, 1, 2].sorted() equals `[1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DICT-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-DICT-DEEP-c958
step("Verify: array sort")
# oracle: [1, 2, 3] — sorted() returns ascending order
expect([3, 1, 2].sorted()).to_equal([1, 2, 3])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
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

- Canonical SPipe generation for source `7c32ceda151a177e6cff8d3e67b0b864cbe2426eade1a24a7fa3682fc01e1cdd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c32ceda151a177e6cff8d3e67b0b864cbe2426eade1a24a7fa3682fc01e1cdd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c32ceda151a177e6cff8d3e67b0b864cbe2426eade1a24a7fa3682fc01e1cdd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/deep/dict_deep_4_spec.spl
mirror: doc/06_spec/01_unit/std/deep/dict_deep_4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/deep/dict_deep_4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/deep/dict_deep_4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/deep/dict_deep_4_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads back a value stored under a key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/deep/dict_deep_4_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps distinct keys distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/deep/dict_deep_4_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports key presence and absence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
