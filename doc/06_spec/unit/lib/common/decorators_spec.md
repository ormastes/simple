# decorators_spec

> Purpose: Prove that CachedFunction wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# decorators_spec

Purpose: Prove that CachedFunction wrapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/decorators_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CachedFunction wrapper.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### CachedFunction wrapper

#### caches function results

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- caches function results
- Verify: caches function results
   - Expected: result1 equals `25`
   - Expected: result2 equals `25`
   - Expected: info["hits"] equals `1`
   - Expected: info["misses"] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches function results")
step("Verify: caches function results")
# @req: REQ-LIB-COMMON-001
fn square(x):
    return x * x

# Create cached version
val wrapper = cached(square)

# First call should miss cache
val result1 = wrapper.__call__(5)
expect(result1).to_equal(25)  # oracle: 25 — named expected value from the requirement

# Second call should hit cache
val result2 = wrapper.__call__(5)
expect(result2).to_equal(25)  # oracle: 25 — named expected value from the requirement

# Check cache stats
val info = wrapper.cache_info()
expect(info["hits"]).to_equal(1)
expect(info["misses"]).to_equal(1)
```

</details>

#### caches different arguments separately

- caches different arguments separately
- Verify: caches different arguments separately
   - Expected: result1 equals `5`
   - Expected: result2 equals `9`
   - Expected: result3 equals `5`
   - Expected: info["hits"] equals `1`
   - Expected: info["misses"] equals `2`
   - Expected: info["size"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches different arguments separately")
step("Verify: caches different arguments separately")
fn add(a, b):
    return a + b

val wrapper = cached(add)

val result1 = wrapper.__call__(2, 3)
expect(result1).to_equal(5)  # oracle: 5 — named expected value from the requirement

val result2 = wrapper.__call__(4, 5)
expect(result2).to_equal(9)  # oracle: 9 — named expected value from the requirement

val result3 = wrapper.__call__(2, 3)
expect(result3).to_equal(5)  # oracle: 5 — named expected value from the requirement

val info = wrapper.cache_info()
expect(info["hits"]).to_equal(1)
expect(info["misses"]).to_equal(2)
expect(info["size"]).to_equal(2)
```

</details>

#### clears cache correctly

- clears cache correctly
- Verify: clears cache correctly
   - Expected: info1["hits"] equals `1`
   - Expected: info2["hits"] equals `0`
   - Expected: info2["misses"] equals `0`
   - Expected: info2["size"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears cache correctly")
step("Verify: clears cache correctly")
fn double(x):
    return x * 2

val wrapper = cached(double)

wrapper.__call__(5)
wrapper.__call__(5)

val info1 = wrapper.cache_info()
expect(info1["hits"]).to_equal(1)

wrapper.clear_cache()

val info2 = wrapper.cache_info()
expect(info2["hits"]).to_equal(0)
expect(info2["misses"]).to_equal(0)
expect(info2["size"]).to_equal(0)
```

</details>

### LoggedFunction wrapper

#### logs function calls

- logs function calls
- Verify: logs function calls
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs function calls")
step("Verify: logs function calls")
fn multiply(x, y):
    return x * y

val wrapper = logged(multiply)
val result = wrapper.__call__(3, 4)

# Should log input and output
# Note: output goes to stdout, we just verify it doesn't error
expect(result).to_equal(12)  # oracle: 12 — named expected value from the requirement
```

</details>

#### logs return values

- logs return values
- Verify: logs return values
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs return values")
step("Verify: logs return values")
fn get_value():
    return 42

val wrapper = logged(get_value)
val result = wrapper.__call__()

expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### DeprecatedFunction wrapper

#### shows warning when called

- shows warning when called
- Verify: shows warning when called
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows warning when called")
step("Verify: shows warning when called")
fn old_api(x):
    return x + 1

val wrapper = deprecated(old_api, "Old API")

# First call should print warning
val result = wrapper.__call__(5)
expect(result).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### includes replacement message

- includes replacement message
- Verify: includes replacement message
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes replacement message")
step("Verify: includes replacement message")
fn legacy_function(x):
    return x * 2

val wrapper = deprecated(legacy_function, "Use new_function() instead")

val result = wrapper.__call__(10)
expect(result).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2b3a9b1d11abd383480888d262f2ddb9d1d0a425696954861f785855d0c46c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2b3a9b1d11abd383480888d262f2ddb9d1d0a425696954861f785855d0c46c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2b3a9b1d11abd383480888d262f2ddb9d1d0a425696954861f785855d0c46c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/decorators_spec.spl
mirror: doc/06_spec/unit/lib/common/decorators_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/decorators_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/decorators_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/decorators_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/decorators_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches function results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/decorators_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches different arguments separately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/decorators_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears cache correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
