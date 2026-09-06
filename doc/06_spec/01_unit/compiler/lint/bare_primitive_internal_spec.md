# bare_primitive_internal_spec

> Firmware-style rule: even internal locals carry domain types in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bare_primitive_internal_spec

Firmware-style rule: even internal locals carry domain types in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/bare_primitive_internal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## No bare primitives in internal code (REQ-SSPEC-COMPILER)

    Firmware-style rule: even internal locals carry domain types in
    mission-critical packages. Bare literals and primitive annotations
    are flagged at warn level under the mission-critical profile.

## Scenarios

### W-MC-VAL-001: bare primitive internal bindings

#### when a binding is a bare literal with no type information

#### warns on a bare integer literal val

- warns on a bare integer literal val
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `W-MC-VAL-001`
   - Expected: findings[0].name equals `x`
   - Expected: findings[0].line_num equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a bare integer literal val")
val source = "fn f():\n    val x = 1\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].code).to_equal("W-MC-VAL-001")
expect(findings[0].name).to_equal("x")
expect(findings[0].line_num).to_equal(2)
```

</details>

#### warns on a bare bool literal var

- warns on a bare bool literal var
   - Expected: findings.len() equals `1`
   - Expected: findings[0].name equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a bare bool literal var")
val source = "fn f():\n    var y = true\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].name).to_equal("y")
```

</details>

#### warns on a bare float literal

- warns on a bare float literal
   - Expected: findings.len() equals `1`
   - Expected: findings[0].name equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a bare float literal")
val source = "fn f():\n    val r = 1.5\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].name).to_equal("r")
```

</details>

#### warns on a digit-separator literal (1_000 is still bare)

- warns on a digit-separator literal (1_000 is still bare)
   - Expected: findings.len() equals `1`
   - Expected: findings[0].name equals `big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a digit-separator literal (1_000 is still bare)")
val source = "fn f():\n    val big = 1_000\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].name).to_equal("big")
```

</details>

#### when a binding has an explicit primitive annotation

#### warns on a primitive-table annotation even with an initializer

- warns on a primitive-table annotation even with an initializer
   - Expected: findings.len() equals `1`
   - Expected: findings[0].name equals `t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a primitive-table annotation even with an initializer")
val source = "fn f():\n    val t: i64 = 1\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].name).to_equal("t")
```

</details>

#### warns on a bool annotation (bool IS in the primitive table)

- warns on a bool annotation (bool IS in the primitive table)
   - Expected: findings.len() equals `1`
   - Expected: findings[0].name equals `flag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a bool annotation (bool IS in the primitive table)")
val source = "fn f():\n    var flag: bool = compute()\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].name).to_equal("flag")
```

</details>

#### when the binding carries a domain type

#### does not warn on a domain-type annotation

- does not warn on a domain-type annotation
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on a domain-type annotation")
val source = "fn f():\n    val t: DurationMs = 1\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn on a unit-suffix literal

- does not warn on a unit-suffix literal
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on a unit-suffix literal")
val source = "fn f():\n    val d = 250_ms\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn on a short unit suffix

- does not warn on a short unit suffix
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on a short unit suffix")
val source = "fn f():\n    val d = 1_s\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### when the initializer is not a bare literal

#### does not warn on a call initializer (expression type governs)

- does not warn on a call initializer (expression type governs)
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on a call initializer (expression type governs)")
val source = "fn f():\n    val n = count_items()\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn on an arithmetic expression initializer

- does not warn on an arithmetic expression initializer
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on an arithmetic expression initializer")
val source = "fn f(k: i64):\n    val n = k + 1\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn on a string literal initializer

- does not warn on a string literal initializer
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on a string literal initializer")
val source = "fn f():\n    val s = \"hello\"\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### exclusions

<details>
<summary>Advanced: does not warn on for-loop induction variables</summary>

#### does not warn on for-loop induction variables

- does not warn on for-loop induction variables
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on for-loop induction variables")
val source = "fn f(n: i64):\n    for i in 0..n:\n        print(i)\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>


</details>

#### skips vendored sources

- skips vendored sources
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips vendored sources")
val source = "fn f():\n    val x = 1\n"
val findings = check_bare_primitive_internal(source, "src/runtime/vendor/lib/thing.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### skips discard bindings

- skips discard bindings
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips discard bindings")
val source = "fn f():\n    val _ = 0\n"
val findings = check_bare_primitive_internal(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### profile plumbing (mission-critical tier)

#### parses both mission-critical spellings and keeps old tiers

- parses both mission-critical spellings and keeps old tiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses both mission-critical spellings and keeps old tiers")
expect(parse_lint_profile("mission-critical").is_some()).to_be(true)
expect(parse_lint_profile("mission_critical").is_some()).to_be(true)
expect(parse_lint_profile("reliable").is_some()).to_be(true)
expect(parse_lint_profile("bogus").is_some()).to_be(false)
```

</details>

#### maps W-MC-VAL-001 to the bare_primitive_internal config name

- maps W-MC-VAL-001 to the bare_primitive_internal config name
   - Expected: map_lint_code_to_config_name("W-MC-VAL-001") equals `bare_primitive_internal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps W-MC-VAL-001 to the bare_primitive_internal config name")
expect(map_lint_code_to_config_name("W-MC-VAL-001")).to_equal("bare_primitive_internal")
```

</details>

#### suppresses the rule in strict/moderate/robust tiers (allow)

- suppresses the rule in strict/moderate/robust tiers (allow)
   - Expected: lib["bare_primitive_internal"] equals `allow`
   - Expected: mod["bare_primitive_internal"] equals `allow`
   - Expected: rel["bare_primitive_internal"] equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("suppresses the rule in strict/moderate/robust tiers (allow)")
val lib = profile_default_levels(LintProfile.Strict)
expect(lib["bare_primitive_internal"]).to_equal("allow")
val mod = profile_default_levels(LintProfile.Moderate)
expect(mod["bare_primitive_internal"]).to_equal("allow")
val rel = profile_default_levels(LintProfile.Robust)
expect(rel["bare_primitive_internal"]).to_equal("allow")
```

</details>

#### warns under the critical tier, keeping robust strictness

- warns under the critical tier, keeping robust strictness
   - Expected: mc["bare_primitive_internal"] equals `warn`
   - Expected: mc["unsafe_pattern"] equals `deny`
   - Expected: mc["memory_safety"] equals `deny`
   - Expected: mc["const_ref_default"] equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns under the critical tier, keeping robust strictness")
val mc = profile_default_levels(LintProfile.Critical)
expect(mc["bare_primitive_internal"]).to_equal("warn")
# Reliable elevations carry over...
expect(mc["unsafe_pattern"]).to_equal("deny")
expect(mc["memory_safety"]).to_equal("deny")
# ...and const_ref_default keeps its existing default level.
expect(mc["const_ref_default"]).to_equal("warn")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-SSPEC-COMPILER):`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `953aafdfe6ce525680fa6053d561eade25409d97b06d1f3e28a847fb4c5ad381`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `953aafdfe6ce525680fa6053d561eade25409d97b06d1f3e28a847fb4c5ad381`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `953aafdfe6ce525680fa6053d561eade25409d97b06d1f3e28a847fb4c5ad381`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/bare_primitive_internal_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/bare_primitive_internal_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/bare_primitive_internal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/bare_primitive_internal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/bare_primitive_internal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/bare_primitive_internal_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on a bare integer literal val' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/bare_primitive_internal_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on a bare bool literal var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/bare_primitive_internal_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on a bare float literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
