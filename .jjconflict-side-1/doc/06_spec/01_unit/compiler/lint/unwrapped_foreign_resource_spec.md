# unwrapped_foreign_resource_spec

> Firmware-style rule: a raw opaque handle acquired from an SFFI

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# unwrapped_foreign_resource_spec

Firmware-style rule: a raw opaque handle acquired from an SFFI

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## No unwrapped foreign resource escape (REQ-SSPEC-COMPILER)

    Firmware-style rule: a raw opaque handle acquired from an SFFI
    acquire-verb extern (`rt_..._open`/`_create`/`_new`/`_alloc`) must not
    escape its acquire call site unwrapped. Warn-level under the critical
    profile; allow elsewhere.

## Scenarios

### W-MC-RES-001: unwrapped foreign resource

#### when a bare handle escapes via return

#### warns on a direct acquire call returned bare

- warns on a direct acquire call returned bare
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `W-MC-RES-001`
   - Expected: findings[0].line_num equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a direct acquire call returned bare")
val source = "extern fn rt_file_open(path: text) -> i64\n\nfn read_config(path: text) -> i64:\n    return rt_file_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].code).to_equal("W-MC-RES-001")
expect(findings[0].line_num).to_equal(4)
```

</details>

#### warns on a tracked handle var returned bare

- warns on a tracked handle var returned bare
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a tracked handle var returned bare")
val source = "extern fn rt_file_open(path: text) -> i64\n\nfn read_config(path: text) -> i64:\n    val handle = rt_file_open(path)\n    return handle\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(5)
```

</details>

#### warns on raw handles returned in a tuple

- warns on raw handles returned in a tuple
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on raw handles returned in a tuple")
val source = "extern fn rt_file_open(path: text) -> i64\n\nfn open_two(a: text, b: text) -> (i64, i64):\n    return (rt_file_open(a), rt_file_open(b))\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(4)
```

</details>

#### when a bare handle escapes as the tail expression

#### warns on a direct acquire call as the fn's tail expression

- warns on a direct acquire call as the fn's tail expression
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a direct acquire call as the fn's tail expression")
val source = "extern fn rt_db_open(path: text) -> i64\n\nfn open_db(path: text) -> i64:\n    rt_db_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(4)
```

</details>

#### warns on a tracked handle var as the tail expression

- warns on a tracked handle var as the tail expression
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a tracked handle var as the tail expression")
val source = "extern fn rt_db_open(path: text) -> i64\n\nfn open_db(path: text) -> i64:\n    val h = rt_db_open(path)\n    h\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(5)
```

</details>

#### when a bare handle is assigned directly to a struct/class field

#### warns on self.field = <acquire call>

- warns on self.field = <acquire call>
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on self.field = <acquire call>")
val source = "extern fn rt_db_open(path: text) -> i64\n\nclass Database:\n    handle: i64\n\n    me reopen(path: text):\n        self.handle = rt_db_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(7)
```

</details>

#### warns on self.field = <tracked handle var>

- warns on self.field = <tracked handle var>
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on self.field = <tracked handle var>")
val source = "extern fn rt_db_open(path: text) -> i64\n\nclass Database:\n    handle: i64\n\n    me reopen(path: text):\n        val h = rt_db_open(path)\n        self.handle = h\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(8)
```

</details>

#### when the handle is wrapped in a constructor call

#### does not warn when the acquire call is a constructor argument, tail-returned

- does not warn when the acquire call is a constructor argument, tail-returned
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn when the acquire call is a constructor argument, tail-returned")
val source = "extern fn rt_db_open(path: text) -> i64\nextern fn rt_db_close(handle: i64) -> bool\n\nclass Database:\n    handle: i64\n\n    static fn open(path: text) -> Database:\n        Database(handle: rt_db_open(path))\n\n    me close():\n        rt_db_close(self.handle)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn when the acquire call is a constructor argument, returned via `return`

- does not warn when the acquire call is a constructor argument, returned via `return`
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn when the acquire call is a constructor argument, returned via `return`")
val source = "extern fn rt_db_open(path: text) -> i64\n\nclass Database:\n    handle: i64\n\n    static fn open(path: text) -> Database:\n        return Database(handle: rt_db_open(path))\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### exclusions

#### does not warn on the extern fn declaration itself

- does not warn on the extern fn declaration itself
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on the extern fn declaration itself")
val source = "extern fn rt_file_open(path: text) -> i64\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn on an @unsafe-boundary fn

- does not warn on an @unsafe-boundary fn
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on an @unsafe-boundary fn")
val source = "extern fn rt_file_open(path: text) -> i64\n\n@unsafe(reason: \"ffi boundary\", capabilities: [ffi])\nfn raw_open(path: text) -> i64:\n    return rt_file_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### skips generated sffi_gen adapter modules

- skips generated sffi_gen adapter modules
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips generated sffi_gen adapter modules")
val source = "extern fn rt_file_open(path: text) -> i64\n\nfn raw_open(path: text) -> i64:\n    return rt_file_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/compiler/90.tools/sffi_gen/generated/file_adapter.spl")
expect(findings.len()).to_equal(0)
```

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
val source = "extern fn rt_file_open(path: text) -> i64\n\nfn raw_open(path: text) -> i64:\n    return rt_file_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/runtime/vendor/lib/thing.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not warn on a non-acquire extern call

- does not warn on a non-acquire extern call
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn on a non-acquire extern call")
val source = "extern fn rt_file_close(handle: i64) -> bool\n\nfn shutdown(handle: i64) -> bool:\n    return rt_file_close(handle)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### return-type gate: an acquire verb is not enough, it must be a handle

#### does not flag an acquire-verb extern that returns bool

- does not flag an acquire-verb extern that returns bool
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag an acquire-verb extern that returns bool")
# rt_dir_create makes a directory and returns success; there is no
# handle to wrap. 19 real findings in src/ were this shape.
val source = "extern fn rt_dir_create(path: text, parents: bool) -> bool\n\nfn ensure(path: text) -> bool:\n    return rt_dir_create(path, true)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### does not flag an acquire-verb extern that returns an array

- does not flag an acquire-verb extern that returns an array
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag an acquire-verb extern that returns an array")
val source = "extern fn rt_bytes_alloc(n: i64) -> [u8]\n\nfn buf(n: i64) -> [u8]:\n    return rt_bytes_alloc(n)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### still flags an acquire-verb extern that returns an i64 handle

- still flags an acquire-verb extern that returns an i64 handle
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still flags an acquire-verb extern that returns an i64 handle")
val source = "extern fn rt_file_open(path: text) -> i64\n\nfn open_raw(path: text) -> i64:\n    return rt_file_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
```

</details>

#### still flags when the return type is Any — Any IS used as a handle

- still flags when the return type is Any — Any IS used as a handle
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still flags when the return type is Any — Any IS used as a handle")
# Regression guard: rt_mutex_new/rt_rwlock_new both return Any, so
# treating Any as a non-handle would fail OPEN on real resources.
val source = "extern fn rt_mutex_new() -> Any\n\nfn make() -> Any:\n    return rt_mutex_new()\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
```

</details>

#### fails closed when the extern is declared in another file

- fails closed when the extern is declared in another file
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed when the extern is declared in another file")
# No declaration here means no type information, which is not a
# licence to go quiet.
val source = "fn open_raw(path: text) -> i64:\n    return rt_file_open(path)\n"
val findings = check_unwrapped_foreign_resource(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
```

</details>

#### profile plumbing (critical tier)

#### maps W-MC-RES-001 to the unwrapped_foreign_resource config name

- maps W-MC-RES-001 to the unwrapped_foreign_resource config name
   - Expected: map_lint_code_to_config_name("W-MC-RES-001") equals `unwrapped_foreign_resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps W-MC-RES-001 to the unwrapped_foreign_resource config name")
expect(map_lint_code_to_config_name("W-MC-RES-001")).to_equal("unwrapped_foreign_resource")
```

</details>

#### allows the rule in moderate/strict/robust tiers

- allows the rule in moderate/strict/robust tiers
   - Expected: moderate["unwrapped_foreign_resource"] equals `allow`
   - Expected: strict["unwrapped_foreign_resource"] equals `allow`
   - Expected: robust["unwrapped_foreign_resource"] equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows the rule in moderate/strict/robust tiers")
val moderate = profile_default_levels(LintProfile.Moderate)
expect(moderate["unwrapped_foreign_resource"]).to_equal("allow")
val strict = profile_default_levels(LintProfile.Strict)
expect(strict["unwrapped_foreign_resource"]).to_equal("allow")
val robust = profile_default_levels(LintProfile.Robust)
expect(robust["unwrapped_foreign_resource"]).to_equal("allow")
```

</details>

#### warns under the critical tier, keeping robust strictness

- warns under the critical tier, keeping robust strictness
   - Expected: critical["unwrapped_foreign_resource"] equals `warn`
   - Expected: critical["unsafe_pattern"] equals `deny`
   - Expected: critical["bare_primitive_internal"] equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns under the critical tier, keeping robust strictness")
val critical = profile_default_levels(LintProfile.Critical)
expect(critical["unwrapped_foreign_resource"]).to_equal("warn")
expect(critical["unsafe_pattern"]).to_equal("deny")
expect(critical["bare_primitive_internal"]).to_equal("warn")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `e54d2f0732cf3df02bcfd5d9f93a28b1f2d3d57ec4011d276e940f5f2181c04d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e54d2f0732cf3df02bcfd5d9f93a28b1f2d3d57ec4011d276e940f5f2181c04d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e54d2f0732cf3df02bcfd5d9f93a28b1f2d3d57ec4011d276e940f5f2181c04d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/unwrapped_foreign_resource_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/unwrapped_foreign_resource_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/unwrapped_foreign_resource_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on a direct acquire call returned bare' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on a tracked handle var returned bare' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on raw handles returned in a tuple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
