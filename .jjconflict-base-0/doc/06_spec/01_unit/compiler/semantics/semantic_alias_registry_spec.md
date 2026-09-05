# semantic_alias_registry_spec

> Purpose: Prove that semantic alias registry (lane ALS1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# semantic_alias_registry_spec

Purpose: Prove that semantic alias registry (lane ALS1).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that semantic alias registry (lane ALS1).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### semantic alias registry (lane ALS1)

#### type_to_text rendering

#### renders a bare named type

- renders a bare named type
- Verify: renders a bare named type
   - Expected: type_to_text(_named_type("i64", [])) equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a bare named type")
step("Verify: renders a bare named type")
# @req: REQ-COMPILER-SEMANTICS-001
alias_registry_clear()
expect(type_to_text(_named_type("i64", []))).to_equal("i64")
```

</details>

#### renders a generic named type

- renders a generic named type
- Verify: renders a generic named type
   - Expected: type_to_text(opt_i32) equals `Option<i32>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a generic named type")
step("Verify: renders a generic named type")
alias_registry_clear()
val opt_i32 = _named_type("Option", [_named_type("i32", [])])
expect(type_to_text(opt_i32)).to_equal("Option<i32>")
```

</details>

#### (a) alias to a rule-violating type fires through the alias

#### flags a primitive reached only via an alias name

- flags a primitive reached only via an alias name
- Verify: flags a primitive reached only via an alias name
   - Expected: semantic_api_resolve_alias("Fd") equals `i64`
   - Expected: semantic_api_primitive_leaves("Fd").len() equals `1`
   - Expected: semantic_api_primitive_leaves("Fd")[0] equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a primitive reached only via an alias name")
step("Verify: flags a primitive reached only via an alias name")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "Fd": _alias("Fd", _named_type("i64", []))
}
alias_registry_populate(type_aliases)
expect(semantic_api_resolve_alias("Fd")).to_equal("i64")
expect(semantic_api_primitive_leaves("Fd").len()).to_equal(1)
expect(semantic_api_primitive_leaves("Fd")[0]).to_equal("i64")
```

</details>

#### fires through check_fn_signature for an aliased param type

- fires through check_fn_signature for an aliased param type
- Verify: fires through check_fn_signature for an aliased param type
   - Expected: vs.len() equals `1`
   - Expected: vs[0].code equals `MC-API-001`
   - Expected: vs[0].leaf equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires through check_fn_signature for an aliased param type")
step("Verify: fires through check_fn_signature for an aliased param type")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "Fd": _alias("Fd", _named_type("i64", []))
}
alias_registry_populate(type_aliases)
val vs = check_fn_signature("read", ["fd: Fd"], "", false)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-001")
expect(vs[0].leaf).to_equal("i64")
```

</details>

#### (b) alias to a clean type stays silent

#### does not flag an alias to a domain/struct type

- does not flag an alias to a domain/struct type
- Verify: does not flag an alias to a domain/struct type
   - Expected: semantic_api_primitive_leaves("UserId").len() equals `0`
   - Expected: vs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag an alias to a domain/struct type")
step("Verify: does not flag an alias to a domain/struct type")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "UserId": _alias("UserId", _named_type("Identity", []))
}
alias_registry_populate(type_aliases)
expect(semantic_api_primitive_leaves("UserId").len()).to_equal(0)
val vs = check_fn_signature("lookup", ["id: UserId"], "", false)
expect(vs.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### (c) alias-of-alias resolves

#### chases a two-level alias chain down to the primitive leaf

- chases a two-level alias chain down to the primitive leaf
- Verify: chases a two-level alias chain down to the primitive leaf
   - Expected: semantic_api_resolve_alias("Handle") equals `i64`
   - Expected: semantic_api_primitive_leaves("Handle").len() equals `1`
   - Expected: semantic_api_primitive_leaves("Handle")[0] equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("chases a two-level alias chain down to the primitive leaf")
step("Verify: chases a two-level alias chain down to the primitive leaf")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "Fd": _alias("Fd", _named_type("i64", [])),
    "Handle": _alias("Handle", _named_type("Fd", []))
}
alias_registry_populate(type_aliases)
expect(semantic_api_resolve_alias("Handle")).to_equal("i64")
expect(semantic_api_primitive_leaves("Handle").len()).to_equal(1)
expect(semantic_api_primitive_leaves("Handle")[0]).to_equal("i64")
```

</details>

#### chases a three-level alias chain

- chases a three-level alias chain
- Verify: chases a three-level alias chain
   - Expected: semantic_api_resolve_alias("A") equals `f64`
   - Expected: semantic_api_primitive_leaves("A").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("chases a three-level alias chain")
step("Verify: chases a three-level alias chain")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "A": _alias("A", _named_type("B", [])),
    "B": _alias("B", _named_type("C", [])),
    "C": _alias("C", _named_type("f64", []))
}
alias_registry_populate(type_aliases)
expect(semantic_api_resolve_alias("A")).to_equal("f64")
expect(semantic_api_primitive_leaves("A").len()).to_equal(1)
```

</details>

#### (d) alias cycle bails safely, never hangs

#### bails on a direct self-alias (type A = A)

- bails on a direct self-alias (type A = A)
- Verify: bails on a direct self-alias (type A = A)
   - Expected: alias_registry_resolve("A") equals ``
   - Expected: semantic_api_primitive_leaves("A").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bails on a direct self-alias (type A = A)")
step("Verify: bails on a direct self-alias (type A = A)")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "A": _alias("A", _named_type("A", []))
}
alias_registry_populate(type_aliases)
expect(alias_registry_resolve("A")).to_equal("")
expect(semantic_api_primitive_leaves("A").len()).to_equal(0)
```

</details>

#### bails on a mutual two-alias cycle (type A = B, type B = A)

- bails on a mutual two-alias cycle (type A = B, type B = A)
- Verify: bails on a mutual two-alias cycle (type A = B, type B = A)
   - Expected: alias_registry_resolve("A") equals ``
   - Expected: alias_registry_resolve("B") equals ``
   - Expected: semantic_api_primitive_leaves("A").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bails on a mutual two-alias cycle (type A = B, type B = A)")
step("Verify: bails on a mutual two-alias cycle (type A = B, type B = A)")
alias_registry_clear()
val type_aliases: Dict<text, ParserTypeAlias> = {
    "A": _alias("A", _named_type("B", [])),
    "B": _alias("B", _named_type("A", []))
}
alias_registry_populate(type_aliases)
expect(alias_registry_resolve("A")).to_equal("")
expect(alias_registry_resolve("B")).to_equal("")
expect(semantic_api_primitive_leaves("A").len()).to_equal(0)
```

</details>

#### unknown names remain fail-open

#### returns empty for a name the registry never saw

- returns empty for a name the registry never saw
- Verify: returns empty for a name the registry never saw
   - Expected: alias_registry_resolve("NeverDeclared") equals ``
   - Expected: semantic_api_resolve_alias("NeverDeclared") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty for a name the registry never saw")
step("Verify: returns empty for a name the registry never saw")
alias_registry_clear()
expect(alias_registry_resolve("NeverDeclared")).to_equal("")
expect(semantic_api_resolve_alias("NeverDeclared")).to_equal("")
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-SEMANTICS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4f9cb4d87ec5b7c458ab0c1cf8c901d53949bd046c5b6b791464f5fc35343a8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f9cb4d87ec5b7c458ab0c1cf8c901d53949bd046c5b6b791464f5fc35343a8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f9cb4d87ec5b7c458ab0c1cf8c901d53949bd046c5b6b791464f5fc35343a8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/semantic_alias_registry_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/semantic_alias_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/semantic_alias_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a bare named type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a generic named type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a primitive reached only via an alias name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
