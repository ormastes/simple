# Impl-Head Type Parameters

> `impl Box<T>:` declares `T` at the impl head without the `impl<T>` form. The

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Impl-Head Type Parameters

`impl Box<T>:` declares `T` at the impl head without the `impl<T>` form. The

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/impl_head_type_params_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`impl Box<T>:` declares `T` at the impl head without the `impl<T>` form. The
frontend used to hand the whole target type to `parser_parse_type`, which
merely CONSUMED `<T>`, so the resulting `Impl` AST node always carried
`type_params.len() == 0`. That made the HIR generic-impl gate in `lower_impl`
dead code for this shape and left the impl-method tier of
`is_generic_template` marking unreachable from source. See
doc/08_tracking/bug/hir_generic_templates_unconsumed_by_mono_pass_2026-08-21.md.

## Scenarios

### impl-head type parameters reach the AST

#### populates type_params for impl Box<T>:

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- populates type_params for impl Box<T>:
- Parse a generic inherent impl
- Confirm T reached Impl.type_params
   - Expected: n equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("populates type_params for impl Box<T>:")
step("Parse a generic inherent impl")
val n = impl_type_param_count(
    "struct Box<T>:\n    value: T\n\nimpl Box<T>:\n    fn get(self) -> T:\n        return self.value",
    "impl_head_tp_inherent"
)
step("Confirm T reached Impl.type_params")
expect(n).to_equal(1)
```

</details>

#### populates type_params for a generic trait impl

- populates type_params for a generic trait impl
- Parse impl Show for Box<T>:
- Confirm the self-type's T reached Impl.type_params
   - Expected: n equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("populates type_params for a generic trait impl")
step("Parse impl Show for Box<T>:")
val n = impl_type_param_count(
    "struct Box<T>:\n    value: T\n\ntrait Show:\n    fn show(self) -> i64\n\nimpl Show for Box<T>:\n    fn show(self) -> i64:\n        return 1",
    "impl_head_tp_trait"
)
step("Confirm the self-type's T reached Impl.type_params")
expect(n).to_equal(1)
```

</details>

#### populates both params for a multi-param impl

- populates both params for a multi-param impl
- Parse impl Pair<K, V>:
- Confirm both K and V reached Impl.type_params
   - Expected: n equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("populates both params for a multi-param impl")
step("Parse impl Pair<K, V>:")
val n = impl_type_param_count(
    "struct Pair<K, V>:\n    k: K\n    v: V\n\nimpl Pair<K, V>:\n    fn key(self) -> K:\n        return self.k",
    "impl_head_tp_multi"
)
step("Confirm both K and V reached Impl.type_params")
expect(n).to_equal(2)
```

</details>

#### reports zero type params for a concrete impl

- reports zero type params for a concrete impl
- Parse a non-generic impl
- Confirm a concrete impl still reports no type params
   - Expected: n equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports zero type params for a concrete impl")
step("Parse a non-generic impl")
val n = impl_type_param_count(
    "struct Point:\n    x: i64\n\nimpl Point:\n    fn x_of(self) -> i64:\n        return self.x",
    "impl_head_tp_concrete"
)
step("Confirm a concrete impl still reports no type params")
expect(n).to_equal(0)
```

</details>

#### reports zero type params for a concretely-instantiated impl

- reports zero type params for a concretely-instantiated impl
- Parse impl Box<i64>:
- Confirm a builtin type argument is not mistaken for a type param
   - Expected: n equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports zero type params for a concretely-instantiated impl")
step("Parse impl Box<i64>:")
val n = impl_type_param_count(
    "struct Box<T>:\n    value: T\n\nimpl Box<i64>:\n    fn get(self) -> i64:\n        return self.value",
    "impl_head_tp_instantiated"
)
step("Confirm a builtin type argument is not mistaken for a type param")
expect(n).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `309f8ac4c12881434bb5aac7ab8b7aba17abd3cda2e0498c181201be7e4c146a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `309f8ac4c12881434bb5aac7ab8b7aba17abd3cda2e0498c181201be7e4c146a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `309f8ac4c12881434bb5aac7ab8b7aba17abd3cda2e0498c181201be7e4c146a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/impl_head_type_params_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/impl_head_type_params_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/impl_head_type_params_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/impl_head_type_params_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/impl_head_type_params_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/impl_head_type_params_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'populates type_params for impl Box<T>:' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/impl_head_type_params_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'populates type_params for a generic trait impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/impl_head_type_params_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'populates both params for a multi-param impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
