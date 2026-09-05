# User-declared `Option` enum match lowering (system lane)

> Fences a regression class in match lowering: a USER-DECLARED enum named

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# User-declared `Option` enum match lowering (system lane)

Fences a regression class in match lowering: a USER-DECLARED enum named

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | In Progress — fail-closed, blocked on a qualified pure-Simple runtime |
| Requirements | doc/02_requirements/feature/feature.md |
| Plan | doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md |
| Design | doc/07_guide/language/user_option_enum_match_lowering.md |
| Source | `test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Fences a regression class in match lowering: a USER-DECLARED enum named
`Option` must be lowered on the enum-discriminant path, not on the nil-boxing
fast path reserved for the builtin `Option<T>`. Audience: anyone editing the
match-lowering twins in `hir/lower/expr/control.rs` and
`hir/lower/stmt_lowering.rs`, or their self-hosted equivalents.

## Scope and Preconditions

Requires an admitted pure-Simple runtime (`SIMPLE_QUALIFIED_RUNTIME`); the Rust
bootstrap seed is not acceptable evidence for this lane. Without one these
scenarios FAIL rather than skip.

This must be a NATIVE lane. The tree-walk interpreter binds match arms from
`HirFunction` directly and cannot observe the defect, so an interpreted run
would report green against a broken compiler.

## Primary Workflow

Admit a runtime, native-build `test/fixtures/user_option_enum_match/`, execute
it, and assert both arms of a user-declared `Option` behave as declared.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Builtin `Option<T>` | Nil-boxed at runtime; identified by a RESERVED enum id (1) |
| User `Option` | An ordinary enum object with an ordinary id, that merely shares the name |
| Misroute | Treating the latter as the former makes `Some` irrefutable and `None` unmatchable |

## Related Specifications

- [Bug record](../../../doc/08_tracking/bug/seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16.md) — the traced defect this lane fences

## Evidence and Provenance

Derived from a source trace of `8d96687c991`, which keys its builtin-Option
exception on `name == "Option"` while both runtimes key on the reserved enum id
(`runtime/src/value/objects.rs:490`, `src/runtime/simple_core/core_values.spl:61`).
No runtime evidence has been produced: no qualified pure-Simple runtime exists
on the reference machine as of 2026-08-16.

## Recovery and Troubleshooting

`none_arm` returning `42`, or `none_via_some` reporting `some-matched-none:*`,
is the misroute itself: the `Some` arm captured a `None` value. A failure naming
`no qualified pure-Simple runtime admitted` is the toolchain blocker instead.

## Compatibility and Limitations

Covers the two-variant `Some(payload)`/`None` shape only — the exact shape the
name heuristic collides with. Says nothing about generic `Option<T>` inference
or about `Result`.

## Scenarios

### User-declared Option enum match lowering

#### binds the payload of a user-declared Some arm on every toolchain

- binds the payload of a user-declared Some arm on every toolchain
- Build and run the user-Option fixture under each admitted toolchain
- Verify Some(42) binds its payload rather than dropping it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds the payload of a user-declared Some arm on every toolchain")
step("Build and run the user-Option fixture under each admitted toolchain")
step("Verify Some(42) binds its payload rather than dropping it")
assert_field_on_all("some_arm", "42")
```

</details>

#### matches a user-declared None arm on every toolchain

- binds the payload of a user-declared Some arm on every toolchain
- Build and run the user-Option fixture under each admitted toolchain
- Verify Some(42) binds its payload rather than dropping it
- matches a user-declared None arm on every toolchain
- Build and run the user-Option fixture under each admitted toolchain
- Verify None reaches its own arm and is not swallowed by Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds the payload of a user-declared Some arm on every toolchain")
step("Build and run the user-Option fixture under each admitted toolchain")
step("Verify Some(42) binds its payload rather than dropping it")
assert_field_on_all("some_arm", "42")

# @req REQ-SSPEC-SYSTEM
step("matches a user-declared None arm on every toolchain")
step("Build and run the user-Option fixture under each admitted toolchain")
step("Verify None reaches its own arm and is not swallowed by Some")
assert_field_on_all("none_arm", "99")
```

</details>

#### keeps the Some arm refutable against a None value on every toolchain

- binds the payload of a user-declared Some arm on every toolchain
- Build and run the user-Option fixture under each admitted toolchain
- Verify Some(42) binds its payload rather than dropping it
- keeps the Some arm refutable against a None value on every toolchain
- Build and run the user-Option fixture under each admitted toolchain
- Verify the Some arm does not capture None


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds the payload of a user-declared Some arm on every toolchain")
step("Build and run the user-Option fixture under each admitted toolchain")
step("Verify Some(42) binds its payload rather than dropping it")
assert_field_on_all("some_arm", "42")

# @req REQ-SSPEC-SYSTEM
step("keeps the Some arm refutable against a None value on every toolchain")
step("Build and run the user-Option fixture under each admitted toolchain")
step("Verify the Some arm does not capture None")
assert_field_on_all("none_via_some", "unmatched")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/feature.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md`
- **Design:** `doc/07_guide/language/user_option_enum_match_lowering.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4b752f271b31b6d5f030ad93a176cfd45101a1abeb53daa79e1923b060516c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4b752f271b31b6d5f030ad93a176cfd45101a1abeb53daa79e1923b060516c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4b752f271b31b6d5f030ad93a176cfd45101a1abeb53daa79e1923b060516c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl
mirror: doc/06_spec/03_system/compiler/user_option_enum_match_lowering_system_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/user_option_enum_match_lowering_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the payload of a user-declared Some arm on every toolchain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches a user-declared None arm on every toolchain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the Some arm refutable against a None value on every toolchain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
