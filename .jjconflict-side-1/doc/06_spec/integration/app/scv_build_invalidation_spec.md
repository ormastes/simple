# scv_build_invalidation_spec

> Purpose: This spec proves SCV build invalidation (SCV-IMPL-G-06):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_build_invalidation_spec

Purpose: This spec proves SCV build invalidation (SCV-IMPL-G-06):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_build_invalidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV build invalidation (SCV-IMPL-G-06):
`syntactic_interface_id` drives downstream invalidation in SCV's own
metadata — an interface change invalidates every transitive consumer; an
impl-only change rebuilds the module and marks downstream skippable; and a
comment-only change NEVER skips codegen, because the skip is gated on an
explicit `dependency_model` field that only "confirmed" satisfies, and the
compiler dependency model is honestly reported "unavailable"
(`interface_digest_of` has zero call sites — compiler-confirmed irrelevance
is never claimed). Discriminating properties: the plan rows differ by change
class, transitive consumers are poisoned, and the comment-only reason names
the blocking dependency_model status.
Audience: Maintainers of the SCV gates / build-invalidation layer.

## Scenarios

### scv build invalidation (SCV-IMPL-G-06)

#### reports the dependency model honestly unavailable and blocks the comment-only skip on it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the compiler has no wired dependency model (interface_digest_of: zero callers)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BUILD-INVALIDATION-001, REQ-SSPEC-INTEGRATION
assert_equal(scv_build_invalidation_version(), "scv/build-invalidation/v1")
step("the compiler has no wired dependency model (interface_digest_of: zero callers)")
assert_equal(scv_dependency_model_status(), "unavailable")
assert_false(scv_comment_only_skip_allowed("unavailable"))
assert_false(scv_comment_only_skip_allowed(""))
assert_true(scv_comment_only_skip_allowed("confirmed"))
```

</details>

#### classifies changes from fingerprint rows

- raw hash separates comment-only from unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BUILD-INVALIDATION-001
val base = scv_build_fingerprint_row("m", SRC)
assert_equal(scv_build_change_class(base, scv_build_fingerprint_row("m", SRC)), "unchanged")
assert_equal(scv_build_change_class(base, scv_build_fingerprint_row("m", SRC_COMMENT)), "comment_only")
assert_equal(scv_build_change_class(base, scv_build_fingerprint_row("m", SRC_BODY)), "impl_only")
assert_equal(scv_build_change_class(base, scv_build_fingerprint_row("m", SRC_SIG)), "interface_changed")
assert_equal(scv_build_change_class("", base), "added")
assert_equal(scv_build_change_class(base, ""), "removed")
step("raw hash separates comment-only from unchanged")
assert_not_equal(scv_raw_source_hash(SRC), scv_raw_source_hash(SRC_COMMENT))
```

</details>

#### interface change invalidates transitive consumers; impl-only leaves downstream skippable

- transitive closure: core poisons lib, app and other
- interface change in core: every consumer row is invalidated naming core
- impl-only change in core: consumers stay skippable (interface unchanged)


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BUILD-INVALIDATION-001
val deps = ["app|lib", "lib|core", "other|lib"]
step("transitive closure: core poisons lib, app and other")
val down = scv_downstream_of("core", deps)
assert_equal(down.len(), 3)
val old_rows = [scv_build_fingerprint_row("core", DEP_SRC),
                scv_build_fingerprint_row("lib", SRC),
                scv_build_fingerprint_row("app", SRC),
                scv_build_fingerprint_row("other", SRC)]
step("interface change in core: every consumer row is invalidated naming core")
val new_rows_iface = [scv_build_fingerprint_row("core", "fn helper(extra: i64) -> i64:\n    7\n"),
                      scv_build_fingerprint_row("lib", SRC),
                      scv_build_fingerprint_row("app", SRC),
                      scv_build_fingerprint_row("other", SRC)]
val plan1 = scv_build_invalidation_plan(old_rows, new_rows_iface, deps, scv_dependency_model_status())
expect(scv_build_plan_row(plan1, "core")).to_contain("|interface_changed|rebuild+invalidate_downstream|")
expect(scv_build_plan_row(plan1, "app")).to_contain("|invalidated|")
expect(scv_build_plan_row(plan1, "app")).to_contain("core")
expect(scv_build_plan_row(plan1, "other")).to_contain("|invalidated|")
step("impl-only change in core: consumers stay skippable (interface unchanged)")
val new_rows_impl = [scv_build_fingerprint_row("core", "fn helper() -> i64:\n    8\n"),
                     scv_build_fingerprint_row("lib", SRC),
                     scv_build_fingerprint_row("app", SRC),
                     scv_build_fingerprint_row("other", SRC)]
val plan2 = scv_build_invalidation_plan(old_rows, new_rows_impl, deps, scv_dependency_model_status())
expect(scv_build_plan_row(plan2, "core")).to_contain("|impl_only|codegen|")
expect(scv_build_plan_row(plan2, "core")).to_contain("downstream skippable")
expect(scv_build_plan_row(plan2, "app")).to_contain("|unchanged|skip|")
expect(scv_build_plan_row(plan2, "lib")).to_contain("|unchanged|skip|")
```

</details>

#### comment-only change plans codegen, naming the blocking dependency_model — never a silent skip

- only an explicit compiler-confirmed model would allow the skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BUILD-INVALIDATION-001
val deps: [text] = []
val old_rows = [scv_build_fingerprint_row("m", SRC)]
val new_rows = [scv_build_fingerprint_row("m", SRC_COMMENT)]
val plan = scv_build_invalidation_plan(old_rows, new_rows, deps, scv_dependency_model_status())
val row = scv_build_plan_row(plan, "m")
expect(row).to_contain("|comment_only|codegen|")
expect(row).to_contain("dependency_model: unavailable")
expect(row).to_contain("interface_digest_of")
step("only an explicit compiler-confirmed model would allow the skip")
val plan_ok = scv_build_invalidation_plan(old_rows, new_rows, deps, "confirmed")
expect(scv_build_plan_row(plan_ok, "m")).to_contain("|comment_only|skip|")
```

</details>

#### added and removed modules poison their consumers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BUILD-INVALIDATION-001
val deps = ["app|newmod"]
val plan = scv_build_invalidation_plan(
    [scv_build_fingerprint_row("app", SRC)],
    [scv_build_fingerprint_row("app", SRC), scv_build_fingerprint_row("newmod", DEP_SRC)],
    deps, scv_dependency_model_status())
expect(scv_build_plan_row(plan, "newmod")).to_contain("|added|rebuild+invalidate_downstream|")
expect(scv_build_plan_row(plan, "app")).to_contain("|invalidated|")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-BUILD-INVALIDATION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b608dc791bdd50fe84eacde016065028534faa5a58552c91c3914a055b63c78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b608dc791bdd50fe84eacde016065028534faa5a58552c91c3914a055b63c78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b608dc791bdd50fe84eacde016065028534faa5a58552c91c3914a055b63c78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/integration/app/scv_build_invalidation_spec.spl
mirror: doc/06_spec/integration/app/scv_build_invalidation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_build_invalidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_build_invalidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_build_invalidation_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the dependency model honestly unavailable and blocks the comment-only skip on it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_build_invalidation_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies changes from fingerprint rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_build_invalidation_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interface change invalidates transitive consumers; impl-only leaves downstream skippable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_build_invalidation_spec.spl:105:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'added and removed modules poison their consumers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
