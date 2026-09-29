# scv_profiles_spec

> Purpose: This spec proves SCV-IMPL-G-04 — per-repo strictness profiles

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_profiles_spec

Purpose: This spec proves SCV-IMPL-G-04 — per-repo strictness profiles

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_profiles_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-G-04 — per-repo strictness profiles
(`default` / `strict` / `mission_critical`). The profile is pinned in
`.scv/profile.sdn`; an environment request may raise `default` to `strict`
but can never lower a pinned profile and can never grant `mission_critical`.
Under `strict` and `mission_critical` the `--force-unparsed` escape hatch is
refused outright, the `forced_unparsed` state is unreachable, and any recorded
forced_unparsed audit entry blocks publication. The `default` profile keeps
the landed G-02 behaviour byte-for-byte.
Audience: Maintainers of the SCV commit gates and mission-critical lanes.

## Scenarios

### scv strictness profiles (G-04)

#### knows exactly three profiles and defaults to `default`

**Manual warnings:**
- invalid manual visibility metadata: # @manual scv-strictness-profiles (expected show, folded, detail, or skip)


- Ask the profile registry which profiles exist and which is the fresh-repo default


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PROFILES-001
step("Ask the profile registry which profiles exist and which is the fresh-repo default")
expect(scv_profile_names()).to_be(["default", "strict", "mission_critical"])
expect(scv_profile_valid("strict")).to_be(true)
expect(scv_profile_valid("permissive")).to_be(false)
val root = _repo("default")
expect(scv_profile_read(root)).to_be("default")
```

</details>

#### pins a profile per repo and rejects unknown names

- Pin each profile in .scv/profile.sdn and try an unknown name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PROFILES-001
step("Pin each profile in .scv/profile.sdn and try an unknown name")
val root = _repo("pin")
expect(scv_profile_set(root, "lenient").starts_with("ERROR")).to_be(true)
expect(scv_profile_read(root)).to_be("default")
expect(scv_profile_set(root, "strict")).to_contain("profile: strict")
expect(scv_profile_read(root)).to_be("strict")
expect(scv_profile_set(root, "mission_critical")).to_contain("profile: mission_critical")
expect(scv_profile_read(root)).to_be("mission_critical")
```

</details>

#### lets an environment request raise but never lower, and never grant mission_critical

**Manual warnings:**
- invalid capture metadata value: repo pin (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- mission_critical must be pinned in the repo, never requested from outside


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PROFILES-001
val root = _repo("env")
expect(scv_profile_effective(root, "")).to_be("default")
expect(scv_profile_effective(root, "strict")).to_be("strict")
step("mission_critical must be pinned in the repo, never requested from outside")
expect(scv_profile_effective(root, "mission_critical")).to_be("default")
scv_profile_set(root, "strict")
expect(scv_profile_effective(root, "default")).to_be("strict")
scv_profile_set(root, "mission_critical")
expect(scv_profile_effective(root, "default")).to_be("mission_critical")
expect(scv_profile_effective(root, "strict")).to_be("mission_critical")
expect(scv_profile_effective(root, "bogus")).to_be("mission_critical")
```

</details>

#### refuses --force-unparsed under strict and mission_critical

- A refused force records nothing and blocks nothing
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PROFILES-001
expect(scv_profile_refuses_forced("default")).to_be(false)
expect(scv_profile_refuses_forced("strict")).to_be(true)
expect(scv_profile_refuses_forced("mission_critical")).to_be(true)
val root = _repo("forced")
file_write("{root}/tool.py", "print('hello')\n")
scv_profile_set(root, "strict")
val out = scv_commit_parse_policy_forced(root, "{root}/tool.py", "vendored")
expect(out.starts_with("ERROR")).to_be(true)
expect(out).to_contain("profile strict")
step("A refused force records nothing and blocks nothing")
expect(scv_forced_unparsed_blocks_public(root)).to_be(false)
expect(scv_profile_publication_blocked_reason(root)).to_be("")
```

</details>

#### makes forced_unparsed unreachable in the state model under strict profiles

- Drive the state model from private_editing toward forced_unparsed under each profile
- Ordinary promotions are untouched by the profile
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PROFILES-001
step("Drive the state model from private_editing toward forced_unparsed under each profile")
expect(scv_state_transition_profile("default", "private_editing", "forced_unparsed")).to_contain("state: forced_unparsed")
expect(scv_state_transition_profile("strict", "private_editing", "forced_unparsed").starts_with("ERROR")).to_be(true)
expect(scv_state_transition_profile("mission_critical", "private_editing", "forced_unparsed").starts_with("ERROR")).to_be(true)
step("Ordinary promotions are untouched by the profile")
expect(scv_state_transition_profile("mission_critical", "private_parsed", "compile_ok")).to_contain("state: compile_ok")
```

</details>

#### blocks publication on a legacy forced_unparsed audit under every profile, naming the profile

- Forced under default (allowed), then the repo is raised to mission_critical
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PROFILES-001
val root = _repo("legacy")
file_write("{root}/tool.py", "print('hello')\n")
step("Forced under default (allowed), then the repo is raised to mission_critical")
expect(scv_commit_parse_policy_forced(root, "{root}/tool.py", "legacy")).to_contain("policy: forced_unparsed")
expect(scv_forced_unparsed_blocks_public(root)).to_be(true)
expect(scv_profile_publication_blocked_reason(root)).to_contain("profile default")
scv_profile_set(root, "mission_critical")
expect(scv_forced_unparsed_blocks_public(root)).to_be(true)
val reason = scv_profile_publication_blocked_reason(root)
expect(reason).to_contain("profile mission_critical")
expect(reason).to_contain("forced_unparsed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SCV-PROFILES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67e5f89093d06a1f53d7e75b08d7d8df62e1e659a364a261dbe42c6a0c899b05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67e5f89093d06a1f53d7e75b08d7d8df62e1e659a364a261dbe42c6a0c899b05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67e5f89093d06a1f53d7e75b08d7d8df62e1e659a364a261dbe42c6a0c899b05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/scv_profiles_spec.spl
mirror: doc/06_spec/02_integration/app/scv_profiles_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_profiles_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/02_integration/app/scv_profiles_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_profiles_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
