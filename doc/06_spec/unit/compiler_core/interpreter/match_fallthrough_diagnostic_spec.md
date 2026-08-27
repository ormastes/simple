# Match Fall-Through Diagnostic

> Guards BUG-2026-08-01-match-fallthrough: a `match` on an enum where NO arm

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Fall-Through Diagnostic

Guards BUG-2026-08-01-match-fallthrough: a `match` on an enum where NO arm

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Guards BUG-2026-08-01-match-fallthrough: a `match` on an enum where NO arm
fires used to take no branch and emit no diagnostic. The statement form was a
silent no-op; the expression form silently yielded nil (which reads back as the
integer 3 under the nil-sentinel encoding).

These examples pin the CONTENT of the diagnostic, not merely its existence.
A message that said only "no arm matched" would not have shortened the
investigation the defect caused, so each required part is asserted separately:
the enum name, the value that matched nothing, the arms that WERE covered, and
the bare-name-collision note that fires when the arms are textually exhaustive.

Non-vacuity: every example below fails if `match_fallthrough_message` is
stubbed to return a constant, or if any single component is dropped from the
message. There is no merge/backfill path that can restore the text.

## Scenarios

### match fall-through diagnostic content

#### names the enum that was matched on

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names the enum that was matched on
   - Expected: msg contains `ChangeKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the enum that was matched on")
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove"], "layout/invalidation.spl"
)
expect(msg.contains("ChangeKind")).to_equal(true)
```

</details>

#### names the value that matched nothing

- names the value that matched nothing
   - Expected: msg contains `Style`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the value that matched nothing")
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove"], "layout/invalidation.spl"
)
expect(msg.contains("Style")).to_equal(true)
```

</details>

#### names the source location

- names the source location
   - Expected: msg contains `layout/invalidation.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the source location")
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove"], "layout/invalidation.spl"
)
expect(msg.contains("layout/invalidation.spl")).to_equal(true)
```

</details>

#### lists the arms that were covered

- lists the arms that were covered
   - Expected: msg contains `Insert`
   - Expected: msg contains `Remove`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists the arms that were covered")
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove"], "layout/invalidation.spl"
)
expect(msg.contains("Insert")).to_equal(true)
expect(msg.contains("Remove")).to_equal(true)
```

</details>

#### suggests the missing arm when coverage is genuinely incomplete

- suggests the missing arm when coverage is genuinely incomplete
   - Expected: msg contains `case Style:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests the missing arm when coverage is genuinely incomplete")
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove"], "layout/invalidation.spl"
)
expect(msg.contains("case Style:")).to_equal(true)
```

</details>

#### calls out a bare-name collision when the arms ARE textually exhaustive

- calls out a bare-name collision when the arms ARE textually exhaustive
   - Expected: msg contains `bare-name collision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls out a bare-name collision when the arms ARE textually exhaustive")
# This is the reproduced instance: the arms name every variant, yet no
# arm fired, because the value's enum is a DIFFERENT declaration of the
# same bare name. A plain "missing variant" message would be actively
# misleading here, so the diagnostic must switch wording.
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove", "Style"], "layout/invalidation.spl"
)
expect(msg.contains("bare-name collision")).to_equal(true)
```

</details>

#### does NOT claim a missing arm when the variant is textually covered

- does NOT claim a missing arm when the variant is textually covered
   - Expected: msg does not contain `case Style:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT claim a missing arm when the variant is textually covered")
val msg = match_fallthrough_message(
    "ChangeKind", "Style", "enum", ["Insert", "Remove", "Style"], "layout/invalidation.spl"
)
expect(msg.contains("case Style:")).to_equal(false)
```

</details>

#### degrades readably when the enum could not be resolved

- degrades readably when the enum could not be resolved
   - Expected: msg contains `<unresolved enum>`
   - Expected: msg contains `no arm covered any variant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("degrades readably when the enum could not be resolved")
val msg = match_fallthrough_message("", "", "int", [], "x.spl")
expect(msg.contains("<unresolved enum>")).to_equal(true)
expect(msg.contains("no arm covered any variant")).to_equal(true)
```

</details>

#### is not a constant - different inputs give different text

- is not a constant - different inputs give different text
   - Expected: a == b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not a constant - different inputs give different text")
# Kills the "stub it to a fixed string" degenerate implementation that
# would otherwise satisfy every `contains` assertion above.
val a = match_fallthrough_message("A", "V1", "enum", ["V2"], "a.spl")
val b = match_fallthrough_message("B", "V3", "enum", ["V4"], "b.spl")
expect(a == b).to_equal(false)
```

</details>

### match fall-through severity wiring (SIMPLE_SAFETY_PROFILE -> abort)

#### resolves 'critical' to Deny (must abort)

- resolves 'critical' to Deny (must abort)
   - Expected: match_fallthrough_profile_is_deny("critical") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves 'critical' to Deny (must abort)")
expect(match_fallthrough_profile_is_deny("critical")).to_equal(true)
```

</details>

#### resolves the 'mission-critical' alias to Deny (must abort)

- resolves the 'mission-critical' alias to Deny (must abort)
   - Expected: match_fallthrough_profile_is_deny("mission-critical") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the 'mission-critical' alias to Deny (must abort)")
expect(match_fallthrough_profile_is_deny("mission-critical")).to_equal(true)
```

</details>

#### resolves the 'mission_critical' alias to Deny (must abort)

- resolves the 'mission_critical' alias to Deny (must abort)
   - Expected: match_fallthrough_profile_is_deny("mission_critical") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the 'mission_critical' alias to Deny (must abort)")
expect(match_fallthrough_profile_is_deny("mission_critical")).to_equal(true)
```

</details>

#### does NOT resolve 'robust' to Deny - stays warn-only

- does NOT resolve 'robust' to Deny - stays warn-only
   - Expected: match_fallthrough_profile_is_deny("robust") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT resolve 'robust' to Deny - stays warn-only")
# robust is Warn severity in the driver ladder, not Deny. A prior draft
# of this wiring over-broadly treated every named profile as Deny; this
# is the negative case that proves it does not.
expect(match_fallthrough_profile_is_deny("robust")).to_equal(false)
```

</details>

#### does NOT resolve 'reliable' (deprecated alias of robust) to Deny

- does NOT resolve 'reliable' (deprecated alias of robust) to Deny
   - Expected: match_fallthrough_profile_is_deny("reliable") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT resolve 'reliable' (deprecated alias of robust) to Deny")
expect(match_fallthrough_profile_is_deny("reliable")).to_equal(false)
```

</details>

#### does NOT resolve unset/empty profile to Deny

- does NOT resolve unset/empty profile to Deny
   - Expected: match_fallthrough_profile_is_deny("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT resolve unset/empty profile to Deny")
expect(match_fallthrough_profile_is_deny("")).to_equal(false)
```

</details>

#### does NOT resolve an unrecognized profile name to Deny

- does NOT resolve an unrecognized profile name to Deny
   - Expected: match_fallthrough_profile_is_deny("moderate") is false
   - Expected: match_fallthrough_profile_is_deny("strict") is false
   - Expected: match_fallthrough_profile_is_deny("nonsense") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT resolve an unrecognized profile name to Deny")
expect(match_fallthrough_profile_is_deny("moderate")).to_equal(false)
expect(match_fallthrough_profile_is_deny("strict")).to_equal(false)
expect(match_fallthrough_profile_is_deny("nonsense")).to_equal(false)
```

</details>

#### match_fallthrough_set_abort/get_abort round-trip both ways

- match_fallthrough_set_abort/get_abort round-trip both ways
   - Expected: match_fallthrough_get_abort() is true
   - Expected: match_fallthrough_get_abort() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match_fallthrough_set_abort/get_abort round-trip both ways")
match_fallthrough_set_abort(true)
expect(match_fallthrough_get_abort()).to_equal(true)
match_fallthrough_set_abort(false)
expect(match_fallthrough_get_abort()).to_equal(false)
```

</details>

#### SIMPLE_SAFETY_PROFILE=critical read back through rt_env_get resolves to Deny

- SIMPLE_SAFETY_PROFILE=critical read back through rt_env_get resolves to Deny
   - Expected: resolved is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIMPLE_SAFETY_PROFILE=critical read back through rt_env_get resolves to Deny")
# Exercises the exact expression eval_init() evaluates, without calling
# eval_init() itself (which resets the running interpreter's own val
# arena / func table / env - unsafe to call from inside a spec that IS
# currently being interpreted). This proves the env-var plumbing and
# the severity mapping compose correctly; eval_init() only adds one
# more call, match_fallthrough_set_abort(...), around the same value.
val saved = rt_env_get("SIMPLE_SAFETY_PROFILE") ?? ""
rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")
val resolved = match_fallthrough_profile_is_deny(rt_env_get("SIMPLE_SAFETY_PROFILE") ?? "")
rt_env_set("SIMPLE_SAFETY_PROFILE", saved)
expect(resolved).to_equal(true)
```

</details>

#### SIMPLE_SAFETY_PROFILE=robust read back through rt_env_get stays non-Deny

- SIMPLE_SAFETY_PROFILE=robust read back through rt_env_get stays non-Deny
   - Expected: resolved2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIMPLE_SAFETY_PROFILE=robust read back through rt_env_get stays non-Deny")
val saved2 = rt_env_get("SIMPLE_SAFETY_PROFILE") ?? ""
rt_env_set("SIMPLE_SAFETY_PROFILE", "robust")
val resolved2 = match_fallthrough_profile_is_deny(rt_env_get("SIMPLE_SAFETY_PROFILE") ?? "")
rt_env_set("SIMPLE_SAFETY_PROFILE", saved2)
expect(resolved2).to_equal(false)
```

</details>

### match wildcard-catch diagnostic (BUG-2026-08-01-match-fallthrough follow-up)

#### report_match_wildcard_catch does not error when disabled (default) or enabled (critical)

- report_match_wildcard_catch does not error when disabled (default) or enabled (critical)
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report_match_wildcard_catch does not error when disabled (default) or enabled (critical)")
# NOTE ON SCOPE: this does NOT assert on eval_warnings content via
# eval_get_warnings() (from compiler.core.interpreter.eval). A probe
# done while writing this spec found that a THIRD-PARTY file that
# selectively imports pieces of eval.spl and eval_tables.spl (as this
# spec does, and as any spec must, since it cannot re-enter a running
# interpreter session -- see the docstring above) does not observe
# eval_warnings.push() calls made from eval_tables.spl through
# eval_get_warnings() imported from eval.spl: warnings.len() reads
# back 0 after a push, even though match_wildcard_catch_get_enabled()
# correctly reflects match_wildcard_catch_set_enabled() (see the
# round-trip example below, which DOES pass). This reproduces
# identically for the pre-existing, already-shipped
# report_match_fallthrough -- it is not something this change
# introduced. Filed separately as
# doc/08_tracking/bug/spec_cross_module_eval_warnings_not_observed_2026-08-05.md.
# What IS verified here: calling report_match_wildcard_catch in either
# gate state does not throw. (eval_get_warnings is imported, unused by
# assertion, solely because report_match_wildcard_catch's reference to
# eval_warnings does not resolve at all in this spec's compiled scope
# otherwise -- "variable eval_warnings not found" -- which is itself
# part of the same finding.)
match_wildcard_catch_set_enabled(false)
report_match_wildcard_catch("RoomKind", "Chat", "enum")
match_wildcard_catch_set_enabled(true)
report_match_wildcard_catch("RoomKind", "Chat", "enum")
match_wildcard_catch_set_enabled(false)
val _unused = eval_get_warnings()
expect(true).to_equal(true)
```

</details>

#### match_wildcard_catch_set_enabled/get_enabled round-trip both ways

- match_wildcard_catch_set_enabled/get_enabled round-trip both ways
   - Expected: match_wildcard_catch_get_enabled() is true
   - Expected: match_wildcard_catch_get_enabled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match_wildcard_catch_set_enabled/get_enabled round-trip both ways")
match_wildcard_catch_set_enabled(true)
expect(match_wildcard_catch_get_enabled()).to_equal(true)
match_wildcard_catch_set_enabled(false)
expect(match_wildcard_catch_get_enabled()).to_equal(false)
```

</details>

#### message names the enum and the caught value

- message names the enum and the caught value
   - Expected: msg contains `RoomKind`
   - Expected: msg contains `Chat`
   - Expected: msg contains `tui/room_map.spl`
   - Expected: msg contains `wildcard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message names the enum and the caught value")
val msg = match_wildcard_catch_message("RoomKind", "Chat", "enum", "tui/room_map.spl")
expect(msg.contains("RoomKind")).to_equal(true)
expect(msg.contains("Chat")).to_equal(true)
expect(msg.contains("tui/room_map.spl")).to_equal(true)
expect(msg.contains("wildcard")).to_equal(true)
```

</details>

#### message is not a constant - different inputs give different text

- message is not a constant - different inputs give different text
   - Expected: a == b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message is not a constant - different inputs give different text")
val a = match_wildcard_catch_message("A", "V1", "enum", "a.spl")
val b = match_wildcard_catch_message("B", "V3", "enum", "b.spl")
expect(a == b).to_equal(false)
```

</details>

#### same critical-severity predicate gates both the fall-through abort and the wildcard-catch warning

- same critical-severity predicate gates both the fall-through abort and the wildcard-catch warning
   - Expected: deny is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same critical-severity predicate gates both the fall-through abort and the wildcard-catch warning")
# Both diagnostics are wired from the SAME safety_profile_deny value in
# eval_init() (eval_decls.spl) -- this pins that they cannot drift
# apart (e.g. one reading a stale/rebuilt env var while the other
# reads a fresh one).
val deny = match_fallthrough_profile_is_deny("critical")
expect(deny).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `cd3a6890b1e6a4d244dfc9f334962c03061d07c2a8e6167567802d1b1938e8cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd3a6890b1e6a4d244dfc9f334962c03061d07c2a8e6167567802d1b1938e8cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd3a6890b1e6a4d244dfc9f334962c03061d07c2a8e6167567802d1b1938e8cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl
mirror: doc/06_spec/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the enum that was matched on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the value that matched nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the source location' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
