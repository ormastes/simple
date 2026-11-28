# Per-file weave plan, join-point weave key and plan digest

> Purpose: Prove that a file's weave plan and its keys are a pure function of the file's own join-point rows and the advice effective in its directory, and that each key moves exactly when the woven object can change.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-file weave plan, join-point weave key and plan digest

Purpose: Prove that a file's weave plan and its keys are a pure function of the file's own join-point rows and the advice effective in its directory, and that each key moves exactly when the woven object can change.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aspect_weave_plan_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that a file's weave plan and its keys are a pure function of the file's own join-point rows and the advice effective in its directory, and that each key moves exactly when the woven object can change.
Audience: compiler engineers who maintain aspect weaving, the incremental
rebuild planner and the object cache key.

Lifecycle: research doc/01_research/domain/dir_tldr_aspect.md; plan
doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (stage AW-5);
architecture doc/04_architecture/extreme_typing_traceability.md; design
doc/05_design/compiler/cache/aspect_tldr_async_trace.md (sections 4-5, D1, D2).

## What the operator can rely on

**Plan.** For each own join point the plan lists the static `before`/`after`
advice whose selector matches it, ordered by `(order, AdviceId)` whatever the
input order. Two matched advice rows with equal order on one join point are an
error that names the join point and both advice ids.

**Join-point weave key.** It covers the join point id, its signature digest,
its base body digest and the ordered advice entries (id, mode, activation,
signature digest, effects digest, order). It has no directory-wide input.

| Edit | Weave key of an unaffected join point | Weave key of the affected one |
|---|---|---|
| a sibling join point is added | equal | - |
| a selector that does not reach it is edited | equal | - |
| its signature or base body changes | - | changes |
| advice signature, effects, order or mode changes | - | changes |
| advice body changes, handler has no `inline|` entry | - | equal |
| advice body changes, handler has an `inline|` entry | - | changes (interim D1 rule) |

**Plan digest.** `plan_digest(file)` covers the weave keys of the advised join
points, the mir-family rule set and the log configuration of the file's scope.
A file that nothing reaches has one fixed digest, so its object key is the same
as without aspects. A mir-family rule or a log rule changes the digest of every
file it is effective for, matched or not, and of no other file.

**Fail closed.** `plan_digest` is empty, and must not be used as a key, when
there is an order conflict, when a static advice row cannot be planned here
(unsupported selector, or a mode other than before/after), or when an inline
handler has no body digest. Advice that is not static is not planned: it stays
on the registry path.

## Inputs produced by other stages
The join-point rows are the `join-point|` rows of stage AW-2 (`JoinPointFactV2`:
the fact, a real base body digest and a signature digest). The advice and rule
rows are `effective_advice(dir)` of stages AW-1 and AW-7a, already filtered by
scope; these examples build both by hand.

## Decision inventory (aspect_weave_plan_v1.spl)

| Decision | Conditions | Covering examples |
|---|---|---|
| sorted insert of texts, advice, join points | position, greater | reversed and ordered inputs |
| handler has an inline entry | c1 | inline / call-only body edit |
| advice orders differ, else id order | c1 | different orders / equal orders |
| rule row is inline without a body digest | c1, c2 | inline rule with and without digest, call rule |
| advice row is static | c1 | static / registry |
| static row mode is cacheable | c1 | before / around |
| selector is unsupported | c1 | `cflow(x)` / supported |
| advice is inline without a body digest | c1, c2 | inline with and without digest, call |
| advice is planned for the join point | cacheable, matched | registry row, non-matching row, matching row |
| join point already has advice, equal order | c1 / c1 | first match / second match, equal and different order |
| join point is advised | c1 | advised / unadvised join point |
| reason still empty after advice, after mir rules | c1 / c1 | advice reason, mir reason, log reason, none |
| plan is complete and conflict free | c1, c2 | clean / incomplete / conflict |

## Scenarios

### Plan order

#### orders the advice of a join point by order, then advice id

- Plan three matching advice rows whose orders are 5, 1 and 3
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: advice_of(p, "run") equals `["trace", "meter", "audit"]`
   - Expected: p.order_conflicts equals `[]`
   - Expected: p.incomplete_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan three matching advice rows whose orders are 5, 1 and 3")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan([point("run", "s", "b")],
    [advice("audit", "execution(run)", 5), advice("trace", "execution(run*)", 1), advice("meter", "run", 3)])
expect(advice_of(p, "run")).to_equal(["trace", "meter", "audit"])
expect(p.order_conflicts).to_equal([])
expect(p.incomplete_reason).to_equal("")
```

</details>

#### gives the same plan, keys and digest for any input order

- Plan the same rows and join points forwards and reversed
   - Exec capture: after_step
   - Evidence: execution result verified by 7 expected checks
   - Expected: reversed.plan_digest equals `forward.plan_digest`
   - Expected: key_of(reversed, "run") equals `key_of(forward, "run")`
   - Expected: advice_of(reversed, "run") equals `["trace", "audit"]`
   - Expected: advice_of(reversed, "stop") equals `["meter"]`
   - Expected: reversed.join_points[0].join_point_id equals `app/core.spl::run`
   - Expected: aop_digest_known_v1(forward.plan_digest) is true
   - Expected: aop_digest_known_v1(key_of(forward, "run")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan the same rows and join points forwards and reversed")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val a = advice("audit", "execution(run)", 5)
val t = advice("trace", "execution(run*)", 1)
val m = advice("meter", "execution(stop)", 3)
val forward = plan([point("run", "s1", "b1"), point("stop", "s2", "b2")], [a, t, m])
val reversed = plan([point("stop", "s2", "b2"), point("run", "s1", "b1")], [m, t, a])
expect(reversed.plan_digest).to_equal(forward.plan_digest)
expect(key_of(reversed, "run")).to_equal(key_of(forward, "run"))
expect(advice_of(reversed, "run")).to_equal(["trace", "audit"])
expect(advice_of(reversed, "stop")).to_equal(["meter"])
expect(reversed.join_points[0].join_point_id).to_equal("app/core.spl::run")
expect(aop_digest_known_v1(forward.plan_digest)).to_equal(true)
expect(aop_digest_known_v1(key_of(forward, "run"))).to_equal(true)
```

</details>

#### plans only the advice whose selector matches the join point

- Plan one advice for run and one for stop over both join points
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: advice_of(p, "run") equals `["audit"]`
   - Expected: advice_of(p, "stop") equals `["meter"]`
   - Expected: advice_of(p, "missing") equals `["<no such join point>"]`
   - Expected: key_of(p, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan one advice for run and one for stop over both join points")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan(two_points(), [advice("audit", "execution(run)", 1), advice("meter", "execution(stop)", 1)])
expect(advice_of(p, "run")).to_equal(["audit"])
expect(advice_of(p, "stop")).to_equal(["meter"])
expect(advice_of(p, "missing")).to_equal(["<no such join point>"])
expect(key_of(p, "missing")).to_equal("")
```

</details>

### Order conflict

#### reports equal order on one join point and names both advice ids

- Plan two matching advice rows that both have order 2
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: p.order_conflicts equals `["join point app/core.spl::run: advice audit and trace have equal order 2"]`
   - Expected: p.plan_digest equals ``
   - Expected: advice_of(p, "run") equals `["audit", "trace"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan two matching advice rows that both have order 2")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan([point("run", "s", "b")], [advice("trace", "run", 2), advice("audit", "execution(run)", 2)])
expect(p.order_conflicts).to_equal(["join point app/core.spl::run: advice audit and trace have equal order 2"])
expect(p.plan_digest).to_equal("")
expect(advice_of(p, "run")).to_equal(["audit", "trace"])
```

</details>

#### accepts equal order when the two advice rows reach different join points

- Plan two advice rows with order 2 that match different functions
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: p.order_conflicts equals `[]`
   - Expected: aop_digest_known_v1(p.plan_digest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan two advice rows with order 2 that match different functions")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan(two_points(), [advice("audit", "execution(run)", 2), advice("meter", "execution(stop)", 2)])
expect(p.order_conflicts).to_equal([])
expect(aop_digest_known_v1(p.plan_digest)).to_equal(true)
```

</details>

### Fixed digest of an unadvised file

#### gives a file that nothing reaches the fixed empty digest

- Plan a file with join points but no matching advice, no mir rule and no log rule
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: aop_digest_known_v1(empty) is true
   - Expected: aspect_weave_plan_v1([], [], [], []).plan_digest equals `empty`
   - Expected: plan(two_points(), []).plan_digest equals `empty`
   - Expected: plan(two_points(), [advice("audit", "execution(other)", 1)]).plan_digest equals `empty`
   - Expected: advice_of(plan(two_points(), []), "run") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a file with join points but no matching advice, no mir rule and no log rule")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val empty = aspect_weave_plan_empty_digest_v1()
expect(aop_digest_known_v1(empty)).to_equal(true)
expect(aspect_weave_plan_v1([], [], [], []).plan_digest).to_equal(empty)
expect(plan(two_points(), []).plan_digest).to_equal(empty)
expect(plan(two_points(), [advice("audit", "execution(other)", 1)]).plan_digest).to_equal(empty)
expect(advice_of(plan(two_points(), []), "run")).to_equal([])
```

</details>

#### leaves the fixed digest once a join point is advised

- Plan the same file with one matching advice
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: p.plan_digest == aspect_weave_plan_empty_digest_v1() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan the same file with one matching advice")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan(two_points(), [advice("audit", "execution(run)", 1)])
expect(p.plan_digest == aspect_weave_plan_empty_digest_v1()).to_equal(false)
```

</details>

### Join-point weave key has no directory-wide input

#### keeps a join point's key when a sibling join point is added

- Plan the file with and without a third join point that the advice also matches
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: key_of(after, "run") equals `key_of(before, "run")`
   - Expected: advice_of(after, "run_fast") equals `["trace"]`
   - Expected: after.plan_digest == before.plan_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan the file with and without a third join point that the advice also matches")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val rows = [advice("trace", "execution(run*)", 1)]
val before = plan([point("run", "s", "b")], rows)
val after = plan([point("run", "s", "b"), point("run_fast", "s3", "b3")], rows)
expect(key_of(after, "run")).to_equal(key_of(before, "run"))
expect(advice_of(after, "run_fast")).to_equal(["trace"])
expect(after.plan_digest == before.plan_digest).to_equal(false)
```

</details>

#### keeps a join point's key when a selector that does not reach it is edited

- Edit the selector of the advice on stop so that it no longer matches stop
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: key_of(after, "run") equals `key_of(before, "run")`
   - Expected: key_of(after, "stop") == key_of(before, "stop") is false
   - Expected: advice_of(after, "stop") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit the selector of the advice on stop so that it no longer matches stop")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val before = plan(two_points(), [advice("audit", "execution(run)", 1), advice("meter", "execution(stop)", 2)])
val after = plan(two_points(), [advice("audit", "execution(run)", 1), advice("meter", "execution(halt)", 2)])
expect(key_of(after, "run")).to_equal(key_of(before, "run"))
expect(key_of(after, "stop") == key_of(before, "stop")).to_equal(false)
expect(advice_of(after, "stop")).to_equal([])
```

</details>

#### keeps the key when the selector is respelled and still matches

- Replace an exact selector by a prefix selector that matches the same join point
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: key_of(prefix, "run") equals `key_of(exact, "run")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace an exact selector by a prefix selector that matches the same join point")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val exact = plan([point("run", "s", "b")], [advice("audit", "execution(run)", 1)])
val prefix = plan([point("run", "s", "b")], [advice("audit", "execution(ru*)", 1)])
expect(key_of(prefix, "run")).to_equal(key_of(exact, "run"))
```

</details>

#### changes the key when the join point's signature or base body changes

- Plan the same advice over the join point with another signature and another base body
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: key_of(signature, "run") == key_of(base, "run") is false
   - Expected: key_of(body, "run") == key_of(base, "run") is false
   - Expected: signature.plan_digest == base.plan_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan the same advice over the join point with another signature and another base body")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val rows = [advice("audit", "execution(run)", 1)]
val base = plan([point("run", "sig-1", "body-1")], rows)
val signature = plan([point("run", "sig-2", "body-1")], rows)
val body = plan([point("run", "sig-1", "body-2")], rows)
expect(key_of(signature, "run") == key_of(base, "run")).to_equal(false)
expect(key_of(body, "run") == key_of(base, "run")).to_equal(false)
expect(signature.plan_digest == base.plan_digest).to_equal(false)
```

</details>

#### changes the key when the advice signature, effects, order or mode changes

- Plan one join point under five variants of the same advice
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: key_of(plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig2", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base is false
   - Expected: key_of(plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff2", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base is false
   - Expected: key_of(plan(jp, [advice_full("audit", "run", "before", "static", 7, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base is false
   - Expected: key_of(plan(jp, [advice_full("audit", "run", "after", "static", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base is false
   - Expected: key_of(plan(jp, [advice_full("audit2", "run", "before", "static", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan one join point under five variants of the same advice")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val jp = [point("run", "s", "b")]
val base = key_of(plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run")
expect(key_of(plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig2", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base).to_equal(false)
expect(key_of(plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff2", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base).to_equal(false)
expect(key_of(plan(jp, [advice_full("audit", "run", "before", "static", 7, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base).to_equal(false)
expect(key_of(plan(jp, [advice_full("audit", "run", "after", "static", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base).to_equal(false)
expect(key_of(plan(jp, [advice_full("audit2", "run", "before", "static", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)]), "run") == base).to_equal(false)
```

</details>

#### is the key of the join point's own ordered advice and nothing else

- Compute the key from the join point and its ordered advice without a plan
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: key_of(p, "run") equals `join_point_weave_key_v1(jp, [first, second])`
   - Expected: join_point_weave_key_v1(jp, [second, first]) == key_of(p, "run") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compute the key from the join point and its ordered advice without a plan")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val jp = point("run", "s", "b")
val first = advice("trace", "run", 1)
val second = advice("audit", "run", 2)
val p = plan([jp, point("stop", "s2", "b2")], [second, first, advice("meter", "execution(stop)", 1)])
expect(key_of(p, "run")).to_equal(join_point_weave_key_v1(jp, [first, second]))
expect(join_point_weave_key_v1(jp, [second, first]) == key_of(p, "run")).to_equal(false)
```

</details>

### Advice body edit (decision D1, interim inline rule)

#### keeps the plan digest when the handler has no inline entry

- Edit only the body digest of a call-only handler
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: after.plan_digest equals `before.plan_digest`
   - Expected: key_of(after, "run") equals `key_of(before, "run")`
   - Expected: aop_digest_known_v1(after.plan_digest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit only the body digest of a call-only handler")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val jp = [point("run", "s", "b")]
val before = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body-1", AdviceBodyLinkV1.CallOnly)])
val after = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body-2", AdviceBodyLinkV1.CallOnly)])
expect(after.plan_digest).to_equal(before.plan_digest)
expect(key_of(after, "run")).to_equal(key_of(before, "run"))
expect(aop_digest_known_v1(after.plan_digest)).to_equal(true)
```

</details>

#### changes the plan digest when the handler has an inline entry

- Edit only the body digest of a handler that has an inline entry
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: after.plan_digest == before.plan_digest is false
   - Expected: key_of(after, "run") == key_of(before, "run") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit only the body digest of a handler that has an inline entry")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val jp = [point("run", "s", "b")]
val before = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body-1", AdviceBodyLinkV1.Inline)])
val after = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body-2", AdviceBodyLinkV1.Inline)])
expect(after.plan_digest == before.plan_digest).to_equal(false)
expect(key_of(after, "run") == key_of(before, "run")).to_equal(false)
```

</details>

#### gives an inline handler another key than the same call-only handler

- Plan the same advice once with and once without an inline entry
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: key_of(inline, "run") == key_of(call, "run") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan the same advice once with and once without an inline entry")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val jp = [point("run", "s", "b")]
val call = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body-1", AdviceBodyLinkV1.CallOnly)])
val inline = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "body-1", AdviceBodyLinkV1.Inline)])
expect(key_of(inline, "run") == key_of(call, "run")).to_equal(false)
```

</details>

#### refuses a key when an inline handler has no body digest

- Plan an inline advice row and an inline mir rule whose body digests are empty
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: p.incomplete_reason equals `inline-body-digest-missing:audit`
   - Expected: p.plan_digest equals ``
   - Expected: q.incomplete_reason equals `inline-body-digest-missing:probe`
   - Expected: q.plan_digest equals ``
   - Expected: with_body.incomplete_reason equals ``
   - Expected: aspect_weave_plan_v1(jp, [], [inline_rule], []).plan_digest == with_body.plan_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan an inline advice row and an inline mir rule whose body digests are empty")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val jp = [point("run", "s", "b")]
val p = plan(jp, [advice_full("audit", "run", "before", "static", 1, "sig", "eff", "", AdviceBodyLinkV1.Inline)])
expect(p.incomplete_reason).to_equal("inline-body-digest-missing:audit")
expect(p.plan_digest).to_equal("")
var inline_rule = rule("probe", "sha256:sel", 10)
inline_rule.body_link = AdviceBodyLinkV1.Inline
val q = aspect_weave_plan_v1(jp, [], [inline_rule], [])
expect(q.incomplete_reason).to_equal("inline-body-digest-missing:probe")
expect(q.plan_digest).to_equal("")
inline_rule.body_digest = "body-1"
val with_body = aspect_weave_plan_v1(jp, [], [inline_rule], [])
expect(with_body.incomplete_reason).to_equal("")
inline_rule.body_digest = "body-2"
expect(aspect_weave_plan_v1(jp, [], [inline_rule], []).plan_digest == with_body.plan_digest).to_equal(false)
```

</details>

### Mir-family rules and log configuration

#### changes the digest of every file in the rule's scope, matched or not

- Change the priority of a mir-family rule that is effective for two files
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the priority of a mir-family rule that is effective for two files")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val file_a = [point("run", "s", "b")]
val file_b = [point("stop", "s2", "b2")]
val before = [rule("probe", "sha256:sel-run", 10)]
val after = [rule("probe", "sha256:sel-run", 20)]
expect(aspect_weave_plan_v1(file_a, [], after, []).plan_digest ==
    aspect_weave_plan_v1(file_a, [], before, []).plan_digest).to_equal(false)
expect(aspect_weave_plan_v1(file_b, [], after, []).plan_digest ==
    aspect_weave_plan_v1(file_b, [], before, []).plan_digest).to_equal(false)
expect(aspect_weave_plan_v1(file_a, [], before, []).plan_digest ==
    aspect_weave_plan_empty_digest_v1()).to_equal(false)
```

</details>

#### leaves a file outside the rule's scope untouched

- Plan a file that receives no rule row because the rule scope does not admit its directory
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: outside.mir_rule_set_digest equals `aspect_mir_rule_set_digest_v1([])`
   - Expected: outside.log_config_digest equals `aspect_log_config_digest_v1([])`
   - Expected: aspect_mir_rule_set_digest_v1([rule("probe", "sha256:sel-run", 10)]) == outside.mir_rule_set_digest is false
   - Expected: aspect_mir_rule_set_digest_v1([rule("probe", "sha256:sel-run", 20)]) == outside.mir_rule_set_digest is false
   - Expected: aop_digest_known_v1(outside.plan_digest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a file that receives no rule row because the rule scope does not admit its directory")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val outside = aspect_weave_plan_v1([point("other", "s3", "b3")], [advice("audit", "execution(other)", 1)], [], [])
expect(outside.mir_rule_set_digest).to_equal(aspect_mir_rule_set_digest_v1([]))
expect(outside.log_config_digest).to_equal(aspect_log_config_digest_v1([]))
expect(aspect_mir_rule_set_digest_v1([rule("probe", "sha256:sel-run", 10)]) == outside.mir_rule_set_digest).to_equal(false)
expect(aspect_mir_rule_set_digest_v1([rule("probe", "sha256:sel-run", 20)]) == outside.mir_rule_set_digest).to_equal(false)
expect(aop_digest_known_v1(outside.plan_digest)).to_equal(true)
```

</details>

#### changes the digest of every file when a log rule is switched on

- Add the call-logging rule to the log configuration of two files
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: file_a.plan_digest == aspect_weave_plan_empty_digest_v1() is false
   - Expected: file_b.plan_digest == aspect_weave_plan_empty_digest_v1() is false
   - Expected: file_a.log_config_digest equals `aspect_log_config_digest_v1(log)`
   - Expected: file_a.log_config_digest == aspect_log_config_digest_v1([]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Add the call-logging rule to the log configuration of two files")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val log = [rule("__spl_aop_log_function_call", "join:call", 100)]
val file_a = aspect_weave_plan_v1([point("run", "s", "b")], [], [], log)
val file_b = aspect_weave_plan_v1([], [], [], log)
expect(file_a.plan_digest == aspect_weave_plan_empty_digest_v1()).to_equal(false)
expect(file_b.plan_digest == aspect_weave_plan_empty_digest_v1()).to_equal(false)
expect(file_a.log_config_digest).to_equal(aspect_log_config_digest_v1(log))
expect(file_a.log_config_digest == aspect_log_config_digest_v1([])).to_equal(false)
```

</details>

#### does not confuse a mir-family rule with the same row used as a log rule

- Digest one row list as a mir rule set and as a log configuration
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: aspect_mir_rule_set_digest_v1(rows) == aspect_log_config_digest_v1(rows) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Digest one row list as a mir rule set and as a log configuration")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val rows = [rule("probe", "sha256:sel", 10)]
expect(aspect_mir_rule_set_digest_v1(rows) == aspect_log_config_digest_v1(rows)).to_equal(false)
expect(aspect_weave_plan_v1([], [], rows, []).plan_digest ==
    aspect_weave_plan_v1([], [], [], rows).plan_digest).to_equal(false)
```

</details>

#### is independent of the order of the rule rows

- Digest two mir-family rules forwards and reversed
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: aspect_mir_rule_set_digest_v1([second, first]) equals `aspect_mir_rule_set_digest_v1([first, second])`
   - Expected: aspect_mir_rule_set_digest_v1([first]) == aspect_mir_rule_set_digest_v1([first, second]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Digest two mir-family rules forwards and reversed")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val first = rule("probe", "sha256:sel-a", 10)
val second = rule("guard", "sha256:sel-b", 20)
expect(aspect_mir_rule_set_digest_v1([second, first])).to_equal(aspect_mir_rule_set_digest_v1([first, second]))
expect(aspect_mir_rule_set_digest_v1([first]) == aspect_mir_rule_set_digest_v1([first, second])).to_equal(false)
```

</details>

### Rows that cannot be planned here

#### does not plan advice that is activated through the registry

- Plan a registry-activated advice whose selector matches the join point
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: advice_of(p, "run") equals `[]`
   - Expected: p.incomplete_reason equals ``
   - Expected: p.plan_digest equals `aspect_weave_plan_empty_digest_v1()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a registry-activated advice whose selector matches the join point")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan([point("run", "s", "b")],
    [advice_full("dyn", "run", "before", "registry", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)])
expect(advice_of(p, "run")).to_equal([])
expect(p.incomplete_reason).to_equal("")
expect(p.plan_digest).to_equal(aspect_weave_plan_empty_digest_v1())
```

</details>

#### refuses a key when a static advice has a mode other than before or after

- Plan a static around advice
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: p.incomplete_reason equals `uncacheable-advice-mode:wrap`
   - Expected: p.plan_digest equals ``
   - Expected: advice_of(p, "run") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a static around advice")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan([point("run", "s", "b")],
    [advice_full("wrap", "run", "around", "static", 1, "sig", "eff", "body", AdviceBodyLinkV1.CallOnly)])
expect(p.incomplete_reason).to_equal("uncacheable-advice-mode:wrap")
expect(p.plan_digest).to_equal("")
expect(advice_of(p, "run")).to_equal([])
```

</details>

#### refuses a key when a static advice has a selector that cannot be evaluated

- Plan a static before advice whose selector uses an unsupported atom
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: p.incomplete_reason equals `unsupported-selector:flow`
   - Expected: p.plan_digest equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a static before advice whose selector uses an unsupported atom")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
val p = plan([point("run", "s", "b")], [advice("flow", "cflow(run)", 1)])
expect(p.incomplete_reason).to_equal("unsupported-selector:flow")
expect(p.plan_digest).to_equal("")
```

</details>

#### reports the first reason and keeps the conflict list separate

- Plan an order conflict together with an inline log rule that has no body digest
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: p.incomplete_reason equals `inline-body-digest-missing:log`
   - Expected: p.order_conflicts.len() equals `1)  # oracle: 1 - the one equal-order pair audit/trace on run`
   - Expected: p.plan_digest equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan an order conflict together with an inline log rule that has no body digest")
# @req: REQ-ASPECT-AW5-WEAVE-PLAN
var log_rule = rule("log", "join:call", 100)
log_rule.body_link = AdviceBodyLinkV1.Inline
val p = aspect_weave_plan_v1([point("run", "s", "b")],
    [advice("audit", "run", 2), advice("trace", "run", 2)], [rule("probe", "sha256:sel", 1)], [log_rule])
expect(p.incomplete_reason).to_equal("inline-body-digest-missing:log")
expect(p.order_conflicts.len()).to_equal(1)  # oracle: 1 - the one equal-order pair audit/trace on run
expect(p.plan_digest).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-ASPECT-AW5-WEAVE-PLAN`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d47baa132bf515647086957553fa4973d1d0835a1462c56699d15edcb0f494c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d47baa132bf515647086957553fa4973d1d0835a1462c56699d15edcb0f494c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d47baa132bf515647086957553fa4973d1d0835a1462c56699d15edcb0f494c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aspect_weave_plan_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aspect_weave_plan_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aspect_weave_plan_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aspect_weave_plan_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
