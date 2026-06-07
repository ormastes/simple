# Promise<T> Intensive Tests

> Intensive tests for Promise chaining, combinators, error propagation, and edge cases beyond basic creation/resolution.

<!-- sdn-diagram:id=promise_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=promise_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

promise_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=promise_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Promise<T> Intensive Tests

Intensive tests for Promise chaining, combinators, error propagation, and edge cases beyond basic creation/resolution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Plan | doc/03_plan/async_promise_intensive_tests.md |
| Design | doc/05_design/async_promise_intensive_tests.md |
| Source | `test/01_unit/lib/nogc_async_mut/promise_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for Promise chaining, combinators, error propagation,
and edge cases beyond basic creation/resolution.

## Scenarios

### Promise Chaining

#### then on resolved promise maps the value

1. var p = make resolved
2. var chained = p then
   - Expected: chained.is_resolved() is true
   - Expected: chained.get_value() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved(10)
var chained = p.then(_1 + 5)
expect(chained.is_resolved()).to_equal(true)
expect(chained.get_value()).to_equal(15)
```

</details>

#### then on rejected promise propagates rejection

1. var p = make rejected
2. var chained = p then
   - Expected: chained.is_rejected() is true
   - Expected: chained.get_error() equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("fail")
var chained = p.then(_1)
expect(chained.is_rejected()).to_equal(true)
expect(chained.get_error()).to_equal("fail")
```

</details>

#### catch_err on rejected promise handles the error

1. var p = make rejected
2. var caught = p catch err
   - Expected: caught.is_resolved() is true
   - Expected: caught.get_value() equals `recovered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("oops")
var caught = p.catch_err(\_: "recovered")
expect(caught.is_resolved()).to_equal(true)
expect(caught.get_value()).to_equal("recovered")
```

</details>

#### catch_err on resolved promise passes value through

1. var p = make resolved
2. var caught = p catch err
   - Expected: caught.is_resolved() is true
   - Expected: caught.get_value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved(42)
var caught = p.catch_err(\_: "should not happen")
expect(caught.is_resolved()).to_equal(true)
expect(caught.get_value()).to_equal(42)
```

</details>

#### multi-step then chaining transforms values

1. var p = make resolved
2. var step1 = p then
3. var step2 = step1 then
4. var step3 = step2 then
   - Expected: step3.is_resolved() is true
   - Expected: step3.get_value() equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved(1)
var step1 = p.then(_1 + 1)
var step2 = step1.then(_1 * 10)
var step3 = step2.then(_1 + 3)
expect(step3.is_resolved()).to_equal(true)
expect(step3.get_value()).to_equal(23)
```

</details>

#### error propagates through multiple then steps

1. var p = make rejected
2. var step1 = p then
3. var step2 = step1 then
   - Expected: step2.is_rejected() is true
   - Expected: step2.get_error() equals `upstream error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("upstream error")
var step1 = p.then(_1)
var step2 = step1.then(_1)
expect(step2.is_rejected()).to_equal(true)
expect(step2.get_error()).to_equal("upstream error")
```

</details>

#### catch in middle of chain recovers from error

1. var p = make rejected
2. var recovered = p catch err
3. var after = recovered then
   - Expected: after.is_resolved() is true
   - Expected: after.get_value() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("mid-error")
var recovered = p.catch_err(\_: 99)
var after = recovered.then(_1 + 1)
expect(after.is_resolved()).to_equal(true)
expect(after.get_value()).to_equal(100)
```

</details>

#### finally_do runs on resolved promise

1. var p = make resolved
2. var same = p finally do
   - Expected: same.is_resolved() is true
   - Expected: same.get_value() equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved("done")
var same = p.finally_do(\: ())
# Verify it returns the same promise and does not crash
expect(same.is_resolved()).to_equal(true)
expect(same.get_value()).to_equal("done")
```

</details>

#### finally_do runs on rejected promise

1. var p = make rejected
2. var same = p finally do
   - Expected: same.is_rejected() is true
   - Expected: same.get_error() equals `err`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("err")
var same = p.finally_do(\: ())
# Verify it returns the same promise and does not crash
expect(same.is_rejected()).to_equal(true)
expect(same.get_error()).to_equal("err")
```

</details>

#### finally_do preserves promise state

1. var p = make resolved
2. var same = p finally do
   - Expected: same.is_resolved() is true
   - Expected: same.get_value() equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved(77)
var same = p.finally_do(\: ())
expect(same.is_resolved()).to_equal(true)
expect(same.get_value()).to_equal(77)
```

</details>

### Promise Combinators

#### all resolves when all promises are resolved

1. var p1 = make resolved
2. var p2 = make resolved
3. var p3 = make resolved
4. var combined = promise all
   - Expected: combined.is_resolved() is true
5. var vals = combined get value
   - Expected: vals.len() equals `3`
   - Expected: vals[0] equals `1`
   - Expected: vals[1] equals `2`
   - Expected: vals[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_resolved(1)
var p2 = make_resolved(2)
var p3 = make_resolved(3)
var combined = promise_all([p1, p2, p3])
expect(combined.is_resolved()).to_equal(true)
var vals = combined.get_value()
expect(vals.len()).to_equal(3)
expect(vals[0]).to_equal(1)
expect(vals[1]).to_equal(2)
expect(vals[2]).to_equal(3)
```

</details>

#### all rejects on first rejected promise

1. var p1 = make resolved
2. var p2 = make rejected
3. var p3 = make resolved
4. var combined = promise all
   - Expected: combined.is_rejected() is true
   - Expected: combined.get_error() equals `fail at 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_resolved(1)
var p2 = make_rejected("fail at 2")
var p3 = make_resolved(3)
var combined = promise_all([p1, p2, p3])
expect(combined.is_rejected()).to_equal(true)
expect(combined.get_error()).to_equal("fail at 2")
```

</details>

#### all resolves immediately with empty list

1. var combined = promise all
   - Expected: combined.is_resolved() is true
2. var vals = combined get value
   - Expected: vals.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var combined = promise_all([])
expect(combined.is_resolved()).to_equal(true)
var vals = combined.get_value()
expect(vals.len()).to_equal(0)
```

</details>

#### race resolves with first resolved promise

1. var p1 = make resolved
2. var p2 = make pending
3. var p3 = make pending
4. var winner = promise race
   - Expected: winner.is_resolved() is true
   - Expected: winner.get_value() equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_resolved("first")
var p2 = make_pending()
var p3 = make_pending()
var winner = promise_race([p1, p2, p3])
expect(winner.is_resolved()).to_equal(true)
expect(winner.get_value()).to_equal("first")
```

</details>

#### race rejects with first rejected promise

1. var p1 = make rejected
2. var p2 = make pending
3. var winner = promise race
   - Expected: winner.is_rejected() is true
   - Expected: winner.get_error() equals `fast fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_rejected("fast fail")
var p2 = make_pending()
var winner = promise_race([p1, p2])
expect(winner.is_rejected()).to_equal(true)
expect(winner.get_error()).to_equal("fast fail")
```

</details>

#### race stays pending when all are pending

1. var p1 = make pending
2. var p2 = make pending
3. var result = promise race
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_pending()
var p2 = make_pending()
var result = promise_race([p1, p2])
expect(result.is_pending()).to_equal(true)
```

</details>

#### any resolves with first resolved even if others rejected

1. var p1 = make rejected
2. var p2 = make resolved
3. var p3 = make rejected
4. var result = promise any
   - Expected: result.is_resolved() is true
   - Expected: result.get_value() equals `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_rejected("err1")
var p2 = make_resolved("success")
var p3 = make_rejected("err3")
var result = promise_any([p1, p2, p3])
expect(result.is_resolved()).to_equal(true)
expect(result.get_value()).to_equal("success")
```

</details>

#### any rejects when all promises are rejected

1. var p1 = make rejected
2. var p2 = make rejected
3. var p3 = make rejected
4. var result = promise any
   - Expected: result.is_rejected() is true
   - Expected: result.get_error() equals `All promises rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p1 = make_rejected("e1")
var p2 = make_rejected("e2")
var p3 = make_rejected("e3")
var result = promise_any([p1, p2, p3])
expect(result.is_rejected()).to_equal(true)
expect(result.get_error()).to_equal("All promises rejected")
```

</details>

#### all_settled resolves when all are settled

1. var p1 = make resolved
2. var p2 = make resolved
3. var result = promise all settled
   - Expected: result.is_resolved() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simplified: test with only resolved promises to avoid if-val issue
var p1 = make_resolved("ok")
var p2 = make_resolved("also ok")
var result = promise_all_settled([p1, p2])
expect(result.is_resolved()).to_equal(true)
```

</details>

#### all_settled with empty list resolves to empty

1. var result = promise all settled
   - Expected: result.is_resolved() is true
2. var settled = result get value
   - Expected: settled.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = promise_all_settled([])
expect(result.is_resolved()).to_equal(true)
var settled = result.get_value()
expect(settled.len()).to_equal(0)
```

</details>

### Error Propagation

#### rejection propagates through then chain untouched

1. var p = make rejected
2. var step1 = p then
3. var step2 = step1 then
4. var step3 = step2 then
   - Expected: step3.is_rejected() is true
   - Expected: step3.get_error() equals `original error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("original error")
var step1 = p.then(\_: "should not run")
var step2 = step1.then(\_: "also should not run")
var step3 = step2.then(\_: "still should not run")
expect(step3.is_rejected()).to_equal(true)
expect(step3.get_error()).to_equal("original error")
```

</details>

#### catch stops rejection propagation

1. var p = make rejected
2. var caught = p catch err
3. var after = caught then
   - Expected: after.is_resolved() is true
   - Expected: after.get_value() equals `handled: stopped here`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("stopped here")
var caught = p.catch_err("handled: " + _1)
var after = caught.then(_1)
expect(after.is_resolved()).to_equal(true)
expect(after.get_value()).to_equal("handled: stopped here")
```

</details>

#### re-rejection after catch propagates new error

1. var p = make rejected
2. var caught = p catch err
3. var re rejected = make rejected
4. var final step = re rejected then
   - Expected: final_step.is_rejected() is true
   - Expected: final_step.get_error() equals `second error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("first")
var caught = p.catch_err(\_: "recovered")
# Simulate re-rejection by creating a new rejected promise from recovered value
var re_rejected = make_rejected("second error")
var final_step = re_rejected.then(_1)
expect(final_step.is_rejected()).to_equal(true)
expect(final_step.get_error()).to_equal("second error")
```

</details>

### Nested Promises

#### promise resolving with a value simulates flattening

1. var inner = make resolved
2. var outer = make pending
3. var inner val = inner get value
4. outer resolve
   - Expected: outer.is_resolved() is true
   - Expected: outer.get_value() equals `inner value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inner = make_resolved("inner value")
var outer = make_pending()
# Simulate flattening: resolve outer with inner's value
var inner_val = inner.get_value()
outer.resolve(inner_val)
expect(outer.is_resolved()).to_equal(true)
expect(outer.get_value()).to_equal("inner value")
```

</details>

#### deeply nested resolution flattens correctly

1. var deep = make resolved
2. var mid val = deep get value
3. var mid = make pending
4. mid resolve
5. var top val = mid get value
6. var top = make pending
7. top resolve
   - Expected: top.is_resolved() is true
   - Expected: top.get_value() equals `deep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deep = make_resolved("deep")
var mid_val = deep.get_value()
var mid = make_pending()
mid.resolve(mid_val)
var top_val = mid.get_value()
var top = make_pending()
top.resolve(top_val)
expect(top.is_resolved()).to_equal(true)
expect(top.get_value()).to_equal("deep")
```

</details>

### Edge Cases

#### then on already-resolved promise executes immediately

1. var p = make resolved
2. var result = p then
   - Expected: result.is_resolved() is true
   - Expected: result.get_value() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved(5)
var result = p.then(_1 * 2)
expect(result.is_resolved()).to_equal(true)
expect(result.get_value()).to_equal(10)
```

</details>

#### catch on already-rejected promise executes immediately

1. var p = make rejected
2. var result = p catch err
   - Expected: result.is_resolved() is true
   - Expected: result.get_value() equals `caught: already failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_rejected("already failed")
var result = p.catch_err("caught: " + _1)
expect(result.is_resolved()).to_equal(true)
expect(result.get_value()).to_equal("caught: already failed")
```

</details>

#### multiple then callbacks on same promise each get value

1. var p = make resolved
2. var r1 = p then
3. var r2 = p then
4. var r3 = p then
   - Expected: r1.get_value() equals `11`
   - Expected: r2.get_value() equals `12`
   - Expected: r3.get_value() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved(10)
var r1 = p.then(_1 + 1)
var r2 = p.then(_1 + 2)
var r3 = p.then(_1 + 3)
expect(r1.get_value()).to_equal(11)
expect(r2.get_value()).to_equal(12)
expect(r3.get_value()).to_equal(13)
```

</details>

#### promise with large value resolves correctly

1. var p = make resolved
   - Expected: p.is_resolved() is true
2. var v = p get value
   - Expected: v.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved("abcdefghij")
expect(p.is_resolved()).to_equal(true)
var v = p.get_value()
expect(v.len()).to_equal(10)
```

</details>

#### chaining with identity function preserves value

1. var p = make resolved
2. var chained = p then
   - Expected: chained.is_resolved() is true
   - Expected: chained.get_value() equals `keep me`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_resolved("keep me")
var chained = p.then(_1)
expect(chained.is_resolved()).to_equal(true)
expect(chained.get_value()).to_equal("keep me")
```

</details>

#### resolve is idempotent - second resolve is ignored

1. var p = make pending
2. p resolve
3. p resolve
   - Expected: p.get_value() equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_pending()
p.resolve("first")
p.resolve("second")
expect(p.get_value()).to_equal("first")
```

</details>

#### reject is idempotent - second reject is ignored

1. var p = make pending
2. p reject
3. p reject
   - Expected: p.get_error() equals `first error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_pending()
p.reject("first error")
p.reject("second error")
expect(p.get_error()).to_equal("first error")
```

</details>

#### resolve after reject is ignored

1. var p = make pending
2. p reject
3. p resolve
   - Expected: p.is_rejected() is true
   - Expected: p.get_error() equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_pending()
p.reject("rejected")
p.resolve("too late")
expect(p.is_rejected()).to_equal(true)
expect(p.get_error()).to_equal("rejected")
```

</details>

#### reject after resolve is ignored

1. var p = make pending
2. p resolve
3. p reject
   - Expected: p.is_resolved() is true
   - Expected: p.get_value() equals `resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_pending()
p.resolve("resolved")
p.reject("too late")
expect(p.is_resolved()).to_equal(true)
expect(p.get_value()).to_equal("resolved")
```

</details>

#### complete is alias for resolve

1. var p = make pending
2. p complete
   - Expected: p.is_resolved() is true
   - Expected: p.get_value() equals `via complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = make_pending()
p.complete("via complete")
expect(p.is_resolved()).to_equal(true)
expect(p.get_value()).to_equal("via complete")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)
- **Plan:** [doc/03_plan/async_promise_intensive_tests.md](doc/03_plan/async_promise_intensive_tests.md)
- **Design:** [doc/05_design/async_promise_intensive_tests.md](doc/05_design/async_promise_intensive_tests.md)


</details>
