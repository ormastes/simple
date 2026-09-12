# `expect(<text>).not_to_contain(...)` does not exist

- Status: OPEN (2026-09-12)
- Binary: deployed seed, sha256 `3d120a6f9ab5704b...`

## Symptom

`std.spec` offers `to_contain` on text but no negation, so the obvious spelling
of "this line must not name the facade" fails at run time, inside the example,
as a semantic error rather than as a matcher failure:

```
semantic: method `not_to_contain` not found on type `str`
  (receiver value: use std.nogc_async_mut.io.file_ops.{file_exists, file_read})
```

Encountered writing `test/05_perf/startup/cli_args_closure_budget_spec.spl`.

## Why it matters

The failure is indistinguishable, at a glance, from the assertion the author
meant to write failing: the example goes red either way. A spec that "passes"
after the author works around it can end up asserting something weaker than
intended. The workaround used in that spec is to collect offenders in a helper
and assert `expect(offenders.len()).to_equal(0)`, which loses the offending
line from the failure message.

## What the workaround costs

The workaround used in that spec is a top-level helper that collects the
offending lines and `expect(offenders.len()).to_equal(0)`. Verified to
discriminate: adding one `use std.io.{file_exists}` back to the fixed
`src/lib/nogc_async_mut/cli/cli_util.spl` turns the example red with
`expected 1 to equal 0`. What is lost is the offending line itself — the
message names a count, not the import that broke the rule.

## Suggested fix

Add `not_to_contain` (and the matching negations for the other text matchers)
to `std.spec`, so the negative assertion is a matcher failure naming the line.
