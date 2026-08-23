# Writing a test for code that doesn't work yet: `@tag:in-development`

You are writing a spec for something that is not finished. The test is
correct; the code isn't. You want to land the test anyway, without turning
the whole suite red for everyone else.

Add one line to the spec header:

```simple
"""Spec for the thing I am still building."""
# @tag:in-development

describe "The thing":
    it "does the thing":
        expect(thing()).to_equal(42)      # not true yet
```

That's the whole feature. No decorator, no wrapper, no per-example call.

## What it does

**In a sweep** (`bin/simple test`, `bin/simple test test/01_unit`, CI):

- The spec still **runs**. Its failure does **not** fail the suite.
- Each tagged file that failed prints one line:

  ```
  IN-DEVELOPMENT SKIP test/01_unit/thing_spec.spl (1 expected failure(s); @tag:in-development)
  ```

- The summary carries a count, right under `Results:`:

  ```
  Results: 412 total, 412 passed, 0 failed, 3 skipped
  All tests passed!
  In-development: 3 skipped (expected to fail)
  ```

**When you name the file** (`bin/simple test test/01_unit/thing_spec.spl`):

- It runs and reports the **honest** verdict — red is red, exit code 1.
  This is the mode you iterate in.

  ```
  IN-DEVELOPMENT EXPLICIT test/01_unit/thing_spec.spl — `@tag:in-development`; explicit-path run reports the honest verdict (the suite would neutralise it)
  Results: 1 total, 0 passed, 1 failed
  FAIL test/01_unit/thing_spec.spl
  ```

  Naming a **directory** is a sweep, not an explicit run.

**When it starts passing**, the sweep tells you, loudly:

```
IN-DEVELOPMENT UNEXPECTED PASS test/01_unit/thing_spec.spl (1 example(s) passed) — ready to promote: remove `# @tag:in-development`
```

Do what it says: delete the tag line. The suite does **not** go red on an
unexpected pass — making it work is good news, not a violation — but the
line will keep appearing on every run until you remove the tag.

## The tag does NOT excuse a spec that can't load

If your tagged spec fails to **load** — syntax error, broken import,
unresolvable module — it is reported as BROKEN and **still fails the run**:

```
IN-DEVELOPMENT BROKEN test/01_unit/thing_spec.spl (unresolved-module) — a spec that cannot load is a DEFECT, not unfinished work; `@tag:in-development` does not excuse it
In-development: 2 skipped (expected to fail), 1 BROKEN (failed to load — FAILS the run)
```

This is on purpose. The tag says *the feature isn't finished*; it does not
say *this file is allowed to be broken*. Without the distinction, a typo'd
import would be indistinguishable from honest unfinished work, and the tag
would become a place broken specs go to stop being counted.

If the module you need genuinely doesn't exist yet, **stub the import**, or
leave the spec untagged until it loads.

A spec that loads fine and simply declares no examples is *not* broken — it
counts as an ordinary expected failure.

## When to use it, and when not to

Use it for a test whose **subject** is unfinished — you are building the
feature and the test leads the code.

Do **not** use it for:

| situation | use instead |
|---|---|
| this host can't run it (no GPU, wrong OS) | `skip()` / `skip_it()` / `# @mode:` — a statement about the environment |
| the example is an empty placeholder | `pending()` — nothing is written yet |
| the test is flaky | neither; fix the flake or file it. A flaky test tagged in-development hides a real defect |
| the code is done and the test just fails | neither. That is a bug — fix it or file it |
| the spec won't load at all | neither — fix the load error first. Tagging it will NOT neutralise it |

Do not use it to silence a test you have stopped working on. The counts are
printed on every run precisely so that a growing in-development number is
visible; that number is a to-do list, not a shrug.

## Rules of thumb

- **Tag the file, not an example.** The tag is file-level.
- **Remove the tag in the same commit as the fix** that makes it pass.
- **A tagged spec that crashes or times out** is treated the same as a
  failing one — neutralised in a sweep, counted, printed.
- **A tagged spec that runs no examples at all** counts as an expected
  failure, not a promotion signal. An empty file will never announce itself
  as ready.

## Reading the counts in a tool

Don't grep for prose. The markers are stable constants exported from
`std.spec.in_development`: `IN_DEVELOPMENT_SKIP_MARKER`,
`IN_DEVELOPMENT_UNEXPECTED_PASS_MARKER`, `IN_DEVELOPMENT_EXPLICIT_MARKER`,
`IN_DEVELOPMENT_SUMMARY_MARKER`. To ask whether a source is tagged, call
`source_is_in_development(source)`; for the whole tag set of a file,
`spec_tags(source)`.

## Why the name is `in-development`

It reuses the existing `@tag:<name>` convention (57 names, 1022 uses in
tree), and multi-word tags in this tree are already hyphenated
(`back-compat`, `api-individual`). `pending` and `skip` were already taken
by different, narrower notions. Full rationale and the semantics decisions:
`doc/05_design/app/testing/in_development_tag.md`.
