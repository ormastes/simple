# SSpec Anti-Patterns — What Makes an Amateur Manual

SSpec `.spl` specs are the source of truth *and* the source text for the
generated scenario manual (`bin/simple spipe-docgen <spec> --output doc/06_spec`).
The generator assembles; it never invents prose. A lazy spec yields a lazy manual
— machine noise instead of a product manual like
[`scenario_manual_example.md`](../app/spipe/scenario_manual_example.md).

The 12 anti-patterns below were each found in real specs (file:line cited); each
degrades the generated manual in a specific way. Fix the spec, not the generator.

## 1. Test-speak scenario names

`it "test 1"` (`test/01_unit/app/auto_coverage_1_spec.spl:11`) renders a manual
section literally titled **"test 1"** — the reader learns nothing.

```simple
# BAD
it "test 1":
    ...
# GOOD
it "user adds a task and sees it in the list":
    ...
```

## 2. Assert-only bodies, zero `step()`

`check(1 == 1)` (`auto_coverage_1_spec.spl:12`, `compress_tool_basic_spec.spl:11`)
gives docgen one word to render — **"check"** — and no narrative.

```simple
# BAD
it "compresses a file":
    check(compress("in") == "out")
# GOOD
it "compresses a file to the smaller archive":
    step("Compress `report.log` with the default codec")
    expect(archive.size).to_be_less_than(source.size)
```

## 3. Placeholder docstrings

`"""Comprehensive branch coverage..."""` (`branch_coverage_10_spec.spl:1-5`) is
coverage-speak. The docstring is the manual's overview — say **what / why / who**.

```simple
# BAD
"""Comprehensive branch coverage of the parser."""
# GOOD
"""Reading a config file. Operators point the CLI at a `.sdn` file; the
loader reports the first syntax error with a line number so they can fix it."""
```

## 4. Magic numerics with no domain meaning

`verify(sum == 435)` (`acceptance_1_system_spec.spl:27-35`) — 435 is 1..29 summed,
no domain meaning. A reader cannot tell what behavior passed.

```simple
# BAD
expect(total).to_equal(435)
# GOOD
val invoice_total = sum_line_items(cart)   # 3 items: 12.00 + 4.50 + 9.99
expect(invoice_total).to_equal(26.49)
```

## 5. Zero captures in user-facing specs

Sampled unit/system specs attach **no** TUI/CLI evidence, so the manual shows
steps with nothing the user recognizes. Every user-facing flow needs a `@capture`
grid (Todo example's boxed screens).

```simple
# GOOD
# @capture
it "shows the empty task list on launch":
    step("Launch `todo` from a terminal")
    expect(capture_region("task_list")).to_contain("No tasks yet.")
```

## 6. Fake system narrative

An `it "end-to-end workflow"` that is string concat + array math
(`acceptance_1_system_spec.spl:16-35`) exercises nothing real: the manual
promises a workflow and delivers arithmetic.

```simple
# BAD
it "end-to-end workflow":
    val s = "a" + "b" + "c"
    expect(s.len()).to_equal(3)
# GOOD — drive the real surface
it "operator submits an order and sees it queued":
    val res = order_service.submit(sample_order())
    expect(res.status).to_equal("queued")
```

## 7. Flat scenario dumps

When edge/matrix/stress scenarios sit inline with primary flows and no
`@manual_section` folding, the primary flow is lost in noise. Group; fold the rest.

```simple
# GOOD
# @manual_section("Adding a Task")
it "user adds a task and sees it in the list": ...

# @manual_section("Edge Cases")
# @manual: folded
it "rejects an empty task name": ...
```

## 8. Boilerplate repeated inline instead of named helpers

`fn run_for(...)` repeated per scenario (`auto_coverage_1_spec.spl:29-35`) dumps
plumbing into every manual section. Extract a named `@step` helper so the manual
reads as one sentence and the setup appears once.

```simple
# GOOD
@step "Run the tool against the sample project"
fn run_for_sample() -> text:
    return run_cli("--project", "samples/basic")
```

## 9. No troubleshooting / verification appendix

No `@troubleshooting(...)` rows and no verification metadata means the manual
lacks the *Troubleshooting* and *Verification Record* appendices (example manual's
Appendix A) that make it trustworthy.

```simple
# GOOD
# @troubleshooting(symptom: "Task not added on Enter", fix: "Type a name first")
it "rejects an empty task name": ...
```

## 10. Copy-paste "At a Glance" metadata

`compress_tool_basic` ships the template header with empty **Feature IDs** and an
unedited category line; docgen emits it verbatim atop the manual. Fill or delete.

```simple
# BAD
**Feature IDs:**            **Category:** Infrastructure | Language | ...
# GOOD
**Feature IDs:** #412   **Category:** Tooling   **Status:** Implemented
```

## 11. Internal tags leaking into user output

`(slow)` appended to every scenario name leaks a runner hint into the manual title.
Keep internal tags in annotations, not in user-visible `it` strings.

```simple
# BAD
it "rebuilds the index (slow)": ...
# GOOD
# @slow
it "rebuilds the search index for a large project": ...
```

## 12. No step vocabulary at all

With neither legacy `Given_`/`When_`/`Then_` helpers nor `step(...)` calls, docgen
has nothing to lay out as ordered steps — the manual becomes a title and a bare
assertion. Always express the flow as steps.

```simple
# BAD
it "signs in":
    expect(login("u", "p")).to_be_truthy()
# GOOD
it "operator signs in with valid credentials":
    step("Open the sign-in page")
    step("Submit a valid username and password")
    expect(session.status).to_equal("authenticated")
```

## Modern SSpec checklist

Confirm every item; `spipe-docgen` must report `0 stubs` and read cleanly.

1. **Docstring in user voice** — overview says what / why / who, not "coverage".
2. **Outcome-named `it` blocks** — user-observable result, never `test N`.
3. **`step()` imperatives** — the primary flow is ordered instruction sentences.
4. **Named `@step` helpers** — shared setup extracted, appears once, not inlined.
5. **Captures with component checks** — `@capture` grids asserted by region/id.
6. **`@manual_section` grouping/folding** — primary flow separated; edges folded.
7. **Meaningful domain values** — numbers/strings carry real-world meaning.
8. **Troubleshooting + verification metadata** — `@troubleshooting`, run appendix.
9. **`@req` traceability** — scenarios annotated with their requirement IDs.
10. **No internal tags in user output** — `(slow)`/QA hints live in annotations.

See also: [`sspec_scenario_manual.md`](sspec_scenario_manual.md) (full guide), the
target output [`scenario_manual_example.md`](../app/spipe/scenario_manual_example.md),
worked specs under [`manual_examples/`](../app/spipe/manual_examples/), and the
capture/annotation feature set (FR-1..FR-6) in
[`sspec_scenario_manual.md` requirements](../../02_requirements/feature/sspec_scenario_manual.md).
