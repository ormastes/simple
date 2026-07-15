# Parser: `@step "label"` decorator form fails — "expected Fn, found FString"

Date: 2026-07-02
Status: source fix implemented; focused execution pending
Severity: P3
Related: .claude/templates/spipe_template.spl, SPipe SSpec authoring

## Symptom

The SPipe template (`.claude/templates/spipe_template.spl`) shows the
decorator form on its own line before a function:

```simple
@step "Open the application"
fn open_app():
    ...
```

Parsing any spec that uses this form fails:

```
parse: Unexpected token: expected Fn, found FString([Literal("Open the application")])
```

Working specs in the tree all use the comment form `# @step: ...` instead.
Either the parser should accept the decorated-string form the template
advertises, or the template should be corrected to the comment form.

## Repro (verified 2026-07-02)

`bin/simple run` any spec containing `@step "x"` above a top-level `fn`,
e.g. the pre-fix version of
`test/03_system/check/gui_low_res_readability_spec.spl`.

## Workaround

Converted the spec's `@step "..."` lines to `# @step: ...`.

## Resolution (2026-07-15)

The shared declaration parser now consumes the one string label following a
`step` decorator before continuing with stacked decorators or the function.
`parser_attribute_spec.spl` covers `@step "..."` followed by `@inline` and
asserts both a clean parse and the expected declaration. Execution awaits a
runnable pure-Simple test artifact.
