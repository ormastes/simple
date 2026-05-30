# Bug: IDE render example falls back from JIT on static-method self diagnostic

Date: 2026-05-30

## Observation

Running the embedded IDE render example succeeds through interpreter fallback:

```bash
bin/simple run examples/ide/simple_ide_render.spl
```

Observed output includes the expected render proof:

```text
target=pure_simple
has_editor_source=true
has_markdown_language=true
```

but also reports:

```text
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: cannot use `self` in static method
```

## Impact

The example is functionally valid and covered by
`test/unit/lib/editor/editor_launch_contract_spec.spl`, but it does not yet
prove the JIT/native path for shared editor GUI/WebRender rendering.

## Follow-Up

Identify which imported shared editor/WebRender helper triggers the static-method
`self` diagnostic under JIT lowering, then either fix the lowering bug or adjust
the helper to avoid the unsupported form.
