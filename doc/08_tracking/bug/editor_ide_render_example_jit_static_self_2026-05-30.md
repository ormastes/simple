# Bug: IDE render example falls back from JIT on static-method self diagnostic

Date: 2026-05-30
Status: open (triaged 2026-06-11, JIT proof still open per body)

## Observation

Running the embedded IDE render example succeeds through interpreter fallback:

```bash
bin/simple run examples/10_tooling/ide/simple_ide_render.spl
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
`test/01_unit/lib/editor/editor_launch_contract_spec.spl`, but it does not yet
prove the JIT/native path for shared editor GUI/WebRender rendering.

## Follow-Up

Identify which imported shared editor/WebRender helper triggers the static-method
`self` diagnostic under JIT lowering, then either fix the lowering bug or adjust
the helper to avoid the unsupported form.

## 2026-05-30 Update

The hardcoded HTML smoke has been replaced with the shared editor GUI backend
and WebRender envelope path again. The source-side resolver used by the current
compiler resolves `std.editor.backend.*` through numbered layer directories such
as `src/lib/editor/70.backend`.

Verification after refreshing `bin/simple` from the rebuilt bootstrap binary:

```bash
cd src/compiler_rust && cargo test -p simple-compiler resolves_numbered_stdlib_imports_from_examples_tree -- --nocapture
cd ../.. && SIMPLE_LIB=src bin/simple check examples/10_tooling/ide/simple_ide_render.spl
SIMPLE_LIB=src bin/simple run examples/10_tooling/ide/simple_ide_render.spl
bin/simple run examples/10_tooling/ide/simple_ide_render.spl
bin/simple test test/01_unit/lib/editor/editor_launch_contract_spec.spl --mode=interpreter --clean
bin/simple run examples/10_tooling/ide/simple_ide_launch.spl
```

The example prints:

```text
target=pure_simple
has_editor_source=true
has_markdown_language=true
```

## 2026-05-30 Recovery Recheck

The recovered editor/IDE crash-session audit still proves the shared
GUI/WebRender path through interpreter fallback:

```bash
SIMPLE_LIB=src bin/simple run examples/10_tooling/ide/simple_ide_render.spl
bin/simple test test/01_unit/lib/editor/editor_launch_contract_spec.spl --mode=interpreter --clean
```

Current fallback text is:

```text
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown type: RenderBlock
```

Functional status remains PASS for the embedded example render contract, but the
JIT/native proof remains open under this bug until the imported render block
type is available to HIR lowering.
