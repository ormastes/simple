# Browser animation target blocked by `JsValue.Symbol` lowering

## Evidence

The pure-Simple stage-2 compiler built successfully from commit `22ab90dbf881`,
then failed the production browser animation fixture while compiling
`src/lib/nogc_sync_mut/js/engine/interpreter.spl`:

```text
mir: Unsupported HIR construct: unknown variant or method 'Symbol' on enum JsValue
```

Reproduction:

```sh
build/browser-full-refresh/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --source src --entry test/fixtures/browser_script_css_animation/main.spl \
  --entry-closure --backend cranelift --runtime-bundle auto \
  -o build/browser-target-evidence/browser_script_css_animation
```

## Required fix

Trace every `JsValue.Symbol` construction and pattern through HIR-to-MIR enum
resolution, fix the shared qualified-variant lowering, and rerun the fixture.
Do not replace symbols with strings or use the Rust seed as target evidence.
