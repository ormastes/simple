# Browser animation target blocked by `JsValue.Symbol` lowering

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## Re-verification 2026-08-17 (UI/JS slice) — NOT ACTIONED HERE (owner conflict)

Confirmed still live by CONTENT: `JsValue.Symbol` is constructed and matched at
many live sites, so the lowering blocker has real callers —
`src/lib/common/js/engine/runtime.spl:380` (`return JsValue.Symbol(id: ...)`),
`interpreter_types.spl:223,250`, `gc.spl:368`,
`vm_object_store.spl:110-111,127`, `vm_builtins.spl:155`. Nothing in the JS
engine works around or removes the variant.

**This row is SKIPPED, not fixed.** The doc's own "Required fix" is
"HIR-to-MIR enum resolution / shared qualified-variant lowering", i.e.
`src/compiler/20.hir/hir_lowering/**` and `src/compiler/50.mir/**`. Both are
explicitly claimed by other lanes in this fleet's brief, so editing them here
would be a clobber. The defect is NOT in the JS engine sources this slice owns —
`JsValue.Symbol` is a legitimate enum variant and the engine-side code is
correct; the compiler cannot lower it.

Not proven: the fixture repro was not re-run (it needs a stage-2 pure-Simple
`native-build`, unaffordable while the priority bootstrap holds the box).

Status: OPEN — reassign to the HIR/MIR enum-lowering owner.
