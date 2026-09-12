# Browser animation target blocked by `JsValue.Symbol` lowering
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
