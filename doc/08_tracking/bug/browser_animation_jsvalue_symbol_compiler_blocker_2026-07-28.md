# Browser animation target blocked by `JsValue.Symbol` lowering
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Triage 2026-11-25 (fleet lane p2w1-ai, worktree wt-p2w1-ai, release/1.0.0 HEAD 50adb6f42ce)

SKIP — left open, but the specific blocking construct no longer exists in the
tree:

- `src/lib/nogc_sync_mut/js/types/js_types.spl:7-15`: `enum JsValue` now has
  only `Undefined/Null/Boolean/Number/String/Object/Array/Function` — there
  is **no `Symbol` variant** and no `JsValue.Symbol` construction or pattern
  anywhere under `src/lib/nogc_sync_mut/js/` (grep-verified). `interpreter.spl`
  was split (`interpreter_eval*.spl`) and `Symbol.iterator`/`Symbol.asyncIterator`
  are handled as plain strings.
- The required-fix verification (rebuild stage2, native-build the
  `browser_script_css_animation` fixture) needs a full bootstrap-scale
  compiler build, which this lane cannot perform; an interpreter-mode run of
  the fixture on the pinned seed exceeded a 180 s timeout while still
  executing, so it is not evidence either way.

Net: the named `JsValue.Symbol` lowering blocker cannot recur in its filed
form (the variant is gone), but the underlying qualified-enum-variant
lowering question and the stage2 fixture re-run remain unverified — leaving
OPEN for an owner with bootstrap capacity.
