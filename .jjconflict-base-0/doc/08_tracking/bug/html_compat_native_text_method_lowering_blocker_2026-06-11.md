# html_compat native text method lowering blocker

Date: 2026-06-11
Status: Partially fixed 2026-07-03 (rt_any_add symbol+ABI gap fixed & component-verified;
        full native spec verification blocked on a broken pure-Simple bootstrap +
        a separate seed-codegen renderer-execution infinite loop — see 2026-07-03 section)

## Verification 2026-07-03 (root-caused + partial fix)

The remaining native blocker is NOT text-method lowering. `substring`/`slice`
were already resolved (see the 2026-06-11 note below), and no renderer text
method is missing a runtime symbol. The actual `--mode=native` failure is the
dynamic ANY+ANY add helper `rt_any_add`.

### How `--mode=native` really runs

`bin/simple test --mode=native` compiles the (wrapped) spec to a `.smf`
(native code + relocations) via `simple compile … -o x.smf`, then loads/runs
that `.smf`. It is the compiler codegen path, not the interpreter — which is
why erased-operation lowering surfaces here and not in interpreter mode.

### Reproduction on this host (aarch64-apple-darwin)

    bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/\
      simple_web_flex_grow_weighted_spec.spl --mode=native --clean   # FAILS

Running the compiled `.smf` directly exposes the raw crash:

    error: load failed: relocation failed: Undefined symbol: _rt_any_add

(The stale deployed `bin/simple`, built Jun 6, additionally reports
`Undefined symbol: _rt_len`; `rt_len` was only force-kept on 2026-07-01, so the
Jun-6 binary predates it.)

### Root cause

The MIR lowering emits a call to `rt_any_add` whenever both operands of `+` are
ANY-typed (untyped params / erased values), which happens inside the HTML
layout renderer (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`,
`if op == BinOp::Add && left.ty == ANY && right.ty == ANY`). But `rt_any_add`
(defined `pub extern "C"` in `runtime/src/value/collections.rs`) was registered
in NEITHER place it needs to be:

1. Missing from `RUNTIME_SYMBOL_NAMES` (`common/src/runtime_symbols.rs`).
   `runtime/build.rs` force-keeps exactly the names in that list; absent, the
   symbol is dead-stripped from the binary and the SMF loader cannot resolve it
   → hard load failure `Undefined symbol: rt_any_add`.
2. Missing from `RUNTIME_FUNCS` (`compiler/src/codegen/runtime_sffi.rs`). The
   Cranelift call path (`instr/calls.rs`) only reaches a runtime call for names
   in `ctx.runtime_funcs` (populated from `RUNTIME_FUNCS`), and
   `get_runtime_return_type()` returns `None` for unlisted names, so even once
   the symbol resolves the call's *result is never captured* → silently yields 0.

### Fix (this change)

* `common/src/runtime_symbols.rs`: add `"rt_any_add"` to `RUNTIME_SYMBOL_NAMES`.
* `compiler/src/codegen/runtime_sffi.rs`: add
  `RuntimeFuncSpec::new("rt_any_add", &[I64, I64], &[I64])` (two RuntimeValue
  args + one RuntimeValue return, all i64-sized, like `rt_string_concat`).

Rebuild seed: `cargo build --profile bootstrap -p simple-driver -p simple-native-all`.

### Component verification (rebuilt seed)

`fn f(a: any, b: any) -> any: a + b` compiled+run as `.smf`:

    f(3, 4)       -> 7          (was: Undefined symbol at load)
    f("foo","bar")-> foobar

i.e. the symbol now resolves AND the ABI is correct. The 56 `rt_*` symbols the
renderer references are now all resolvable and all have specs (`rt_any_add` was
the only gap). Node interpreter-lane bitmap gate re-run:
`check-simple-web-engine2d-js-bitmap-evidence.shs` (JS_RENDER_RUNTIME=node)
`status=pass mismatch_count=0` — no interpreter-lane regression.

### Why full `--mode=native` spec verification is still blocked here

The `rt_any_add` fix is correct and necessary but could not be proven
end-to-end through `bin/simple test --mode=native` on this host, for two
reasons that are INDEPENDENT of this fix and pre-existing:

* The deployed `bin/simple` is the Jun-6 self-hosted binary and predates both
  `rt_len` (force-kept 2026-07-01) and this `rt_any_add` fix. Rebuilding it via
  `scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple` fails at **stage 2**
  native-build (`native-build worker exited with code 1 (no binary produced)`,
  even for the minimal `bootstrap_main.spl` entry). The pure-Simple bootstrap is
  broken on this host, so `bin/simple` cannot be redeployed to carry the fix.
* The Rust seed compiles the renderer `.smf` successfully, but its native code
  **infinite-loops at runtime** (>200 s at 99% CPU with no output; trivial
  programs run instantly). This is a SEPARATE seed-codegen defect surfaced only
  after `rt_any_add` unblocked loading — not the same bug. A likely-related
  observation: untyped/erased params marshal as raw payloads and read back as 0
  in native (`fn ident(a): a` → `ident(3)` prints `0`, `ident("hi")` prints
  `0`), which can drive a non-terminating loop counter. Root cause not isolated.

Net: land the `rt_any_add` symbol+ABI fix (real, verified). Full native
assertion verification of the renderer specs remains gated on (a) repairing the
pure-Simple stage-2 bootstrap so `bin/simple` can be rebuilt/redeployed, and
(b) the separate erased-value native-execution infinite loop.

## Verification 2026-07-02

## Verification 2026-07-02

The blocker persists for full renderer-driven specs compiled natively. Both
`test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl` and the new
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl`
pass under the default interpreter runner but fail immediately (subprocess
crash) under `bin/simple test --mode=native`. This is the same native
text-method / string-runtime lowering gap in the HTML layout renderer closure,
not a layout-geometry defect: interpreter-mode probes produce the correct
weighted flex-grow widths (400px 1:2:1 -> 100/200/100; 240px fixed+1:2 ->
40/67/133) and correct wrap-reverse ordering. No compiler hack applied; the
gap is left for a dedicated native string-lowering fix.

## Summary

The focused HTML compatibility geometry path no longer proves a
`06_card_panel` zero-box layout failure. Interpreter mode returns three
`06_card_panel` boxes and four `24_flex_wrap_reverse_basic` boxes through the
focused native smoke input.

Native evidence was blocked before execution by text-method lowering in the
HTML renderer closure. The blocker is resolved for `substring` in this slice:
the Rust seed LLVM builtin-method path maps `String.substring` to existing
`rt_slice`, and the Pure Simple MIR lowering mirrors typed `text.substring` /
`text.slice` to the native string slice runtime.

## Repro

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple compile \
  src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl \
  --native \
  --output build/tmp/html_compat_geometry_probe_native_full_smoke \
  && build/tmp/html_compat_geometry_probe_native_full_smoke
```

Previously observed after removing iterable `for` loops from the focused
closure:

```text
error: codegen: undefined symbol: str.substring
```

Resolved evidence with the patched bootstrap compiler:

```text
Compiled src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl -> src/app/wm_compare/html_compat_geometry_probe_native_full_smoke
status=pass
```

Before that cleanup, the same native closure failed earlier with:

```text
error: codegen: undefined symbol: rt_for_iterable
```

## Interpreter Control

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple run \
  src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl \
  --mode=interpreter --clean
```

Observed:

```text
fixture=06_card_panel count=3
fixture=24_flex_wrap_reverse_basic count=4
status=pass
```

## Current Assessment

This was a native compiler/runtime lowering gap for method-form text operations
inside the Simple Web HTML parser/layout closure, not a proved Chromium layout
geometry mismatch for `06_card_panel`.

The earlier parser-stack suspicion was also hardened in this slice:
`parse_html()` now truncates the close-tag stack by copying the kept prefix
instead of using `pstack.pop()` in a loop. The focused native smoke now executes
through that path and returns `status=pass`.

The native smoke should remain focused on both `06_card_panel` and
`24_flex_wrap_reverse_basic` so future native work continues proving real
layout output instead of only linking.
