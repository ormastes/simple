# Native codegen: an omitted trailing default parameter reads an UNINITIALIZED slot

Status: **partially fixed** (prerequisite landed; the call-site pad is still missing on the AOT lane)
Date: 2026-08-09

## Symptom

Calling a function with fewer positional arguments than it has parameters, where
the missing trailing parameters have declared defaults, does **not** bind the
declared default under `native-build` / baremetal codegen. The callee reads
whatever happens to be in the corresponding register or stack slot.

For a trailing `bool = false` this frequently comes back **`true`**.

## Minimal repro

```simple
fn plain(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, simd: bool = false, req: bool = false) -> i64:
    print("plain simd={simd} req={req}")
    0

fn two_only(x: i64, simd: bool = false, req: bool = false) -> i64:
    print("two_only simd={simd} req={req}")
    0

fn ret_true() -> bool:
    true

fn main() -> i64:
    plain(1, 2, 3, 4, 5, 6, 7, 8, true)         # req must be false
    two_only(1, true)                            # req must be false
    plain(1, 2, 3, 4, 5, 6, 7, 8, ret_true())    # req must be false
    0
```

## Per-engine results

| engine | binary | result |
|---|---|---|
| interpreter | `bin/simple` (**Rust bootstrap seed**, banner-confirmed) | **CORRECT** — every `req=false` |
| native / AOT | `bin/simple native-build` (drives the **pure-Simple** compiler in `src/compiler`, confirmed: the `[mir-lower-expr]` diagnostics it emits exist only in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, with no Rust counterpart) | **WRONG** — `two_only(1, true)` → `req=true`; `plain(..., ret_true())` → `req=true` |

The value is garbage, not a consistent misbinding: `plain(...,true)` happened to
read `false` (that stack slot was zero) while the same call with `ret_true()`
read `true`. Anything that asserts a *specific* wrong value will be flaky; the
correct assertion is that the declared default is what is read.

## Root cause chain

1. The parser **does** record per-parameter defaults
   (`_ParserDecls/fn_struct_decls.spl:646`, `parser_decls_use.spl` →
   `decl_set_param_defaults`).
2. `decl_set_param_defaults` stored them through the `ast_decl_text_set`
   `"PARAM_DEFAULTS"` text-field store, which **never round-trips under arena
   mode** — the exact hazard already documented in the `decl_param_mut_text`
   note in `_Ast/decl_nodes.spl`. So the defaults were written and immediately
   lost.
3. Consequently `_FlatAstBridge/convert_nodes.spl` hardcoded
   `has_default: false` for every parameter, and `resolve.spl:745` documented
   that it therefore could not emit an arity error.
4. `Resolver.fill_call_defaults` (`resolve.spl:713`) is the only default-fill
   machinery for compiled code — and it is gated on `p.has_default`, so it was
   dead.
5. Nothing later pads the call. The LLVM backend
   (`_MirToLlvm/core_codegen.spl:1681`) *detects* the arity mismatch but only
   reconciles it by emitting an explicit function-type signature, so the short
   call is emitted as-is and the callee reads uninitialized storage.

The interpreter is unaffected because it binds defaults directly from
`HirFunction.params` in `backend/interpreter_calls.spl:193`, bypassing the whole
chain above.

## What was fixed (landed)

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` — added the
  `decl_param_default_text` arena pool (grown in `decl_push_default_slot` /
  `decl_ensure_slot`, mirroring `decl_param_mut_text`) and rewrote
  `decl_set_param_defaults` / `decl_get_param_defaults` to use it.
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` — `convert_decl_fn`
  now reads `decl_get_param_defaults` and sets real `has_default` / `default`.

Verified by instrumentation: defaults now round-trip end to end
(`fn=plain nparams=10 ndefaults=10`, `fn=Holder__make nparams=10 ndefaults=10`).

## What is NOT fixed — the remaining defect

Instrumenting `fill_call_defaults` at its entry and rebuilding proved it is
**never called** under `native-build` (`dbg-fill: 0`). The whole
`35.semantics/resolve.spl` pass does not run on the AOT lane, so plumbing
`has_default` through is necessary but not sufficient. The repro still
reproduces after the fix above.

Two further gaps in `fill_call_defaults` even where it does run:

- it only handles **same-module direct free-function calls** (`Var(sym)` present
  in `module_functions`); cross-module callees are skipped by design. The WM
  case (`Engine2dWmFrameExecutor.create_host_gpu`) is cross-module.
- the `MethodCall` arm (`resolve.spl:364`) has **no default fill at all**, so
  static/instance methods are never padded.

**Correct fix:** pad omitted trailing arguments during **MIR call lowering**
(`src/compiler/50.mir/_MirLoweringExpr/`), which is on the live AOT path and sees
every call kind (free function, method, cross-module) against the callee's
registered signature. Do not fix it in `resolve.spl` — that pass is not on this
lane.

## Blast radius

Every `.spl` call in the repo that omits a trailing defaulted parameter is
affected on the native/baremetal lane. Confirmed instances, both fixed by
passing the value explicitly:

- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` — flipped
  the lane from `host-gpu-fallback` to `host-gpu-required-rejected`, which fails
  closed because the gate's QEMU cmdline has no ivshmem device. This was the
  SimpleOS rung (d) blocker.
- `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl` — same
  latent bug (9 of 10 positional args), not yet observed failing.

`arm64/gui_entry_desktop.spl` passes all 10 explicitly and was never affected —
which is why commit `575eb941cf5`, that added the parameter and touched only the
arm64 entry, silently broke x86_64 without changing its call site.

## Regression fence

Belongs in `scripts/check/check-aot-lane-fences.shs` once the MIR pad lands.
`bin/simple test` hard-defaults to the tree-walk interpreter, which binds
defaults correctly, so **no spec can ever observe this defect**.
