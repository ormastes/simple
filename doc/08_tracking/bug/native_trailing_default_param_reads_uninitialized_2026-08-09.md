# Native codegen: an omitted trailing default parameter reads an UNINITIALIZED slot

Status: **FIXED** — the MIR call-lowering pad has landed
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

## What was NOT fixed by the prerequisite alone (now fixed here)

Instrumenting `fill_call_defaults` at its entry and rebuilding proved it is
**never called** under `native-build` (`dbg-fill: 0`). The whole
`35.semantics/resolve.spl` pass does not run on the AOT lane, so plumbing
`has_default` through was necessary but not sufficient. The repro still
reproduced after the prerequisite fix alone.

Two further gaps existed in `fill_call_defaults` even where it does run:

- it only handled **same-module direct free-function calls** (`Var(sym)` present
  in `module_functions`); cross-module callees were skipped by design. The WM
  case (`Engine2dWmFrameExecutor.create_host_gpu`) is cross-module.
- the `MethodCall` arm (`resolve.spl:364`) had **no default fill at all**, so
  static/instance methods were never padded.

**Correct fix (landed):** pad omitted trailing arguments during **MIR call
lowering** (`src/compiler/50.mir/_MirLoweringExpr/`), which is on the live AOT
path and sees every call kind (free function, method, cross-module) against the
callee's registered signature. `resolve.spl` was intentionally left untouched —
that pass is not on this lane.

## The fix

- `src/compiler/50.mir/mir_data.spl` — new `_bootstrap_fn_param_defaults`
  registry (`bootstrap_fn_param_defaults_register` /
  `bootstrap_fn_param_defaults_lookup`), keyed by callee name, storing the
  callee's full `[HirParam]` (not just the default expressions) so the pad
  knows both per-index `has_default` and the declared arity. Ambiguous
  (differently-shaped) same-name definitions are dropped and never answered,
  same policy as the sibling return-type/return-shape registries.
- `src/compiler/50.mir/_MirLowering/module_lowering.spl` — the existing
  cross-module prescan (the only pass that sees every module before any is
  lowered) now also registers each function's params into the new registry,
  under three spellings: the function's own name, its symbol's owner-qualified
  name (`Owner::method`), and that name with `::` rewritten to `.` — because
  `symbol_to_operand` (`method_calls_literals.spl:3207`) always performs that
  same `::`→`.` rewrite before a method-call operand ever reaches the pad's
  lookup, so the registration key has to match what the lookup actually asks
  for.
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` — new
  `pad_trailing_default_args(func, args_in)`, wired into
  `emit_resolved_direct_call`, the choke point for direct free-function and
  static-method calls. Defaults are lowered as **expressions** via
  `lower_expr`, so a default that is a call (`= dep_seven()`) or a const
  expression (`= 3 * 5 + 1`) works, not just a literal. The pad is
  all-or-nothing: if any omitted trailing slot lacks a declared default, the
  arg list is returned untouched.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` — the
  `InstanceMethod`, `TraitMethod`, `FreeFunction` (UFCS), and the
  `Unresolved`-arm name-derived custom-owner dispatch all call `b.emit_call`
  **directly**, bypassing `emit_resolved_direct_call` entirely, so each needed
  its own `pad_trailing_default_args` call. For all of these, `arg_operands[0]`
  is the receiver and the registered `HirFunction.params[0]` is the synthetic
  `self` parameter (`20.hir/hir_lowering/_Items/declaration_lowering.spl:317`)
  — the two already align 1:1, so the **full** array (receiver included) is
  passed to the pad. An earlier draft of this fix stripped the receiver before
  padding and re-prepended it after; that shifted every index by one, which
  both broke the arity check (a real explicit arg misread as "needs a
  default") and, once padding did trigger, duplicated an already-supplied
  argument instead of appending the missing one. Caught by the fixture's
  instance/static-method calls before landing, not by inspection.

## Coverage

Verified via `scripts/check/check-native-trailing-default-param.shs` against
`test/fixtures/native_trailing_default_param/{main,dep}.spl`:

| shape | covered |
|---|---|
| same-module free function, literal defaults | yes |
| cross-module free function | yes |
| default is a **call expression** (`= dep_seven()`) | yes |
| default is a **const expression** (`= 3 * 5 + 1`) | yes |
| instance method | yes |
| static method | yes |
| trait method | yes (code path patched; not exercised by the fixture) |
| UFCS free-function-as-method call | yes (code path patched; not exercised by the fixture) |

Not covered: a default parameter that is itself another parameter reference
(`fn f(a: i64, b: i64 = a)`) — not attempted; `lower_expr` would need the
callee's own parameter locals in scope, which they are not at the call site.
No such default exists in the repo today; if one is added, this pad will
silently mis-lower it (whatever `lower_expr` resolves the bare name to at the
*call site*, not the callee's `a`) rather than reject it. Filed as a follow-up,
not blocking: the blast-radius section below lists only trailing-literal/
const/call defaults, none of which hit this case.

Sabotage-tested: with `pad_trailing_default_args` short-circuited to
`return args_in` (no padding), the fence fails closed — every omitted slot in
the fixture reads back a different garbage value than the correct run,
confirming the fence is not vacuously green.

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

`scripts/check/check-native-trailing-default-param.shs`, landed alongside the
fix. Not yet added to `scripts/check/check-aot-lane-fences.shs`'s `FENCES`
roster — that aggregator wiring is a follow-up, tracked separately; run the
script directly in the meantime. `bin/simple test` hard-defaults to the
tree-walk interpreter, which binds defaults correctly, so **no spec can ever
observe this defect** — only a script driving `native-build` directly can.
