# Native/AOT has no erased by-name method dispatch — and cannot have one without an object-model change

**Date:** 2026-08-18
**Status:** OPEN — design note. No code change landed. **No build was verified** (see "What I did NOT verify").
**Engine under discussion:** native/AOT only. Not the tree-walk interpreter (`simple test`), not the Cranelift JIT (`simple run`).

## Summary

`native-build` fails an erased-receiver method call with
`MIR lowering error: unresolved method call: <name>`. A sibling lane fixed the
equivalent JIT defect at `4b487af8ea17` in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`. **That fix
cannot be ported, because native/AOT does not go through that file at all.**

Two structural findings, both read directly out of the tree at
`1897ee732e8` (`/mnt/data/worktrees/simple-stage4-clean`):

1. **Different compiler.** `bin/simple native-build` does not lower with the
   Rust seed's MIR. It spawns
   `timeout --kill-after=10s 7200s ... simple run src/app/cli/native_build_worker.spl <args>`
   — i.e. the seed JITs the **pure-Simple** compiler (`src/compiler/**`) and
   *that* does the native build. Observed live in the process table. So the
   failure site is `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`,
   not `lowering_expr_method.rs`. Any port of the JIT fix to the Rust file
   would change nothing on this lane.

2. **The native MIR has no dynamic-dispatch instruction whatsoever.**
   `grep -rn "MethodCallVirtual\|VirtualCall\|CallVirtual" --include=*.spl src/compiler/`
   returns **zero lines**. `grep -rln vtable --include=*.spl src/compiler/`
   returns two files, neither of which emits one
   (`70.backend/backend/llvm_ir_builder.spl` mentions it only in a comment).
   The runtime has no by-name lookup either: no `rt_method_lookup`,
   no `rt_class_name`, no method-name table anywhere under `src/runtime/` or
   `src/compiler_rust/runtime/`.

## The crux: is the receiver's concrete type available at the native lowering site?

**Sometimes — and exactly where it is, it is already correct. Where it is not,
it is unrecoverable, at lowering time AND at run time.**

The `case Unresolved:` arm already does receiver-type-keyed dispatch
(`method_calls_literals.spl` ~2680-2800):

```
val unresolved_struct_name = self.struct_value_syms.get(unresolved_receiver_local.id)
val unresolved_method_key  = "{unresolved_struct_name}::{method}"
... self.struct_method_syms[unresolved_method_key]
```

`struct_value_syms : Dict<i64, text>` maps a **MIR local id → the concrete
type NAME**, and `struct_method_syms` maps `"{Type}::{method}" → SymbolId`.
This is exactly the discipline the coordinator requires: it keys on the
receiver's actual type, never on name/layout unanimity, so the
`length=5 → length=130433` failure class cannot arise through it. Method
symbols are owner-qualified during HIR lowering, so two classes may share a
method name safely.

`struct_value_syms` is populated only from statically-derivable sites:

| site | file |
|---|---|
| struct/class construction | `_MirLoweringExpr/switch_operators_calls.spl:3612` |
| `let` binding aliases the constructed local | `mir_lowering_stmts.spl:857/870`, `:1081` |
| params whose declared type is a named struct/class | `_MirLowering/function_lowering.spl:349/381/383` |
| match-payload bindings, for-loop element types | `switch_operators_calls.spl:2571`, `mir_lowering_stmts.spl:2738` |

Consequences:

* **`val d: Any = Dog()` is statically recoverable.** The `Any` annotation does
  not erase anything here: `lower_struct_construct` writes
  `struct_value_syms[dest] = "Dog"`, and the `let` path aliases the binding
  straight to that local whenever `struct_sym != nil` — the annotated type is
  not consulted on that branch. So this case *should* already resolve, and if
  it does not, the defect is a narrow propagation gap, not a missing feature.
* **`fn f(x: Any)` is NOT recoverable.** The param arm is gated on
  `self.struct_field_order.has(parameter_type.name)`; `Any` is not a struct, so
  nothing is registered, the key degrades to `"::speak"`, and the call falls to
  the loud failure. **This is correct.** The concrete type genuinely differs
  per call site, and MIR lowering here is a single syntax-directed pass with no
  dataflow, no points-to analysis and no whole-program call graph. There is no
  sound static answer to recover.
* **A runtime answer is also unavailable today.** Native class layout is
  `struct_field_order[class_def.name] = field_names`
  (`_MirLowering/module_lowering.spl:1224`) — the **declared fields only**.
  There is no synthetic type-id header slot, so a native class instance
  reaching an `Any` carries **no runtime type identity at all**. Nothing can be
  switched on at run time even in principle.

**So: the receiver type is not obtainable at the native lowering site for a
genuinely erased receiver, and the object model provides nothing to obtain it
at run time either. That is the finding.** It is not a lowering bug; it is a
missing object-model feature.

## Current failure mode is the right one — do not regress it

`method_calls_literals.spl:3240-3275` collects `self.error("unresolved method
call: {method}")` **and** emits an `rt_panic` ahead of the const-0 placeholder,
precisely because several lanes (notably
`driver_bootstrap.bootstrap_lower_to_mir_context`) drop the collected error
list. So native fails closed at build time, and closed again at run time in the
lanes that swallow the build error. Any change here must preserve both.

## Smallest correct increment (in order)

1. **Do nothing to the erased case; fix only the propagation gap.** Confirm
   with `scripts/check/check-native-erased-dispatch.shs` whether
   `val d: Any = Dog()` already resolves. If it does not, the fix is to carry
   `struct_value_syms` across whatever boxing step the `Any` annotation
   introduces — a few lines, receiver-type-keyed, no new machinery. Cost: one
   lane.
2. **Sharpen the diagnostic.** When the receiver is `Any`/erased and the method
   name *does* exist on one or more classes, say so:
   `unresolved method call: 'speak' on an erased (Any) receiver; native/AOT has
   no dynamic dispatch — candidates: Dog::speak, Cat::speak`. Today's message
   is indistinguishable from "no such method anywhere". Cost: one lane.
   **Explicitly do NOT dispatch to the unique candidate when there is only
   one** — that is name unanimity, the exact reasoning that produced
   `length=130433` on the sibling lane.
3. **Only then, the real feature**: a type-id header word on every
   heap-allocated class instance, a per-module `(type_id, method_name) →
   fn_ptr` table emitted into the binary, a `MirInst` for a dynamic call, LLVM
   emission for it, and a runtime `rt_method_lookup`. Four layers
   (`50.mir`, `60.mir_opt`, `70.backend`, `src/runtime`) plus an ABI change to
   every class layout. **This is multiple lanes and needs its own design
   review — it is not a bugfix.**

## Test family (written, NOT run)

`scripts/check/check-native-erased-dispatch.shs` +
`scripts/check/fixtures/native_erased_dispatch/`:

| fixture | expectation |
|---|---|
| `any_local_noarg.spl` | builds, prints `A=7` |
| `any_local_args.spl` | builds, prints `B=21` |
| `any_local_same_name_two_classes.spl` | prints `C=7` **and** `D=42` — the wrong-method detector |
| `any_local_unique_name.spl` | prints `E=101` |
| `any_param_two_classes.spl` | must FAIL CLOSED, loudly |
| `any_local_missing_method.spl` | must FAIL CLOSED, loudly |

The script builds with `native-build` and executes the resulting **binary**;
it never invokes `simple test` or `simple run`, and it does not use the unsound
`2^60` engine control. It asserts exact stdout lines, not exit status. rc is
read on the line after each command; 137/143/144 with no result line is
`ERROR — nothing was checked` (exit 2), never a pass or a fail; 139 is FAIL.

## What I did NOT verify

* **No native build completed.** Every attempt was killed. `native-build` of a
  20-line fixture was measured at ~**19 GB RSS** on this host and the
  coordinator reaped my workers to protect a Stage-3 bootstrap (`earlyoom`
  killed a 65.7 GB bootstrap at 06:35 the same morning). Last direct worker run
  ended `rc=137` → **UNVERIFIED**, not failed.
* Therefore the parent lane's report that the `Any` fixture "fails 5×" is
  **not reproduced here**, and the prediction in step 1 above — that
  `val d: Any = Dog()` may already resolve — is a **source reading, not a
  measurement**. It is the first thing to check when the box frees up.
* Whether the JIT-fallback defect seen on this tree
  (`HIR lowering error: Cannot infer field type: struct 'Span' field 'end'
   [in src/app/cli/native_build_worker.spl]: whole module dropped to the
   interpreter`) contributes to the 19 GB / multi-hour native-build cost. It is
  a separate, unfiled-here observation and may deserve its own record.
* Nothing about aarch64/riscv or any non-x86_64 native target.

## Reproduce (when the host is free — one at a time)

```sh
awk '/MemAvailable/{print int($2/1048576)"G"}' /proc/meminfo   # wait for >= 40G
sh scripts/check/check-native-erased-dispatch.shs
```
