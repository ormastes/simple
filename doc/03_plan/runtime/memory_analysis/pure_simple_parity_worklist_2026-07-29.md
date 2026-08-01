# Pure-Simple Parity Worklist — Memory-Infra (M1-M8) 2026-07-29

Read-only audit. Scope: what the **self-hosted toolchain**
(`src/compiler` pure-Simple compiler/interpreter, deployed as
`bin/release/<triple>/simple`) has vs. what the memory-infra campaign (M1-M8)
added only on the **Rust seed** side (`src/compiler_rust`). Per repo law
(`.claude/rules/bootstrap.md`, `CLAUDE.md`), the self-hosted binary is the real
default engine for `test`/`run`/`lint` — gaps there are the ones that matter.

## Critical caveat found during this audit: the deployed `bin/simple` IS the seed

`bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`. Running
`bin/simple --version` prints:
```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```
`strings bin/release/x86_64-unknown-linux-gnu/simple | grep -c "bootstrap seed only"`
→ `1` (the literal string lives in `src/compiler_rust/driver/src/seed_warning.rs:20`,
printed unconditionally unless `SIMPLE_BOOTSTRAP=1` / `SIMPLE_RUST_SEED_WARNING=0`
/ `--seed-ok`). **The currently-deployed `bin/simple` is the Rust seed, not a
self-hosted build** — a "resting-state revert" the bootstrap rule calls an
emergency stopgap only. Every "test with the deployed binary" instruction in
this audit therefore exercises the seed, not the self-hosted pipeline; all
verdicts below come from reading `src/compiler` source plus one live probe
against the seed (useful as an analog, not as self-hosted evidence). **Filed
as a parity/deploy blocker in the worklist below (item 0).**

Live probe used for item 1 (seed, not self-hosted — see caveat):
```
SIMPLE_MEM_ATTR=1 bin/simple run test/fixture/mem_infra/attr_enabled_probe.spl
```
→ `rt_interp_call error: ... "unknown extern function: rt_mem_attr_enabled"`,
then `attr_enabled_probe: enabled=0` (the fixture treats the call as
returning a fallback/zero and keeps going — not a hard crash). This is the
**seed's own** per-function registry (`interpreter_extern/mod.rs`'s
`insert_simple!` table) missing the entry in *this build*, confirming the
registry-gap failure mode is real and diagnosable — the same failure mode the
self-hosted interpreter would show, by source inspection (item 1 below).

---

## Verdict table

| # | Item | Verdict | Evidence (file:line) |
|---|------|---------|----------------------|
| 0 | Self-hosted binary actually deployed at `bin/simple` | **GAP** | `bin/release/x86_64-unknown-linux-gnu/simple` is the Rust seed (seed-warning string present; confirmed via `--version` + `strings`). No self-hosted redeploy has landed since the M1-M8 seed work started. |
| 1 | Interpreter extern dispatch: auto-resolve vs. per-function registry | **HAS (registry model), GAP (missing entries)** | `src/compiler/70.backend/backend/interpreter_calls.spl:38-91` (`enum BuiltinTag`, `lookup_builtin_tag`) + `:255-437` (`try_call_builtin` match, 12 real builtin cases + `Unknown`). No `dlsym`/auto-resolution anywhere in `src/compiler` (`dlopen`/`dlsym`/`GetProcAddress` greps hit only linker/plugin code, never the interpreter). `rt_mem_attr_enabled`/`rt_mem_attr_set_owner`/`rt_mem_attr_report` are **not** in the table → `try_call_builtin` returns `BuiltinTag.Unknown` → falls through to `resolve_function_by_name` (`:167`), which fails for a pure `extern fn` with no HIR body → `Err(BackendError.runtime_error("function '...' not found", ...))` at `:171`. Same shape as the seed's `insert_simple!` table (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:240-266+`) — this is **not** dlsym-style auto-resolution in either engine, just two independently-maintained name→handler tables. |
| 2 | Interpreter module-owner tracking (M1 parity) | **GAP (no such concept exists)** | `EvalContext` (`src/compiler/70.backend/backend/env.spl:18-47`) holds a single `module: HirModule`, `env: Environment`, `fn_by_name` index — no owner/attribution field, no push/pop-on-call-entry stack. `call_hir_function` (`interpreter_calls.spl:182-208`) pushes/pops an `Environment` scope on every call but does nothing analogous to the seed's per-call owner switch. Seed reference: `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:27` (`function_module_owner`) + `:48-112` (owner-keyed globals swap on call entry). **Natural hook location for parity:** `call_hir_function` in `interpreter_calls.spl:182`, immediately after `ctx.env.push_scope()` — would need a `current_owner: text` (or a stack) added to `EvalContext`/`Environment` and threaded through, since `EvalContext` today is a flat struct with no owner-stack field to push onto. |
| 3 | Native backend text-arg `(ptr,len)` convention | **N/A — no such table exists; convention is manual/source-level** | `grep -rln text_arg_indices\|RUNTIME_FUNCS src/compiler` → no hits. Every extern fn in the pure-Simple compiler's own source that takes a text argument is declared with **already-split** `ptr: i64, len: i64` params (e.g. `interpreter_calls.spl:19-25`: `rt_file_read_text(path_ptr: i64, path_len: i64)`) and callers manually call `.ptr()`/`.len()` at the call site (`interpreter_calls.spl:348,359,370,386,396`). MIR lowering (`src/compiler/50.mir/_MirLowering/module_lowering.spl:953-966`) just **skips** extern function bodies entirely (`hir_function_is_extern` gate, `:310-313`) — it never touches call-site arguments, so there is no backend-level rewrite pass to update. Seed reference for contrast: `src/compiler_rust/compiler/src/codegen/instr/calls.rs:2388` (`text_arg_indices`) + `:3130` (call-site use), which auto-splits a single `text`-typed extern param — a convenience the pure-Simple pipeline has never had. **Parity implication:** `rt_mem_attr_set_owner` must be declared in `.spl` with `(name_ptr: i64, name_len: i64)`, exactly like the existing `rt_env_set`/`rt_file_write_text` pattern — no table to update, just follow the established manual idiom. |
| 4 | M5 strict-mode uninitialized-let handling | **GAP in the live interpreter; HAS only in a dead-code sibling** | The feature exists at `src/compiler/95.interp/mir_interpreter.spl:97` (`strict_mode: bool`, read from `SIMPLE_STRICT_INTERP` at `:119`) and `:413`/`:482` (overflow + uninit-read checks) — **but** `test/01_unit/compiler/interp/strict_interp_spec.spl:16-20` documents, and this audit's `grep -rl MirInterpreter src/` confirms, that this `MirInterpreter` class has **zero production callers**: it's constructed directly by its own unit spec only, and `bin/simple run` never reaches it. The actual live interpreter that `simple test`/`simple run` execute is `src/compiler/70.backend/backend/interpreter_calls.spl` (`call_hir_function`, `:182-208`) + `env.spl`'s `Environment` (`:49-59`, plain `Dict<text, Value>` scopes with **no per-binding initialized/uninitialized state at all**). **Parity task:** either (a) wire `mir_interpreter.spl`'s MIR-level interpreter into a real execution path (large — it doesn't share HIR/Environment with the live tree-walker), or (b) re-implement the same trap directly in `call_hir_function`/`Environment`, e.g. tagging scope-dict entries with an uninitialized sentinel on `let` without an initializer and checking it on read. (b) is the lower-effort, in-scope-of-the-actual-runner option. |
| 5 | rt_alloc/rt_free — which allocator executes for the self-hosted world | **HAS (native/compiled path); GAP (interpreted path)** | Single shared C allocator: `src/runtime/runtime_memory.c:249` defines `rt_alloc` (and its `rt_free` counterpart) once; both the Rust-seed-compiled and self-hosted-compiled native binaries link against the *same* runtime library — confirmed via extern declarations in the pure-Simple native backends: `src/compiler/70.backend/backend/llvm_backend.spl:416,418`, `llvm_backend_tools.spl:265,267`, `llvm_lib_translate.spl:307,309`, `cranelift_codegen_adapter.spl:622,639`. So **for compiled/native `.spl`**, the answer is exactly as assumed: the real C `rt_alloc`/`rt_free` (with the in-flight M2 guard-page/hardened-allocator work landing there) is what both engines' compiled output uses — the seed's Rust-side "hosted-mode" quarantine (`src/compiler_rust/compiler/src/interpreter_extern/memory.rs:16-113`, a **separate in-process Rust reimplementation** of alloc/free bookkeeping, keyed by pointer in a `Mutex<HashMap<usize,usize>>`) is a **seed-interpreter-only simulation** and never runs for compiled code on either engine. **New gap this audit found:** `rt_alloc`/`rt_free` are **not** in the self-hosted interpreter's `BuiltinTag` table (`interpreter_calls.spl:38-91`) — so *interpreted* self-hosted `.spl` calling them directly hits the same "function not found" path as item 1, not the real C allocator and not any hosted-mode simulation. This is a real (if narrow) hole: nothing in the self-hosted interpreter's own memory bookkeeping (e.g. any user `.spl` that manually calls `rt_alloc`/`rt_free` rather than using language-level `new`/collections) currently executes correctly under `bin/simple run` at all. |

---

## Parity task list, ranked by user impact

`simple test`/`simple run` on the self-hosted binary is what most work
actually exercises, so gaps in `interpreter_calls.spl` rank above backend/MIR
gaps that only matter for compiled/native paths.

1. **(Blocking everything else) Redeploy the self-hosted binary.** `bin/simple`
   is currently the Rust seed (item 0). None of the parity work below is
   verifiable end-to-end against the real tool until a genuine self-hosted
   `bin/release/<triple>/simple` is deployed and `--version` no longer prints
   the seed warning.
2. **Add `rt_mem_attr_enabled`/`rt_mem_attr_set_owner`/`rt_mem_attr_report`
   (and `rt_alloc`/`rt_free`, item 5) to `interpreter_calls.spl`'s
   `BuiltinTag`/`try_call_builtin` table.** (`interpreter_calls.spl:38-91,
   255-437`.) Declare `rt_mem_attr_set_owner` with the manual `(name_ptr: i64,
   name_len: i64)` split per item 3's established idiom — no backend table
   needs touching. This is the single change that makes `SIMPLE_MEM_ATTR=1`
   observable and mem-owner-taggable when running interpreted `.spl` on the
   self-hosted binary, which is the default `simple test`/`simple run` engine.
3. **Add a strict-mode uninitialized-let trap directly to the live
   interpreter** (item 4) — `call_hir_function`/`Environment` in
   `interpreter_calls.spl`/`env.spl`, not the dead-code `mir_interpreter.spl`
   sibling. Gate on `SIMPLE_STRICT_INTERP=1` exactly like the seed, default
   OFF/byte-identical.
4. **Add module-owner tracking to `EvalContext`** (item 2) so M1-style
   attribution can eventually tag interpreted allocations by the module that
   triggered them, not just by explicit `rt_mem_attr_set_owner` calls. Lower
   priority than #2/#3 — attribution already works manually via explicit
   `set_owner` calls once #2 lands; automatic module-owner sync is a
   nice-to-have on top.
5. **(Backend/native, lower priority — already works via manual idiom)** No
   text-arg table exists or is needed (item 3) — confirm any new `rt_mem_attr_*`
   `.spl` declarations follow the existing `ptr,len` manual pattern; nothing
   to build.

## Which landed `.spl` specs would start exercising this automatically

- `test/fixture/mem_infra/attr_enabled_probe.spl` +
  `test/03_system/check/mem_infra_flag_spec.spl` — currently only proven on
  "the default (cranelift) engine" (compiled path, per the spec's own text);
  once #2 lands **and** the self-hosted binary is redeployed, re-running this
  spec's fixture through `bin/simple run` (interpreted) would newly exercise
  the parity path instead of erroring "unknown extern function".
- `test/03_system/check/mem_attr_report_spec.spl` (`@cover
  src/compiler_rust/runtime/src/value/heap.rs`) — spawns a child process with
  `SIMPLE_MEM_ATTR=1`; once #2 lands this becomes a genuine cross-engine check
  rather than exercising only whatever engine the child process defaults to.
- `test/01_unit/lib/mem_infra/config_spec.spl` — pure capability-matrix logic
  in `std.common.mem_infra.config`, already engine-agnostic; unaffected by
  these gaps but is the natural place to add a self-hosted-interpreter row
  once #2/#3 land.
- `test/01_unit/compiler/interp/strict_interp_spec.spl` — explicitly documents
  today that it is "the only honest way to exercise" `MirInterpreter" because
  `bin/simple run` doesn't reach it; once #3 is implemented in the live
  interpreter instead, a new sibling spec against `interpreter_calls.spl`
  (not this dead-code class) would be the real regression gate — this spec
  itself stays as a MIR-level unit test, it does not "start passing
  differently."
