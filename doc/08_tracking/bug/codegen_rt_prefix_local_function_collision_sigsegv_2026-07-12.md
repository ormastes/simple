---
id: codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12
status: SOURCE-FIXED-EXECUTION-PENDING
severity: blocking
discovered: 2026-07-12
discovered_by: native-build redeploy verification (agent session), follow-up to
  seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md
related: src/compiler_rust/compiler/src/codegen/instr/calls.rs
related: src/compiler/10.frontend/core/lexer.spl
related: doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md
---

# Codegen: locally-defined function whose name coincidentally matches a runtime SFFI symbol name compiles to a SIGSEGV, not a call to the local body

## Resolution (2026-07-17)

The pure-Simple Cranelift adapter resolves ordinary user-authored named calls
through its local function table before declaring an external import. Its
compiler-synthesized string conversions use the unconditional runtime-import
helper. Lowering-owned array length/get/set names are kept on that runtime path
and same-named local bodies receive private object symbols.

The Rust seed now mirrors that ownership rule. Current-module function bodies
replace preloaded runtime raw-name entries, while empty extern declarations do
not displace an existing body. Native call codegen keeps compiler-owned inline
intrinsics authoritative, then resolves a non-import body before the generic
runtime SFFI path. Genuine imports retain runtime tagging and argument
expansion.

Unit coverage pins import/defined linkage and reused-backend mapping. The
existing Cranelift AOT gate builds and runs both generic and non-generic
`rt_array_len_safe` collisions. The generic fixture also carries unused local
`rt_array_len/get/set` bodies. Exact output `4`, `20`, and `25` proves the
ordinary local call wins while generated length/index/mutation operations keep
runtime ownership; the non-generic fixture independently requires `3`.
Source/static verification is complete; first staged execution with the
rebuilt seed remains pending.

This fixes the reported `rt_array_len_safe` crash without pretending MIR has
call origin. Generic compiler-generated helpers such as `rt_array_new` and
`rt_array_push` still require the explicit-origin refactor tracked in
`mir_runtime_call_origin_ambiguity_2026-07-17.md`; a portability lint prevents
new owned-code definitions of selected allocation/container helper names until
that work lands.

**Status:** SOURCE FIXED — staged Cranelift execution pending.
**Severity:** Blocking for the real self-hosted redeploy target. Does not
block `native-build` from running/producing a binary in general (the sibling
interpreter-level bug is fixed — see the related doc) — this is a *different*
mechanism that only affects `.spl` programs that both (a) define a top-level
function whose bare name coincidentally matches a real Rust runtime export
(any of `simple_runtime`'s exported `rt_*` symbols), and (b) call it from
compiled (not interpreter-fallback) code. **The seed's own compiler source
did exactly this at discovery**; the current surviving compiler collision is
in `src/compiler/10.frontend/core/lexer_struct.spl`, which defines
`fn rt_array_len_safe<T>(array: [T]) -> i64`, unrelated to the real runtime
export `rt_array_len_safe(array: RuntimeValue) -> i64`
(`runtime/src/value/collections.rs:432`). Once native-build's entry-closure
compiles lexer.spl to native code (rather than tree-walking it, which is what
today's `run`-based repro does), this bug will very likely fire on the actual
redeploy binary.

## Symptom

A trivial program with a local, non-extern function whose name happens to
match a real runtime symbol compiles successfully (no error at build time)
but **crashes at runtime** with a SIGSEGV as soon as the local function is
called:

```simple
fn rt_array_len_safe<T>(array: [T]) -> i64:
    return array.len()

fn main() -> i64:
    val arr: [i64] = [10, 20, 30, 40]
    val n = rt_array_len_safe(arr)
    print(n)
    return n - 4
```

```bash
SIMPLE_BOOTSTRAP=1 <fixed seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --entry probe.spl -o out
./out
```
```
[simple-runtime] Fatal: SIGSEGV at address 0x4
Backtrace:
./out[0x202164]
libc.so.6(+0x45330)
libc.so.6(+0x18b7dd)
libc.so.6(fputs+0x1a)
./out[0x202035]
```
(`RC=139`.) Reproduces identically with a non-generic
`fn rt_array_len_safe(a: [i64]) -> i64` and with the generic
`fn rt_array_len_safe<T>(array: [T]) -> i64` form (the latter matches
lexer.spl's actual signature exactly). `nm out` shows exactly one
`rt_array_len_safe` symbol landed in the binary (`T` — defined, in `.text`),
so this is not a link-time duplicate-symbol failure; the crash is a
calling-convention/ABI mismatch between the call site and whichever body
ends up wired to that call.

Confirmed this does **not** go through the interpreter SFFI bridge
(`interp_call_handler` in `interpreter_sffi.rs`, which already checks local
`funcs.get(name)` before any `rt_`-prefix fallback — see the sibling bug fix)
— a debug print placed at the top of that handler's body never fires for
this repro. The call is fully native-compiled.

## Root cause

`src/compiler_rust/compiler/src/codegen/instr/calls.rs`, function
`compile_call` (~2731-3200+ lines, a large per-callee-name dispatch
cascade). The relevant branch:

```rust
// calls.rs:2994-3088
} else if let Some(&runtime_id) = ctx.runtime_funcs.get(sffi_name) {
    // Runtime SFFI function — checked BEFORE func_ids because runtime functions
    // are also registered in func_ids for name resolution. Checking here first
    // ensures text expansion and SFFI-specific handling (tagging, return type
    // extension) is always applied for known runtime functions.
    ...
} else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
    // User-defined function (not a known runtime SFFI function)
    ...
}
```

`ctx.runtime_funcs: &HashMap<&'static str, cranelift_module::FuncId>`
(`codegen/instr/mod.rs:98`, `codegen/common_backend.rs:232`) is populated
from the compiler's static table of known runtime SFFI symbol names/argument
conventions (the codegen-side counterpart of `RUNTIME_SYMBOL_NAMES` /
`EXTERN_FUNCTIONS`, same family that caused the sibling interpreter bug).
`ctx.func_ids` is the module's own compiled-function table and, per the
comment, **does** contain an entry for the local `rt_array_len_safe` too
(codegen declares every top-level function there) — but the
`ctx.runtime_funcs` branch is checked *first*, unconditionally, with no check
for whether the name is *also* a local definition. So the call site emits a
call using the **runtime SFFI calling convention** (arg tagging/boxing,
`RuntimeValue`-typed marshalling, `rt_array_len_safe(RuntimeValue) -> i64`'s
ABI) against a symbol that, per `nm`, actually resolved to the **locally
compiled function's body** (which expects the normal Simple
array-parameter ABI, not a boxed `RuntimeValue`). The mismatch — passing a
raw array pointer/length pair to a body that tries to unbox it as a tagged
`RuntimeValue` handle (or vice versa) — is consistent with the observed
`SIGSEGV at address 0x4` (a classic small-tagged-value-dereferenced-as-pointer
crash).

This is the **exact same bug class** as
`seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`
(bulk-registered runtime-symbol-name membership checked before/instead of
local-definition presence), but in the **codegen backend** instead of the
tree-walk interpreter, and the fix pattern is analogous in spirit ("a local
definition must win over a same-named runtime symbol") but **not** a safe
copy-paste of that fix: `ctx.runtime_funcs.get(sffi_name)` returning `Some`
also carries essential SFFI-specific *codegen* behavior (arg tagging,
text/cstr expansion, return-type extension — see the ~90 lines following the
branch) that many *legitimate* runtime calls depend on, and the comment
signals this ordering was already a deliberate (if incomplete) choice, not a
plain oversight. A correct fix needs to:
1. Determine, for each `sffi_name` for which `ctx.runtime_funcs` has an
   entry, whether `ctx.func_ids` *also* has a *local* (non-imported)
   definition for the same bare name.
2. When both exist, decide correctly rather than assuming either always wins
   — a local definition should take priority for actual calls, but that must
   not silently break legitimate cases (if any exist) where a local wrapper
   intentionally shares a runtime symbol's name expecting runtime semantics.
3. Verify there is no case in the existing `.spl` stdlib that *relies* on the
   current "runtime wins" behavior (a scan for local functions whose name
   matches a `runtime_funcs` entry would establish this — not done here).

Given the size and special-casing density of `compile_call` (dozens of
`sffi_name == "..."` inline-compilation branches ahead of this point, all
implicitly assuming `sffi_name` uniquely identifies a runtime primitive) and
that this ordering appears intentional rather than accidental, this needs a
dedicated, carefully-scoped follow-up rather than a same-session patch.

## Impact

- Does **not** block `native-build` from running or producing binaries in
  general — confirmed via a trivial `fn main() -> i64: return 0` probe and a
  `fn main(): print("hello")` probe, both build and run correctly through the
  full pipeline (see the sibling bug doc).
- **Likely blocks the actual self-hosted redeploy binary from working
  correctly** once native-build's entry-closure compiles
  `src/compiler/10.frontend/core/lexer.spl` (and `parser.spl`,
  `decl_nodes.spl`, `lexer_struct.spl`) to native code and the compiled
  `main`/lexer call path reaches a compiled call to `rt_array_len_safe`
  (used constantly throughout lexing — e.g. lexer.spl lines 93, 95, 97, 99,
  ... 713). The full entry-closure build (`--entry-closure --source
  src/compiler --source src/app --source src/lib`) was still in `phase2:parse`
  (interpreted, unaffected by this codegen bug) after ~14 minutes at the time
  of writing and had not yet reached codegen, so this has not been observed
  directly on the real closure output — the risk is established via a
  signature-matching minimal repro (see Symptom), not yet via the real
  build reaching that code path.

## Suggested next steps (not attempted here)

1. Audit `ctx.runtime_funcs`'s static population table
   (`codegen/instr/mod.rs` around line 191, `common_backend.rs` around line
   232) against the full local-function-name space of `src/compiler`,
   `src/app`, `src/lib` to find every other coincidental collision (not just
   `rt_array_len_safe`) before attempting a fix, so the fix's blast radius is
   known upfront.
2. In `compile_call`, before taking the `ctx.runtime_funcs.get(sffi_name)`
   branch, check `ctx.func_ids.get(func_name)` for a *local* (not
   `Linkage::Import`) definition; if one exists, prefer the standard
   user-function call path (mirroring the interpreter-side fix in
   `interpreter_call/mod.rs::evaluate_call`) — but first confirm (step 1)
   that this doesn't regress any legitimate same-named runtime call.
3. Re-run the two repros in this doc (non-generic and generic
   `rt_array_len_safe` collisions) after the fix; both should print `4` and
   exit `0`.
4. Once fixed, re-run the entry-closure redeploy build end-to-end and confirm
   the produced binary's own lexer works (smoke: `<binary> run
   <any-source-file>.spl` should not crash while lexing).
