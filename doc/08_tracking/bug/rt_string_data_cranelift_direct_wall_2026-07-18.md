---
id: rt_string_data_cranelift_direct_wall_2026-07-18
status: FIXED (two facets); one separate, unrelated bug found and left OPEN
severity: high (blocked every cranelift native-build through the self-hosted
  "cranelift-direct" interpreted adapter path)
discovered: 2026-07-18
discovered_by: lane S74 (smoke-matrix case 21 `dict_fn_return`, deterministic
  llvm-pass/cranelift-fail split)
lane: S91 (this doc); facet 1 fix landed independently by lane S81
  (`c8f1bb85e8851b0419129cedfcc66ec17f256894`, worktree `wt_clif`) and applied
  here rather than duplicated
related: src/compiler_rust/compiler/src/interpreter_extern/mod.rs
related: src/compiler_rust/compiler/src/interpreter_extern/sffi_string.rs
related: src/compiler/70.backend/backend/cranelift_codegen_adapter.spl
related: src/lib/nogc_sync_mut/sffi/codegen.spl
related: src/lib/nogc_sync_mut/ffi/codegen.spl
related: doc/08_tracking/bug/cranelift_seed_missing_sffi_externs_2026-07-16.md
related: doc/08_tracking/bug/seed_native_cranelift_dict_return_abi_2026-07-17.md
related: doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md
related: doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md
---

# The "rt_string_data cranelift-direct wall" — two stacked facets, both fixed

## Summary

Every `native-build --backend=cranelift` that reaches the self-hosted
compiler's *interpreted* "cranelift-direct" backend adapter
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`, the
pure-Simple path that drives Cranelift via `rt_cranelift_*` SFFI calls) died
immediately with:

```
[cranelift-direct] start
[cranelift-direct] target
error: semantic: unknown extern function: rt_string_data
```

Fixing that exposed a **second, independent** bug one step further in:

```
[cranelift-direct] module
[cranelift-direct] declare __simple_main
[cranelift-direct] compile main
error: semantic: function expects 2 argument(s), but more were provided
```

Both are now fixed. A **third, unrelated** bug was found while stress-testing
verification and is documented at the bottom as still open.

## Repro

Deterministic reproduction of facet 1, using the deployed self-hosted binary
(`bin/simple`, itself a natively-compiled binary that still interprets this
one `.spl` adapter file at the "cranelift-direct" call site):

```
$ env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
    --backend=cranelift --entry probe1.spl -o /tmp/probe1_bin --clean
...
[cranelift-direct] start
[cranelift-direct] target
error: semantic: unknown extern function: rt_string_data
```

where `probe1.spl` is the minimal:

```simple
fn main():
    print(42)
```

Reproducing via a **freshly built Rust seed**
(`src/compiler_rust/target/release/simple`, `cargo build --release --bin
simple`) requires unsetting `SIMPLE_BOOTSTRAP`/`SIMPLE_RUNTIME_PATH` and
invoking the same `native-build --backend=cranelift --entry <file> -o <out>
--clean`; the fresh seed additionally interprets the *entire* self-hosted CLI
+ compiler module graph to service `native-build` (it has no native Rust
implementation of that subcommand — only `compile`), so the log is ~160K
lines of import/deprecation warnings before the `[cranelift-direct]` trace
lines appear. `dict_fn_return`-shaped repro (S74's original finding) and the
minimal `probe1.spl` above hit the identical first-facet symptom; not
reproducible with a hand-rebuilt case-21-equivalent in this worktree because
this worktree's `scripts/check/native-smoke-matrix.shs` only goes up to case
19 (`dict_struct_value`) — case 21/`dict_fn_return` was added in a
not-yet-synced sibling worktree (lane S74's). A locally reconstructed
equivalent (`fn make_scores() -> Dict<text, i64>: ... ; fn main() -> i64: ...
scores["a"] + scores["b"]`) reproduces facet 1 identically but cannot be used
to verify facet 2/e2e — see "Third bug" below for why.

## Facet 1 — missing `EXTERN_DISPATCH` entry (root-caused and fixed by lane S81)

`rt_string_data` is a real, heavily-used Rust runtime function
(`runtime/src/value/collections.rs:1564`,
`pub extern "C" fn rt_string_data(string: RuntimeValue) -> *const u8`) and is
declared as an `extern fn rt_string_data(value: text) -> i64` in several `.spl`
SFFI surfaces, including `src/lib/nogc_sync_mut/sffi/codegen.spl` (used
directly by the cranelift-direct adapter's `codegen.spl` wrapper functions,
e.g. `rt_cranelift_declare_string_data(module, rt_string_data(name),
rt_string_len(name))`). It is used by natively-compiled code (LLVM/Cranelift
codegen call sites declare/link it directly), but **interpreted** calls to it
(i.e. executing the `.spl` adapter file itself via the tree-walking
interpreter, which is how the self-hosted CLI's "cranelift-direct" path runs)
go through a separate mechanism: `EXTERN_DISPATCH`, a
`HashMap<&'static str, ExternHandler>` in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`. `rt_string_data`
had **no entry at all** in that table, so every interpreted call fell through
to `interpreter_extern::dynamic_sffi`'s dlopen-based fallback — which
marshals a `Value::Str` argument as a raw *leaked `CString` pointer*, not the
tagged `RuntimeValue` the real native `rt_string_data` expects, producing
nondeterministic "type mismatch: cannot convert X to int" garbage (X varying
by run) further downstream, or the flat "unknown extern function" error when
the dlopen path itself couldn't resolve the symbol shape. Same landmine class
as the already-fixed `rt_string_bytes` gap
(`seed_flat_registry_len_i64_2026-07-17`, see MEMORY.md).

**Fix** (lane S81, commit `c8f1bb85e8851b0419129cedfcc66ec17f256894` in
worktree `wt_clif`, applied here via patch rather than reimplemented): added
`rt_string_data_fn` to `interpreter_extern/sffi_string.rs` and registered it
in `EXTERN_DISPATCH`. Introduced a shared `resolve_runtime_string` helper
that accepts *both* an already-boxed `Value::Int` (RuntimeValue handle, the
common shape after a prior `rt_string_new` round-trip) and a raw, never-boxed
`Value::Str` literal (the shape a direct call-site literal like
`cranelift_new_aot_module("bootstrap_main", target_code)` produces) — boxing
the latter on the fly via `rt_string_new`. Applied the same helper to the
sibling `rt_string_len_fn`/`rt_string_concat_fn`/`rt_string_eq_fn`, since the
same unboxed-literal shape flows through `rt_string_len` in the same
statement. Two regression tests assert the dispatch entry exists and that a
literal `"abc"` round-trips to a real pointer at the string's own UTF-8 bytes
(not a leaked/garbage pointer).

This lane (S91) independently found and root-caused the identical gap before
being redirected by the coordinator to lane S81's already-landed fix; rather
than duplicate, S81's patch was applied here verbatim (`git apply` from
`git -C wt_clif show c8f1bb85e88`) and both of its regression tests pass in
this worktree's incremental build.

## Facet 2 — stale extra argument at the one `cranelift_aot_define_function` call site (root-caused and fixed by this lane, S91)

Fixing facet 1 let the cranelift-direct path advance past module creation,
static/global declaration, and per-function declaration, into per-function
body compilation ("`[cranelift-direct] compile main`"), where it immediately
hit a **second, independent** wall:

```
error: semantic: function expects 2 argument(s), but more were provided
```

Root cause: `cranelift_aot_define_function` is declared with exactly 2
parameters in **both** duplicated SFFI surface files
(`src/lib/nogc_sync_mut/sffi/codegen.spl:353` and
`src/lib/nogc_sync_mut/ffi/codegen.spl:353`):

```simple
fn cranelift_aot_define_function(module: i64, ctx: i64) -> bool:
    rt_cranelift_aot_define_function(module, 0, 0, ctx)
```

The `0, 0` are placeholder `name_ptr`/`name_len` values for the underlying
extern `rt_cranelift_aot_define_function(module: i64, name_ptr: i64, name_len:
i64, ctx: i64) -> bool`. Checking the Rust implementation
(`src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs:1523`) confirms
this is *intentional and correct*: the parameters are named `_name_ptr` /
`_name_len` (unused) — the real function name is recovered from the
implementation's own `FINISHED_FUNCS` map, keyed by `ctx` and populated back
when the function was finished (`cranelift_end_function`), which itself
carries the name given to the earlier `cranelift_begin_function` call. So the
extern's `name_ptr`/`name_len` parameters are vestigial by design; the `.spl`
wrapper's `0, 0` placeholders are the *correct* way to call it.

The bug was at the **one call site**
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:399`, inside
`compile_function`), which passed a stale 3rd argument:

```simple
val ok = cranelift_aot_define_function(cl_module, emit_name, finished)
```

`emit_name` is not a parameter the 2-param wrapper ever declared — every call
(even the single-function `fn main(): print(42)` probe, one function, zero
parameters, zero Dict usage) triggered "function expects 2 argument(s), but
more were provided" in
`src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs`
(positional-argument-count-mismatch branch).

**Fix:** drop the redundant argument:

```simple
val ok = cranelift_aot_define_function(cl_module, finished)
```

Single-line change, single call site (verified via
`grep -rn cranelift_aot_define_function` — only one caller exists).

### How the failing call site was pinpointed

Root cause was found empirically, not by static reading alone: temporary
`SIMPLE_DEBUG_ARG_BINDING`-gated `eprintln!` instrumentation was added at all
4 call sites of `bind_args`/`bind_args_with_injected`
(`interpreter_call/core/function_exec.rs` ×2,
`interpreter_call/core/class_instantiation.rs` ×2) and at the "too many
positional args" error branches in `arg_binding.rs`, then removed again once
the culprit (`func=cranelift_aot_define_function ... params=["module", "ctx"]
args.len()=3`) was identified. **This instrumentation was reverted before the
final commit** — it was diagnostic scaffolding, not part of the shipped fix;
the `git diff` for this change touches only the one `.spl` call site (plus
facet 1's already-landed Rust patch).

## Verification

`cargo build --release --bin simple` (incremental, from the fresh seed
already present in this worktree) after applying facet 1's patch + facet 2's
one-line `.spl` fix:

```
$ env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH \
    src/compiler_rust/target/release/simple native-build \
    --entry probe1.spl -o probe1_bin --backend cranelift --clean
...
[cranelift-direct] start
[cranelift-direct] target
[cranelift-direct] module
[cranelift-direct] declare __simple_main
[cranelift-direct] compile main
[cranelift-direct] emit /tmp/simple_cranelift_....o
$ echo $?
0
$ ./probe1_bin
42
$ echo $?
0
```

Before either fix, this identical invocation died at the first `error:` line
shown in the Repro section above. Confirmed the wall is closed **and** the
compiled binary runs and produces the correct output — a full round trip, not
just "no error."

`cargo test --release -p simple-compiler --lib rt_string_data` (facet 1's
tests, carried over from S81's patch):

```
test interpreter::interpreter_extern::tests::rt_string_data_dispatches_through_native_handler_rt_string_data_extern_dispatch_gap_2026_07_18 ... ok
test interpreter::interpreter_extern::tests::rt_string_data_rejects_missing_argument ... ok
```

A second function (`fn helper() -> i64: return 1`) added alongside `main` in
the entry file still builds and runs clean under cranelift-direct — the fix
is not scoped to single-function files.

## Third bug found (separate, NOT fixed here — out of scope)

Any entry file whose functions have **parameters** (e.g. `fn add(a: i64, b:
i64) -> i64: return a + b`, or the Dict-returning
`dict_fn_return`-equivalent used to try to reproduce case 21 exactly) fails
**when driven via a freshly `cargo build`'d Rust seed's own `native-build`
subcommand** — under **both** `--backend=cranelift` and the default llvm
backend equally — with:

```
error: semantic: type mismatch: cannot convert object to int
```

This is unrelated to facets 1/2 above:

- It is backend-independent (llvm fails identically), whereas facets 1/2 are
  cranelift-only.
- It reproduces at the exact same ~160K-line log offset regardless of the
  entry file's content, strongly suggesting it fires during the fresh seed's
  own (slow, still-maturing) tree-walking interpretation of the self-hosted
  CLI/compiler module graph that `native-build` requires (the fresh Rust seed
  has no native Rust implementation of `native-build`, only of `compile`), not
  in cranelift/MIR-to-native codegen itself.
- Control experiment: the same parameterized-function file
  (`fn add(a: i64, b: i64) -> i64: ...`) compiled and ran correctly (rc=7)
  via `bin/simple native-build --entry ... ` (llvm backend) — a natively
  compiled binary that does NOT need to interpret the self-hosted CLI from
  source. Only the **fresh seed's own interpretation of `native-build`**
  triggers this; it is not a defect in the compiler's actual native codegen.
  `bin/simple --backend=cranelift` on the same file hits facet 1 (unfixed
  there, since `bin/simple` predates this fix and lives outside this
  worktree — never rebuilt here per the no-`bin/release`-writes constraint).

This blocked reconstructing an exact, fully-verified `dict_fn_return`
end-to-end repro in this worktree (Dict-returning functions inherently take
at least one parameter or are otherwise non-trivial), but does not weaken the
facet 1/2 fixes above, both of which are proven on their own minimal,
targeted repros. Left as a follow-up for a lane investigating fresh-Rust-seed
interpreter robustness on large self-hosted-source module graphs; not
chased further here (out of scope for the assigned cranelift-direct wall).

## Files changed

- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — facet 1,
  applied from lane S81's commit `c8f1bb85e8851b0419129cedfcc66ec17f256894`.
- `src/compiler_rust/compiler/src/interpreter_extern/sffi_string.rs` — facet
  1, same origin.
- `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` — facet 2,
  this lane (S91): dropped the stale `emit_name` argument at the sole
  `cranelift_aot_define_function` call site.
