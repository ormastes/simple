---
id: cranelift_direct_string_constant_null_pointer_2026-07-12
status: OPEN
severity: blocking
discovered: 2026-07-12
discovered_by: native-build --entry-closure self-host closure build (agent session)
related: src/compiler/70.backend/backend/cranelift_codegen_adapter.spl
related: src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs
related: src/lib/nogc_sync_mut/ffi/codegen.spl
---

# `native-build --backend cranelift`: string constants always compile to a null pointer (SIGSEGV / silent no-op)

**Status:** OPEN — architectural gap, not a quick fix.
**Severity:** Blocking for `native-build --entry-closure` on **any** program
that uses a string literal — i.e. essentially all real Simple programs,
including `src/app/cli/main.spl`. Confirmed blocking for the standard
3-stage bootstrap too: `scripts/bootstrap/bootstrap-from-scratch.sh:538-541`
(Stage 2) invokes the exact same `--backend cranelift --entry-closure`
combination against `--entry src/app/cli/bootstrap_main.spl`, and the
script's own comment explains cranelift is used deliberately ("the seed
interpreter intercepts `--backend llvm-lib` and dispatches to
`bootstrap_main.spl` via the interpreter, where `rt_native_build` is a stub
that fails. With cranelift the seed uses its Rust `handle_native_build`
directly") — so there is no LLVM fallback to route around this bug; Stage 2
is cranelift-or-nothing today.
**Path:** `bug` track.

## Symptom

Minimal repro (outside the repo, entry file passed via `--entry`):

```simple
fn main():
    print("hello")
```

Build:

```bash
<seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 4 --cache-dir <cache> --mode dynload \
  --entry <probe>.spl --runtime-path <repo>/src/compiler_rust/target/bootstrap \
  -o <out>
```

Build succeeds (exit 0, produces a linked ELF binary). Running the binary
exits 0 but **prints nothing at all** — `rt_print` receives a `NULL` pointer
(the constant `0` emitted below) instead of a pointer to `"hello"`.

**Note on a related but distinct symptom seen in the same session:** a
separate probe, `fn add(a: i64, b: i64) -> i64: return a + b` then
`print(add(2, 3))`, SIGSEGVs inside `fputs` at address `0x5` (literally the
int value `5`). That is **not** this bug — `5` is an `i64`, never routed
through `cl_translate_const_value`'s `Str` arm at all. It is a separate bug
one level up, in MIR lowering: `lower_bootstrap_print_call`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:526-543`)
declares the `rt_print` call signature as taking a single `text` param but
passes `self.lower_expr(args[0].value)` straight through with **no
int→text conversion inserted**, whatever the argument's real type is. The
interpreter's `print` intrinsic (`src/compiler/95.interp/mir_interp_intrinsics.spl:16-26`)
is forgiving here — it checks `self._get_string(v)` and falls back to
`print "{v}"` formatting when the value isn't already text — but
`lower_bootstrap_print_call` has no equivalent coercion, so any native
backend (this affects cranelift AND, per the shared MIR lowering, likely
LLVM too — not verified here) that reaches this call with a non-text
argument passes garbage. Filed as a **separate** bug; not fixed here. Do not
conflate the two: fixing string-constant emission alone will not fix
`print(<int>)`, and fixing the print-argument coercion alone will not fix
`print("literal")`.

## Root Cause

`cl_translate_const_value` in
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` (around line
669-683):

```simple
fn cl_translate_const_value(ctx: i64, value: MirConstValue, type_: MirType) -> i64:
    match value:
        case Int(v):
            cranelift_iconst(ctx, mir_type_to_cl(type_), v)
        case Float(v):
            cranelift_fconst(ctx, mir_type_to_cl(type_), v)
        case Bool(v):
            cranelift_iconst(ctx, CL_TYPE_I8, if v: 1 else: 0)
        case Str(v):
            # String constants: emit pointer (handled by runtime)
            cranelift_iconst(ctx, CL_TYPE_I64, 0)
        case Zero:
            cranelift_iconst(ctx, mir_type_to_cl(type_), 0)
        case _:
            cranelift_iconst(ctx, CL_TYPE_I64, 0)
```

The `Str(v)` arm discards the actual string content `v` and always emits the
constant `0` (a null pointer) — regardless of what the string literal was.
The comment ("handled by runtime") does not match the code: there is no
runtime call, no string-pool index, no data-section reference — `v` is
simply dropped.

Grepping the Cranelift SFFI surface confirms there is **no** existing support
for emitting string/data constants in the direct-AOT path at all:

```
grep -n "data_object|DataDescription|declare_data|cranelift_string|cranelift_data|global_value|GlobalValue" \
  src/lib/nogc_sync_mut/ffi/codegen.spl src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs
# (no matches)
```

`cranelift_sffi.rs` has SFFI for signatures, functions, blocks, stack slots,
arithmetic/control-flow instructions, and runtime-import calls — but nothing
for `Module::declare_data` / `DataDescription` (the Cranelift API for
placing a byte blob in `.rodata`/`.data` and taking its address), which is
what a real fix needs.

Every call downstream that consumes a `text` value compiled through this
path (any `print(...)`, any string argument to a runtime import, any string
comparison) receives `0` (or, for a non-constant `text` computed from other
data, whatever garbage happens to be at that stack slot) instead of a valid
pointer — this is a **general-purpose blocker**, not specific to `print`.

## Why this matters for the entry-closure build

`native-build --entry-closure`'s own closure BFS + parse phase (fixed
2026-07-12, see
`doc/08_tracking/bug/native_build_entry_closure_quadratic_hang_2026-07-12.md`)
now reaches parse/HIR/MIR/codegen for real source files. The originally
documented next wall in that doc ("cannot convert array to int" on
`src/app/cli/main.spl`) did **not** reproduce in two independent full-closure
runs during this session (`--source src/compiler --source src/app --source
src/lib --entry src/app/cli/main.spl`, `--threads 4`) — both progressed
cleanly through `main.spl`'s parse with no error. That wall may have been
fixed incidentally by an unrelated parallel-session change, or may be
order/state-dependent; it was not seen again and is not re-investigated
here.

The actual, currently-reproducing next wall is this one. This session's full
closure runs used `--entry src/app/cli/main.spl` (per the task's repro
command); the real bootstrap Stage 2 uses `--entry
src/app/cli/bootstrap_main.spl` instead — either way, both are real CLI code
that use string literals pervasively (`print`, error messages, path
construction, etc). Once the (very slow — see Performance note below) full
closure build reaches Cranelift codegen, it will hit this exact bug on the
first string constant it compiles, either as a build-time crash/miscompile
or (more likely, given the minimal repro) a *silently* corrupt binary that
segfaults or hangs at runtime rather than failing the build outright. The
full closure builds run this session did not individually reach codegen
before being stopped (parse phase alone runs many minutes to an hour+, see
Performance note) — this bug's blocking status is established via the
isolated minimal-entry probe, not by observing the full closure fail at this
exact point.

## Fix (not attempted — scope estimate)

Requires new Rust SFFI in `cranelift_sffi.rs`:
1. A registry (parallel to `SIGNATURES`/`DECLARED_FUNCS`) for interned
   string-constant data objects, keyed by content (or by MIR constant id) to
   dedupe.
2. `rt_cranelift_declare_string_data(module, ptr, len) -> i64` (or similar):
   `Module::declare_data(name, Linkage::Local, writable=false, tls=false)`,
   build a `DataDescription` with the byte content (`+ NUL` if the runtime
   ABI expects C-strings, or emit `(ptr, len)` pairs if it expects Simple's
   fat `text` representation — needs to match whatever
   `src/runtime`'s string ABI already uses for JIT/interpreted `text`
   values, to avoid a second parallel string representation), then
   `module.define_data(...)`.
3. `rt_cranelift_data_addr(ctx, data_id) -> i64` inside a function body:
   `module.declare_data_in_func(data_id, builder.func)` +
   `builder.ins().global_value(...)` to materialize the address as an SSA
   value.
4. New extern bindings in `src/lib/nogc_sync_mut/ffi/codegen.spl` mirroring
   the existing `cranelift_*` wrapper pattern.
5. `cl_translate_const_value`'s `Str(v)` arm updated to call the new data-object
   path instead of `cranelift_iconst(ctx, CL_TYPE_I64, 0)`.
6. Needs a check of whether `text` in this runtime is a bare `char*` or a
   `(ptr, len)`/boxed struct — if boxed, the constant also needs to allocate
   (or statically lay out) the box, not just the raw bytes, to match what
   `print`/other runtime imports expect on the receiving end.

This is a genuine cross-language (Rust + Simple), multi-file feature
addition to the Cranelift backend, not a targeted bug fix — treated as a
hard wall per session scope and reported rather than attempted.

**Reference for a future fixer:** strings clearly work correctly through at
least two other paths already in this codebase, which are the right places
to copy the wire format/ABI from rather than inventing a third:
- The tree-walking interpreter (`src/compiler/95.interp/`) obviously handles
  `text` values correctly — it's how every `test/` spec with a string
  literal passes today.
- `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` routes
  `print` to `rt_println` by name; if the LLVM AOT backend already emits
  real string constants (worth checking before assuming it also needs this
  fix), its data-emission path is the direct Cranelift analogue of what
  `rt_cranelift_declare_string_data` needs to do.

## Related minor robustness bug (same investigation, not the primary blocker)

While tracing this, an unrelated parser robustness gap surfaced: an
unrecognized type name (e.g. writing `int` instead of the canonical `i64` —
see `doc/07_guide/quick_reference/syntax_quick_reference.md`) in a function
signature is **silently accepted** by `parser_parse_type()`
(`src/compiler/10.frontend/core/parser.spl`) and resolves to `TYPE_VOID`
(`0`) with no diagnostic, rather than a parse error. This turned an initial
probe using `int` instead of `i64` into a confusing silent miscompile
(function `-> int` treated as `-> Unit`, tripping a Cranelift signature/return
verifier error) instead of a clear "unknown type `int`" error at parse time.
Worth a follow-up (`named_type_find` returning `-1` for a bare, non-generic
identifier that isn't a recognized builtin should be a parse error, not a
silent `TYPE_VOID` fallback) but out of scope here.

## Performance note (separate, not blocking, recorded for visibility)

Independently of this bug: `phase2:parse` on the real 3-`--source`-root,
`main.spl`-rooted entry closure is measured at a flat **~3.3-4.5ms per
source character**, with no correlation to cumulative bytes parsed (i.e. not
the O(n²) class fixed earlier — per-file cost tracks that file's own size
linearly). At that rate the full closure's parse phase alone takes on the
order of many minutes to an hour+ before even reaching codegen (a
`--threads 4`, `SIMPLE_COMPILER_PHASE_PROFILE=1` run was still in
`phase2:parse` after 13+ minutes, having completed roughly two dozen of
~493 loaded source files). This is inherent interpreted-seed overhead
(the seed tree-walks the pure-Simple parser/compiler pipeline to compile
target sources) rather than a specific algorithmic bug, and was not chased
further — noted here so a future session doesn't have to re-discover that a
short repro timeout will look like a "hang" when it is actually just slow.
