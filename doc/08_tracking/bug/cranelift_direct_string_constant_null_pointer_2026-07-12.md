---
id: cranelift_direct_string_constant_null_pointer_2026-07-12
status: FIX-IMPLEMENTED-UNVERIFIED-E2E
severity: blocking
discovered: 2026-07-12
discovered_by: native-build --entry-closure self-host closure build (agent session)
related: src/compiler/70.backend/backend/cranelift_codegen_adapter.spl
related: src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs
related: src/lib/nogc_sync_mut/ffi/codegen.spl
---

# `native-build --backend cranelift`: string constants always compile to a null pointer (SIGSEGV / silent no-op)

## 2026-07-12 update: fix implemented, mechanism verified by Rust unit test, e2e blocked by an unrelated pre-existing wall

**What was implemented** (see commits `8803ee074b9`, `1958c98ba21` in this
worktree):

1. **New Cranelift data-object SFFI** in
   `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs`:
   - `rt_cranelift_declare_string_data(module, bytes_ptr, bytes_len) -> i64`:
     declares + defines a read-only rodata `data` object holding the raw
     bytes (`Module::declare_data` + `DataDescription::define` +
     `Module::define_data`), content-addressed per module (identical bytes
     reuse the same data object, verified by a dedup test) via a new
     `STRING_DATA_CACHE`/`DECLARED_DATA` registry pair mirroring the
     existing `DECLARED_FUNCS` pattern.
   - `rt_cranelift_data_addr_in_func(ctx, data_handle) -> i64`:
     `Module::declare_data_in_func` + `builder.ins().global_value(I64, gv)`
     to materialize the address as an SSA value in the function currently
     being built, mirroring `rt_cranelift_iconst`'s handle-return
     convention.
   - Both registered in `register_cranelift_sffi_functions` (JITBuilder
     symbol table, for the self-hosted-recursive-JIT path) and wired through
     `interpreter_extern/cranelift.rs` + `interpreter_extern/mod.rs` (the
     seed's own tree-walking-interpreter dispatch table, which is what
     `native-build` actually runs through).
2. **Simple-side wrappers** in `src/lib/nogc_sync_mut/ffi/codegen.spl`:
   `cranelift_declare_string_data(module, s: text) -> i64` /
   `cranelift_data_addr_in_func(ctx, data_id) -> i64`.
3. **Adapter wiring** in `cranelift_codegen_adapter.spl`:
   `cl_translate_const_value`'s `Str(v)` arm now declares `v`'s bytes as
   rodata, materializes the address, and calls the runtime's own
   `rt_string_new(ptr, len)` (via the existing `translate_runtime_import_call_i64`
   helper) instead of emitting a null constant. This deliberately reuses the
   runtime's real allocation/heap-registration/hash path (`rt_string_new` ->
   `RuntimeValue::from_heap_ptr` -> `register_heap_ptr`) rather than
   hand-rolling a second one: this runtime's `text` is a **tagged, heap-registered
   RuntimeValue** (`src/compiler_rust/runtime/src/value/heap.rs`:
   `validate_heap_obj` rejects any heap pointer not in
   `HEAP_ALLOCATION_REGISTRY`), so a static data pointer alone is not a valid
   `text` value without going through the registration a real allocation
   gets. `cl_module` had to be threaded through `cl_translate_operand`,
   `cl_translate_terminator`, and `store_phi_incomings_for_edge` (not just
   `cl_translate_instruction`) since string constants can appear at any
   operand site, not only inside a `Const` instruction.
4. **Unrelated fix required to get any native-build running at all**:
   `rt_array_len_safe` existed in the runtime crate but had no
   `interpreter_extern` dispatch entry, so the seed failed on **any**
   native-build (string or not) with `unknown extern function:
   rt_array_len_safe` before reaching codegen. Added the missing wrapper +
   registration (mirrors the existing `rt_array_len` entry).

**Verification performed:**
- `cargo check`/`cargo build --release --bin simple` for the whole
  `compiler_rust` workspace: clean.
- New Rust unit test `test_string_data_constant_roundtrip` in
  `cranelift_sffi.rs`: JIT-compiles a `() -> i64` function that returns the
  address of a declared `"hello"` data object, calls it, and **dereferences
  the actual returned pointer** to compare the 5 bytes against `b"hello"`
  (not just a nonzero-handle check, which would miss a wrong/garbage
  data-reloc — the documented failure mode). Also verifies content-addressed
  dedup (declaring identical bytes twice returns the same handle). **Passes.**
  This validates the Cranelift data-object mechanism (declare_data +
  define_data + declare_data_in_func + global_value) in isolation, via the
  JIT path.

**What was NOT verified — e2e blocked by an unrelated pre-existing wall:**
Running `native-build --backend cranelift --entry <probe>.spl` (with or
without `--source src/compiler --source src/app --source src/lib`, and even
for a **zero-string-literal** probe `fn main() -> i64: return 0`) fails
**before ever reaching `[cranelift-direct]`** (the adapter's own progress
prints) with:
```
error: semantic: type mismatch: cannot convert array to int
```
This reproduces deterministically regardless of `--source` flags or whether
the entry program contains any string literal at all — i.e. it is **not**
caused by this session's changes; it is upstream of Cranelift codegen
entirely, in the seed's own interpreted execution of its (unrelated) source
files. It matches the "originally documented next wall" this bug doc's first
version noted as order/state-dependent and not reliably reproducing. The
message originates from `Value::as_int()` in
`src/compiler_rust/compiler/src/value_impl.rs:45` (`format!("type mismatch:
cannot convert {} to int", actual_type)`), i.e. some extern-call site is
passing an array `Value` through `.as_int()`; the exact call site was not
tracked down (would need seed-internal instrumentation, out of scope for
this session per "assess tractable-vs-hard, fix tractable ones, STOP+document
hard ones").

**Consequently NOT exercised by this session**, and worth flagging
explicitly for the next fixer: whether a string constant surviving storage
into a `text` local and reuse (`val s = "hello"; print(s)`), concatenation,
`==`, or `.len()` is representation-consistent with `cl_translate_cast`'s
existing fat-pointer `{ptr, len}` handling of `text` **operands** (as opposed
to the `Const` instruction path this fix touches, whose `type_` is
`Opaque("str")`, a single-word type — confirmed by tracing
`StringLit` lowering in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:519`). The `Str`
constant now yields a boxed `RuntimeValue` scalar, matching `Opaque("str")`'s
single-word shape and the boundary code in `cl_translate_cast` that already
boxes a fat pointer into the same representation via `rt_string_new` before
calling `rt_string_to_int_lenient`. This is believed consistent but was not
proven by an actual native-run due to the wall above.

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
