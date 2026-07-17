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

## 2026-07-17 blocker update

The later `rt_array_len_safe` interpreter-resolution fix was already landed,
and the separate native codegen local/runtime-name collision is now source
fixed with unit and Cranelift AOT regression coverage. Those historical walls
no longer call for another interpreter extern shim or a lexer rename.
End-to-end proof of this string-data fix still depends on the rebuilt staged
seed running the existing Cranelift executable gates.

## 2026-07-12 update: fix implemented, mechanism verified by Rust unit test, e2e blocked by an unrelated pre-existing wall

**BOTTOM LINE — read before assuming this unblocks redeploy:** the
Cranelift string-constant fix below is implemented, compiles cleanly, and is
verified correct **in isolation** by a Rust unit test that JIT-compiles and
executes the new data-object mechanism and dereferences the real returned
pointer. It has **NOT** been run end-to-end through `native-build`: no
binary was produced, `print("hello")` was never actually executed, and the
AOT `ObjectModule` emit/relocation path (the bug's actual originally-reported
failure mode — object-file emission, not JIT) was never exercised at all
this session. `native-build` currently fails before reaching Cranelift
codegen for *any* program, string or not, on a wall unrelated to this fix
(see below). **Redeploy is not cleared by this change alone.**

**What was implemented** (landed on origin/main as commits `28d9e6936c5`
(the fix), `19e0dc12a8c` (the JIT test), `e4680b6e42a` (first doc update),
`b066df7c669` (revert of the mistaken `rt_array_len_safe` stub, see below),
`692adaa34c7` (this correction)):

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
4. **Attempted (and reverted) fix for an unrelated blocker** — see
   "e2e blocked" section below for the corrected account. A same-named
   `rt_array_len_safe` interpreter_extern stub was added, then found to be
   *wrong* (it globally shadowed a local Simple function of the same name)
   and reverted in a follow-up commit. Net effect on this repo: none — the
   pre-existing wall it was meant to work around is still present and
   undocumented-fixed.

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

**What was NOT verified — e2e blocked by an unrelated pre-existing wall
(IMPORTANT — corrected below, read this version, not any earlier draft):**

Running `native-build --backend cranelift --entry <probe>.spl` — with or
without `--source src/compiler --source src/app --source src/lib`, and even
for a **zero-string-literal** probe `fn main() -> i64: return 0` — fails
**before ever reaching `[cranelift-direct]`** (the adapter's own progress
prints), i.e. before Cranelift codegen runs at all, with:
```
error: semantic: unknown extern function: rt_array_len_safe
```
**Root cause, confirmed by reading source, not guessed:**
`src/compiler/10.frontend/core/lexer.spl:34` defines
```
fn rt_array_len_safe<T>(array: [T]) -> i64:
    return array.len()
```
as a **local, pure-Simple generic function** — unrelated to the
`simple_runtime` crate's same-named `rt_array_len_safe(array: RuntimeValue)
-> i64` extern (a coincidental name collision, or a deliberate mirror for a
different call site — not established). The seed's `native-build` execution
path attempts **extern dispatch** for `rt_array_len_safe` instead of
resolving to lexer.spl's own local definition, and — correctly, given that
call site never registered an interpreter_extern handler by that bare name
— fails with "unknown extern function". This is a **local-generic-function
vs. extern-name resolution gap** in the seed's interpreted execution of
`native-build`, reproduces deterministically for *any* entry program
(string literals irrelevant), and is **not caused by this session's string-
constant changes** — confirmed by A/B testing (see below).

**A mid-session mistake, made and then corrected:** this session initially
mistook the above for "`rt_array_len_safe` is simply missing from
`interpreter_extern`" and added a stub wrapper + registration mirroring
`rt_array_len`'s (commit `28d9e6936c5`). That masked the "unknown extern"
error but **shadowed lexer.spl's local generic function globally** — any
call to bare-name `rt_array_len_safe` anywhere now routed through the new
int-handle-only stub instead of the local `[T]`-array function, so the
stub's `.as_int()?` on a genuine array argument threw `type mismatch: cannot
convert array to int`. This was reverted (commit `b066df7c669`); an A/B
rebuild+run confirmed the revert restores the original "unknown extern
function: rt_array_len_safe" error exactly, both confirming this diagnosis
and confirming the revert introduces no new regression.

**Net state: native-build via this seed does not reach Cranelift codegen at
all right now**, for reasons entirely unrelated to string constants. Tracking
this local-generic-vs-extern resolution gap is out of scope for this session
(no location narrower than "the seed's native-build closure-loading path"
was established; would need seed-internal instrumentation to find the exact
call site attempting extern dispatch instead of local resolution). Treat it
as a **separate, still-open, hard-wall bug** blocking e2e verification of
*any* `native-build --backend cranelift` change, not specific to this fix.

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

## 2026-07-12 follow-up: concrete e2e symptom for the still-unverified Cranelift-direct path

After a separate, unrelated interpreter fix unblocked `native-build` from
failing before reaching codegen at all (see
`doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`),
the string probe here was finally runnable end-to-end. Result:

- Via `SIMPLE_BOOTSTRAP=1` (which overrides `--backend cranelift` to the
  LLVM/`llc` backend — confirmed by `[bootstrap-real-llvm]` log lines, and
  matches `.claude/rules/bootstrap.md`'s own documented "internal stage
  replay" invocation, i.e. the actual redeploy path used in practice):
  `fn main(): print("hello")` builds and runs correctly, printing `hello`.
  This validates the string-constant SFFI mechanism end-to-end **on the LLC
  backend** specifically.
- Via `--seed-ok` (no `SIMPLE_BOOTSTRAP=1`), `--backend cranelift` actually
  engages real Cranelift-direct (confirmed by `[cranelift-direct] start`
  / `compile main` log lines) — and the *same* string probe now fails with
  `error[E1002]: function 'cranelift_declare_string_data' not found`, even
  though that wrapper is defined (`src/lib/nogc_sync_mut/ffi/codegen.spl:320`)
  and imported (`use std.sffi.codegen.*` in `cranelift_codegen_adapter.spl`).
  Sibling bare-`fn`s in the same file (e.g. `cranelift_iconst`, used
  successfully just before this call in the same `cl_translate_const_value`
  function) resolve fine via the identical import, ruling out a simple
  visibility issue. Not investigated further this session (out of scope for
  the interpreter fix that unblocked reaching this point at all) — this is
  the concrete symptom of the "NOT verified e2e" status already called out
  above; still open.

## 2026-07-12 follow-up: the `print(<int>)` sibling bug (lines 198-217 above) is FIXED

The separate bug flagged above (`print(add(2, 3))` SIGSEGVs at address `0x5`
inside `fputs`, because `lower_bootstrap_print_call` passed a raw non-text
argument straight to `rt_print`/`rt_println`, both `const char*`-typed) is now
fixed. Root cause confirmed unchanged from the description above:
`lower_bootstrap_print_call`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:526`)
lowered `args[0].value` and passed it directly as the call operand with no
type coercion.

**Fix:** mirrors bug #136's string-interpolation fix
(`lower_string_interpolation` in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:151`). After lowering
the print argument, check its MIR type via `self.local_mir_type_of(arg_local)`:
if it's already `Opaque("str")`, pass through unchanged; otherwise render it
to a tagged heap string via `rt_raw_i64_to_string`, then unwrap that to a raw
`char*` via `rt_interp_cstr` (the same coercion pair #136 uses), and pass
*that* to `rt_print`/`rt_println` instead of the raw value.

**Scope:** covers i64 (the confirmed SIGSEGV) and, incidentally, bool (renders
as `"0"`/`"1"` via the same raw-int path rather than `"true"`/`"false"` — not
a crash, just not interpreter-matching text; a follow-up if the mismatch
matters). Float is **not** covered — no `rt_raw_f64_to_string` runtime
function exists yet, and adding one is a C-runtime change out of scope for
this pure-Simple lowering fix (`print(<float>)` still SIGSEGVs the same way
this bug did; tracked as a follow-up, not filed as a separate doc yet).

**Verified via minimal LLC-path repro** (`SIMPLE_BOOTSTRAP=1`, the documented
redeploy backend), pinned Rust seed running `native-build` over the fixed
worktree source (no seed rebuild needed — the fix is pure-Simple, interpreted
by the seed):
- BEFORE (unmodified source): `print(5); println(42); print(n); print(a+b)`
  → `SIGSEGV at address 0x5` (the literal `5`, confirming the exact
  mechanism described above), rc=139.
- AFTER (fixed source): same program → prints `542\n542` (i.e. `"5"` +
  `"42\n"` + `"5"` + `"42"`, exactly matching `print`'s no-trailing-newline /
  `println`'s trailing-newline semantics for values `5, 42, 5, 42`), rc=0, no
  crash.
- Regression check: `print("hello")` (literal) and `val s = "world";
  print(s)` (variable) both still print unchanged (`helloworld`, rc=0) —
  the `Opaque("str")` pass-through path (including the variable case, not
  just the literal) is intact.

Landed as a standalone fix to `switch_operators_calls.spl`; independent of
this doc's still-open Cranelift-direct string-constant gap above.

### 2026-07-12 correction: initial "coerce unless proven str" default silently regressed param-passed strings; inverted

The first landed version of this fix (commit `8b4f386a8a1`, rebased/pushed as
`b9ad74ed123`) defaulted to *coercing* any argument whose MIR local type did
not resolve to `Opaque("str")`. That default was backwards: text arriving via
a **function parameter** does not reliably get `Opaque("str")` threaded onto
its local (only literal / `val x = <literal>` bindings do, per #136's own
comment), so `local_mir_type_of` returned a non-str result for it too — and
the "coerce unless str" default routed it through `rt_raw_i64_to_string`,
printing the raw `char*` pointer as a decimal number instead of the string.
Caught before it went unnoticed by an explicit param-passing probe:

```simple
fn greet(s: text) -> i64:
    print(s)
    return 0
fn main() -> i64:
    return greet("hi")
```

Before this correction: printed `2099451` (a pointer value) instead of `hi`.
This would have silently broken the overwhelming majority of real prints
(error messages, paths, names — nearly all passed through a function
parameter, not a bare literal), while leaving the two originally-tested str
cases (literal, `val`-bound literal) looking fine.

**Fix:** inverted the default. `lower_bootstrap_print_call` now coerces
**only** when the local's MIR type explicitly matches a numeric/bool scalar
(`I8`/`I16`/`I32`/`I64`/`U8`/`U16`/`U32`/`U64`/`Bool`); every other case
(including `Opaque("str")`, and any local whose type isn't tracked at all)
passes through unchanged, matching the pre-fix behavior for text. Int
literals/variables/expressions reliably get an explicit `I64` local type from
`lower_expr`, so the original SIGSEGV fix is unaffected.

**Re-verified after the inversion**, same pinned-seed LLC-path harness:
- `print(5); println(42); print(n); print(a+b)` → `542\n542`, rc=0 (int fix
  still holds).
- `print("hello"); val s = "world"; print(s)` → `helloworld`, rc=0 (unchanged).
- `fn greet(s: text): print(s)` called as `greet("hi")` → `hi`, rc=0
  (regression fixed).
- `fn show(n: i64): print(n)` called as `show(42)`, plus
  `print(add(2, 3))` (the doc's own originally-cited `print(add(2,3))`
  SIGSEGV-at-`0x5` repro from the "Symptom" section above) → `425`, rc=0.
  This closes the remaining corner of the matrix (int arriving via a
  function parameter/return, not just an inline literal/local/expr): a
  scalar `i64` parameter's MIR local does reliably resolve to an explicit
  `I64` type (unlike a `text` parameter's `Opaque("str")`, which does not),
  so the numeric-only coercion default catches it correctly. int-inline,
  int-param/return, str-inline/local, and str-param are all now verified
  correct on the LLC bootstrap path.
