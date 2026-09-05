---
id: seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12
status: FIXED
severity: blocking
discovered: 2026-07-12
fixed: 2026-07-12
discovered_by: cranelift AOT string-constant fix verification (agent session)
related: src/compiler/10.frontend/core/lexer.spl
related: src/compiler_rust/compiler/src/interpreter_call/mod.rs
related: src/compiler_rust/common/src/runtime_symbols.rs
related: doc/08_tracking/bug/cranelift_direct_string_constant_null_pointer_2026-07-12.md
---

# `native-build` fails on ANY program with "unknown extern function: rt_array_len_safe" before reaching codegen

**Status:** FIXED. Root cause: `EXTERN_FUNCTIONS` (checked by the tree-walk
interpreter's `evaluate_call`, priority 1, *before* local-function lookup) is
seeded in bulk from `RUNTIME_SYMBOL_NAMES`
(`src/compiler_rust/common/src/runtime_symbols.rs:139-140,386-387`) — the
runtime's full linker symbol manifest — not just from `extern fn`
declarations actually parsed out of the running program. `rt_array_len_safe`
is a real Rust-runtime export (`runtime/src/value/collections.rs:432`) with a
coincidentally identical name to the unrelated local pure-Simple generic
helper `fn rt_array_len_safe<T>(array: [T]) -> i64` in lexer.spl/parser.spl/
decl_nodes.spl/lexer_struct.spl. Because the extern-membership check never
consulted local scope, the coincidental manifest entry always won, even
though a local definition existed.

Confirmed empirically by instrumenting `evaluate_call`'s priority-1 branch
with a debug print gated on `SIMPLE_DEBUG_CALL_RESOLVE=1`:
```
[call-resolve] name=rt_array_len_safe is_extern=true has_local_fn=true
```
`is_extern=true` and `has_local_fn=true` simultaneously — proof this was an
order/priority bug (cause **(a)** in the investigation, not a generic-dispatch
gap).

**Fix** (`src/compiler_rust/compiler/src/interpreter_call/mod.rs`,
`evaluate_call`): before honoring the `EXTERN_FUNCTIONS` membership check,
also check whether a local function definition (including overloaded/generic
ones, via `functions` and `FUNCTION_OVERLOADS`) exists for the same name.
Route to extern dispatch only when `is_extern && !has_local_def`. This
leaves real externs (no local def) completely unaffected — the fix only
changes behavior for the rare case where a bulk-registered runtime symbol
name coincidentally collides with a local/generic `.spl` function name.

**Verification:**
- Trivial probe (`fn main() -> i64: return 0`) via
  `SIMPLE_BOOTSTRAP=1 <fixed seed> run src/app/cli/native_build_main.spl --
  --backend cranelift --entry probe.spl -o out`: no longer errors on
  `rt_array_len_safe`; produces a runnable ELF binary, `rc=0`.
- String probe (`fn main(): print("hello")`) through the same
  `SIMPLE_BOOTSTRAP=1`-forced-llc pipeline (this is the path
  `.claude/rules/bootstrap.md`'s own "internal stage replay" example and this
  session's actual redeploy invocation use — `SIMPLE_BOOTSTRAP=1` overrides
  `--backend cranelift` to the LLVM/`llc` backend, confirmed empirically by
  `[bootstrap-real-llvm]`/`[llvm-tools] llc-object` log lines): produces a
  binary that prints `hello`, `rc=0` — end-to-end verification of the
  string-constant SFFI fix landed in 874914d1fa7 **on the LLC backend**, now
  that native-build can reach codegen at all.
  **Caveat, precisely stated:** this does *not* verify the Cranelift-direct
  backend's own string-constant path. Running the identical string probe
  *without* `SIMPLE_BOOTSTRAP=1` (`--seed-ok`, so `--backend cranelift`
  actually engages real Cranelift-direct — confirmed by `[cranelift-direct]
  start` / `compile main` log lines) fails with `error[E1002]: function
  'cranelift_declare_string_data' not found`, even though that wrapper is
  defined at `src/lib/nogc_sync_mut/ffi/codegen.spl:320` and imported via
  `use std.sffi.codegen.*` in `cranelift_codegen_adapter.spl` — sibling
  bare-`fn`s in the same file (e.g. `cranelift_iconst`) resolve fine via the
  same import, so this isn't a visibility issue; root cause not
  investigated further (out of this bug's scope). This is exactly the
  "NOT verified e2e" caveat already called out in
  `cranelift_direct_string_constant_null_pointer_2026-07-12.md` — not a
  regression introduced by this fix, and not fixed here.
- Sanity: a plain interpreted `run` of a script using a real array (`a.len()`
  builtin) still works, confirming the local-def check didn't regress
  genuine extern dispatch for names without a local definition.

**Separate, newly-discovered follow-on bug:** the same "runtime-symbol-name
membership checked before local-definition presence" pattern also exists in
the **codegen backend** (`compile_call` in
`codegen/instr/calls.rs:2994-3088`), not just the interpreter fixed here — a
locally-defined function whose bare name coincidentally matches a real
runtime export (exactly `rt_array_len_safe`'s situation, generic form
included) compiles without error but **SIGSEGVs at runtime**. This is
directly relevant to the redeploy target once native-build's entry-closure
reaches compiling `lexer.spl` to native code. See
`doc/08_tracking/bug/codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12.md`
for the full writeup; not fixed in this session (deep, higher-risk change to
a 2700+ line dispatch function).

## Original symptom (for history)

**Status (as originally filed):** OPEN — root cause located, fix not attempted (separate scope).
**Severity:** Blocking. Currently prevents `native-build` (any backend, any
entry program) from running through the Rust seed at all.

## Symptom

```bash
SIMPLE_BOOTSTRAP=1 <seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --entry probe.spl -o out
```
fails, before any `[cranelift-direct]`/codegen progress output, with:
```
error: semantic: unknown extern function: rt_array_len_safe
error: native-build worker exited with code 1.
```
Reproduces deterministically for **any** entry program, including a
zero-dependency trivial one (`fn main() -> i64: return 0`), with or without
`--source` flags. Not specific to Cranelift, string constants, or any
particular entry file — the error occurs while the seed is interpreting its
own compiler source files during the closure/parse phase, before the
requested backend or entry program is ever reached.

## Root cause

`src/compiler/10.frontend/core/lexer.spl:34` defines:
```simple
fn rt_array_len_safe<T>(array: [T]) -> i64:
    return array.len()
```
a **local, pure-Simple generic function**, used throughout `lexer.spl` (e.g.
lines 93, 95, 97, 99, ... 713) with real array arguments. This is unrelated
to the `simple_runtime` crate's same-named extern,
`rt_array_len_safe(array: RuntimeValue) -> i64`
(`src/compiler_rust/runtime/src/value/collections.rs:432`) — a coincidental
name collision (or an intentional mirror for a different call site;
not established).

Somewhere in the seed's `native-build` execution path, a call to bare-name
`rt_array_len_safe` is resolved via **extern dispatch** instead of the local
generic function definition in the same file/scope. Since no
`interpreter_extern` entry named `rt_array_len_safe` existed (correctly —
that name was never meant to be an extern from `native-build`'s perspective),
this produced the "unknown extern function" error.

**Confirmed empirically, not just by inspection:** this session briefly (and
mistakenly) added an `interpreter_extern` stub for `rt_array_len_safe`
(int-handle signature, mirroring `rt_array_len`'s). That masked the "unknown
extern" error but caused a *different* failure, `type mismatch: cannot
convert array to int`, because the misrouted calls (meant for lexer.spl's
local `[T]`-array function) landed in the int-handle-only stub instead.
Reverting the stub restored the original "unknown extern function:
rt_array_len_safe" error exactly (A/B verified by rebuild + rerun). This
confirms: (a) the misrouting to extern dispatch is real and happens
regardless of whether a matching `interpreter_extern` entry exists, and
(b) simply adding a matching-name extern entry is NOT the right fix — it
would need to somehow yield the array's `.len()` directly, not attempt
`RuntimeValue`-handle decoding, or (more likely correct) the resolution
order itself needs fixing so a local generic function definition in scope is
tried before falling back to extern dispatch.

## Why this wasn't fixed here

Locating the exact call site that decides "try extern dispatch" for this
name (rather than resolving the local generic `fn rt_array_len_safe<T>`)
requires instrumenting the seed's own name-resolution/call-lowering code
(local-function lookup vs. extern-function lookup ordering, and/or generic
function dispatch support in whatever specific `native-build` execution mode
is engaged — interpreted tree-walk of the seed's own `.spl` source is
different from the seed's normal `run` of arbitrary Simple programs, and this
gap may be specific to that internal path). This is out of scope for the
Cranelift string-constant task that surfaced it; flagged here as its own
blocking bug per the "assess tractable vs. hard, fix tractable, document
hard" policy.

## Impact

Blocks end-to-end verification of `native-build` entirely — including but
not limited to the Cranelift AOT string-constant fix landed alongside this
doc (see `cranelift_direct_string_constant_null_pointer_2026-07-12.md`),
which is mechanism-verified via a Rust-only JIT unit test but has never been
run through the actual `native-build` pipeline because it cannot get past
this wall to reach any backend's codegen.

## Suggested next steps (not attempted here)

1. Trace how `native-build`'s specific compiler invocation resolves a bare
   call name to a callee (local scope lookup, then module lookup, then
   extern table) and find where/why a local generic function in the same
   file is skipped in favor of extern-table lookup.
2. Once located: either fix the resolution order (prefer local/generic
   definitions when one exists in scope), or determine whether generic
   function calls specifically fail to resolve in this execution path
   (falling through to extern dispatch as an incorrect fallback) and fix
   generic-call support there instead.
3. Re-run the Cranelift string-constant probe
   (`fn main(): print("hello")`) once this clears, per
   `cranelift_direct_string_constant_null_pointer_2026-07-12.md`'s
   "What was NOT verified" section.
