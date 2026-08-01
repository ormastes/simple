> **Current status — superseded 2026-07-26.** The historical claim that
> `rt_string_free` did not exist is no longer true: the runtime now exposes a
> registry-checked primitive which refuses shared or already-unregistered
> strings. Phase 2 now has a deliberately narrow owner boundary: after all
> frontend parsing, it clears lexer globals that retain the active source,
> invokes `rt_string_free` for every `SourceFile.content` handle, counts only
> successful unregister-and-free returns, and then replaces source metadata.
> This is not a general AST/HIR deep-free facility. `evict_ast()` and
> `evict_hir()` remain shallow metadata eviction because copied RuntimeValue
> aliases in those graphs are not ownership-safe.
>
> The native Stage4 execution/memory ceiling remains unproved here. The update
> has bounded unit evidence only; it deliberately does not claim a full Stage4
> run, cross-runtime parity, or a measured RSS reduction.

> **Historical orchestrator verification (2026-07-25).** The following was
> accurate before the runtime primitive landed, but its missing-primitive
> conclusion is superseded by the status above.
> independently:
> - `src/compiler_rust/runtime/src/value/core.rs`: `#[derive(Clone, Copy)]` on
>   `pub struct RuntimeValue(pub(crate) u64)` — every text/array/struct assignment
>   is a bitwise pointer copy, never a content clone. Aliasing is pervasive BY
>   CONSTRUCTION, not incidental.
> - `src/runtime/runtime_native.c`: `rt_string_free` occurrences = **0**. The
>   runtime bundle Stage4 actually links has NO way to free a string.
> - `rt_array_free` in that file contains no loop or recursion — shallow only.
>
> Conclusion: the deep-free fix is not "hard", it is **not currently expressible**.
> It requires new C and Rust free primitives that do not exist, plus an ownership
> discriminator to make freeing safe under Copy-semantics aliasing.
>
> No patch was attempted, correctly. On a no-GC runtime an unproven free is memory
> corruption — strictly worse than the leak.

# Deep-free primitive for `evict_sources()`/`evict_ast()`/`evict_hir()` — BLOCKED

Worktree HEAD: `191c530fc1f` (fetched + hard-reset from `origin/main` at session
start; `driver_types.spl` unchanged from the `1ddf2a2b87f` HEAD the prior
"never frees" report used).

## Verdict: BLOCKED — not a granularity/aliasing-uncertainty gap anymore, a
## missing-primitive + unsound-general-case gap, now decisively evidenced

Three prior sessions declined this citing "leans ALIASED, not conclusively
resolved." This session resolves that open question **conclusively** (proof
below) and finds two further, more fundamental blockers underneath it that
make a *general* value-level deep-free primitive unsafe to build in one
session, regardless of the aliasing answer.

## 1. Aliasing verdict: CONFIRMED ALIASED (not "leans") — proven at the type level

`RuntimeValue` (`src/compiler_rust/runtime/src/value/core.rs:43-44`):
```rust
#[derive(Clone, Copy)]
pub struct RuntimeValue(pub(crate) u64);
```
Every heap-backed value (`text`, `[T]`, `Dict`, structs, enums) is represented
as one tagged `u64` (a pointer for heap kinds). Because the type derives
`Copy`, **the Rust type system itself guarantees `let x = y` is a bitwise
8-byte copy — no custom clone logic can ever run on assignment.** This holds
at every boundary: local-to-local, struct-field read (`decl_get_name(idx)` →
`return decl_name[idx]`), array-element read, function return, everywhere.
Corroborating: `rt_string_new_uncached`
(`src/runtime/runtime_native.c:1489-1503`) is the only string constructor and
it **always `memcpy`s a fresh buffer** — the runtime never hands back a view
into someone else's storage — so the "does slicing alias the arena's buffer"
question from 2026-07-24 is moot: slicing produces a genuinely new object,
but a bare *read-and-store* of an existing `text`/array RuntimeValue (e.g.
`val name = decl_get_name(idx)`, then `Function(name: name, ...)`) is a
pointer alias, full stop. This is decisive, not inferred from absent-clone
code reading (the 07-24 update's method) — it's a property the Rust compiler
enforces on `RuntimeValue`'s definition.

Consequence: **the same heap string/array pointer can be reachable from
arbitrarily many live structures with zero bookkeeping of how many.**
`evict_ast()`'s `self.modules = {}` drops the driver's own references, but
any `Function`/`Struct`/`HirModule` field that copied a pointer out of one of
those AST nodes (which, per above, is copied by raw pointer, not content) may
still be holding the *exact same* heap object elsewhere in `self.hir_modules`
or `self.mir_modules`. There is no way, from `evict_ast()`, to know.

## 2. No free primitive for `text` exists in ANY runtime tier used to build/run Stage4

- **`core-c-bootstrap` (`src/runtime/runtime_native.c`) — the bundle Stage4
  actually links:** `rt_string_free` does not exist. `grep -n rt_string_free`
  over the whole file: zero hits. The string registry has a register+lookup
  pair (`rt_core_register_string`/`rt_core_is_registered_string`,
  lines 868-886) but **no unregister function** — contrast with arrays, which
  do have one (`rt_core_unregister_array`, lines 909-917). Strings are
  structurally leak-only in this runtime today; this is not "evict forgot to
  call an existing primitive," it is "the primitive was never built."
- **The one `rt_string_free` that does exist** is declared in
  `src/compiler/70.backend/sffi_minimal.spl:112` (`extern fn
  rt_string_free(ptr: i64)`) and its C header
  `src/app/sffi_gen.templates/simple_sffi.h:86` — but this belongs to a
  **separate, vestigial "minimal SFFI" ABI** (`RuntimeValuePtr`,
  `rt_value_string`/`rt_value_free`/`rt_value_clone`) that is not the
  `RuntimeValue` tagged-pointer heap model the compiler's own `text`/`[T]`
  values use elsewhere. Its `ptr` is documented (prior session's own reading,
  confirmed here) to come from `rt_file_read_text`-style raw C buffers, not
  from an ordinary `text` value's heap pointer. It has no backing
  implementation in `runtime_native.c` either — calling it from real driver
  code would be an unresolved-symbol link error under `core-c-bootstrap`.
- **The Rust runtime** (`src/compiler_rust/runtime/src/value/collections.rs`)
  also has no `rt_string_free` at all (only `rt_array_free`, line 1438).

## 3. `rt_array_free` (the one free primitive that DOES exist, both runtimes) is shallow

C (`runtime_native.c:3269-3272`) and Rust (`collections.rs:1438-1451`) both
free only the array's own backing buffer/header and unregister the array
object itself — **neither recurses into element values.** Freeing
`self.sources` (a `[SourceFile]`, each holding `text` fields) via
`rt_array_free` would drop the outer buffer but leak every string inside it
regardless — confirms the 2026-07-20 doc's reading, now checked against both
runtimes directly rather than one.

## Why a general primitive can't be built safely this session

Combining 1-3: a `text`/`[text]` deep-free primitive would need, at minimum,
(a) a brand-new free/unregister-string primitive in **both** runtimes
(doesn't exist), (b) recursion into container elements (existing
`rt_array_free` doesn't do this for either type), (c) a way to determine
"is this pointer reachable from anywhere else" — which requires either real
refcounting (a runtime-wide change, not a driver-tier patch) or an
ownership/liveness discriminator threaded through every AST/HIR
constructor — and (d) working correctly across every execution backend the
driver runs under (interpreter, Cranelift JIT/AOT, LLVM, self-hosted
native-build), since `evict_*` is ordinary `.spl` driver code, not
codegen-internal. None of this is boundable to one session without a real
risk of shipping the "wrong free = corruption, worse than the leak" outcome
the mission explicitly forbids.

## The one narrow target that stays provably safe (unblocked design, not built)

`source.content` specifically remains safe to free, by the same argument the
prior report already made, now reinforced by finding 1: `rt_string_new`
*always* copies bytes, so nothing the lexer produces from a file's content
can share that file's own top-level `content` string object — there is no
pointer-aliasing path from `SourceFile.content` into any surviving AST/HIR
node (unlike, say, a `Function.name`, which per finding 1 genuinely can
alias an arena slot). Its only known post-phase-2 reader
(`driver.spl:948-957`, the HIR-reparse fallback) is already gated off under
`--low-memory`.

Realizing even this narrow case requires, in order:
1. Add `rt_core_unregister_string` + `rt_string_free(int64_t)` to
   `runtime_native.c`, mirroring `rt_core_unregister_array` — **but** it must
   refuse to free anything present in `rt_core_short_string_cache` (0/1-byte
   strings, process-wide shared) or `rt_literal_intern_table` (literal
   interning, process-wide shared); freeing either would corrupt every other
   use of that cached value. `source.content` for any non-trivial file goes
   through neither cache, but the primitive must still check, not assume.
2. Add the Rust-runtime equivalent for parity (JIT/AOT/self-hosted paths that
   route through it instead of the C bundle).
3. Wire a real extern (not the vestigial `sffi_minimal.spl` one) reachable
   from `driver_types.spl`, verified linkable/callable under every backend
   `evict_sources()` can run under.
4. Call it per-`SourceFile` in `evict_sources()` in place of the current
   rebuild-and-reassign pattern.
5. Validate with the existing `evict_probe.spl` pattern extended to a real
   `text` value (not just array-of-empty-strings), confirming a negative
   `delta_evict` this time, THEN multi-file native-build + run correctness,
   THEN (only once both pass) one bounded/capped Stage4 attempt.

This is a legitimate, scoped next step — but items 1-3 are new runtime
surgery with their own correctness bar (a wrong cache-boundary check is a
process-wide corruption, not a per-file bug), and this session's budget does
not cover building + validating new C/Rust runtime primitives across every
backend inside its cycle cap. Not attempted; recorded here instead of
shipped half-verified.

## Reclamation / correctness evidence

No patch was applied (blocked before the wiring step), so there is nothing
new to measure. The existing before/after numbers from
`doc/09_report/stage4_memory_evict_never_frees_2026-07-25.md` stand
unchanged on this HEAD (`driver_types.spl` is byte-identical to what that
report examined): `before=0 after_fill=10002 after_evict=10004
delta_evict=+2` — i.e. still zero reclamation, for the reasons in finding 1-3
above (now root-caused one level deeper: not just "evict doesn't call free,"
but "the free primitive it would need to call doesn't exist for `text`, and
building a safe one requires solving reference-counting or an ownership
discriminator that no part of the runtime has today").

## Files

- This file: `files/doc/... ` — no source patch included (design-only
  deliverable per the mission's accepted "blocked with a precise reason"
  outcome).
