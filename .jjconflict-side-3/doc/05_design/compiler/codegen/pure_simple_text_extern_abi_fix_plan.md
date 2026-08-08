# Plan: pure-Simple codegen `text`-extern-argument `(ptr, len)` ABI fix

**Status:** DESIGN ONLY — no landing. See verdict at the bottom.
**Scope:** `src/compiler/**` (pure-Simple, self-hosted compiler). `src/compiler_rust/**`
is read-only reference here, never edited.
**Background:** audit at git commit `988ba740cce` (path
`doc/08_tracking/bug/pure_simple_text_extern_abi_audit_2026-07-30.md` — the
file was removed from the working tree by another session; recovered via
`git show 988ba740cce:<path>` for this plan). Companion RED spec on disk:
`test/01_unit/compiler/backend/text_extern_abi_ptr_len_divergence_spec.spl`.

## 1. Confirmed collapse sites (re-verified against current working tree)

| # | File:line | Function | Current behavior |
|---|-----------|----------|-------------------|
| 1 | `src/compiler/70.backend/backend/_MirToLlvm/class_def.spl:118-133` (`llvm_type_text`) | LLVM `.spl` backend | `MirTypeKind.Tuple(_)` (and Struct/Enum/Array/Dict/Slice/Union) all map to the single LLVM type `"ptr"`. `text`'s `Tuple([Ptr(U8), U64])` shape collapses to one opaque pointer type; the length field is invisible from here on. |
| 2 | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:212-229` (`mir_type_to_cl`) | Cranelift `.spl` adapter | Same collapse: `Tuple(_)` → `CL_TYPE_PTR`, one Cranelift type slot. |
| 3 | `src/compiler/70.backend/backend/native/isel_x86_64.spl:328-354` (`isel_call`) | Hand-written x86_64 isel | `for i in 0..args.len()`, one register/stack-slot per `MirOperand` — structurally the same one-word-per-operand assumption, no type-directed splitting at all. |

Task prompt's line numbers (131-132 / 231 / no line given) match these
functions within a few lines; the table above is current-tree-exact.

## 2. What each backend actually emits for a `text` extern arg today

- **LLVM backend:** one `ptr` value per source-level `text` argument. For a
  string **literal**, `translate_const_value`
  (`_MirToLlvm/core_codegen.spl:~1438`) emits a GEP into a `[N x i8]` global —
  a genuine NUL-adjacent C pointer, no length word. For a **local variable**
  holding `text`, whatever single value was produced earlier (see below) is
  passed as-is. Confirmed empirically by the RED spec: `call i64
  @rt_probe_text_len(ptr getelementptr …)` — exactly one top-level call
  argument, not two.
- **Cranelift adapter:** a string literal is boxed via
  `rt_string_new_literal(ptr, len)` into one **tagged runtime `Value` handle**
  (`cranelift_codegen_adapter.spl:~1036-1046`) — not a raw C pointer at all.
  `cl_translate_call`'s extern branch declares every param as `CL_TYPE_I64`
  and passes exactly one `i64`/handle per MIR operand.
- **x86_64 isel:** one register/stack slot per operand, generically; no
  special text/const-string handling was found in `isel_call` itself.
- **None of the three implements `(ptr, len)` correctly**, and per audit §4
  they don't even agree with each other on what the single collapsed word
  *is* (raw C pointer vs. boxed tagged handle vs. whatever isel produces).
- The one exception is a **name-based redirect**, not an ABI fix: LLVM
  backend's `translate_call` (`_MirToLlvm/core_codegen.spl:~1291-1301`)
  string-matches 5 extern names (`rt_process_run`,
  `rt_process_run_bounded`, `rt_process_run_inherit`,
  `rt_process_spawn_guarded`, `rt_process_run_timeout`) and rewrites the
  callee to a `*_tuple`/`*_value` **facade symbol** in `runtime_native.c`
  that itself accepts the single boxed/tagged `cmd` value — it does not
  split any argument into two words, and it is LLVM-only (Cranelift and
  x86_64 isel have no equivalent for these 5 names either).

## 3. Does a `text_arg_indices` / `RuntimeFuncSpec` analogue exist on the `.spl` side?

**No.** Confirmed by direct search:

```
grep -rn "text_arg_indices\|RuntimeFuncSpec" --include=*.spl src/
  → only src/lib/text.spl:70, a COMMENT pointing at the Rust-side names
```

There is no per-extern registry of text-argument positions, no shared
`.spl` table analogous to `RuntimeFuncSpec` (typed param list) or
`text_arg_indices` (which Simple-level args are text and need `(ptr, len)`
expansion) anywhere under `src/compiler` or `src/lib`. The only "registry"
that exists is the 5-name `elif` chain above, and it is a callee-symbol
rewrite, not a text-arg-position table — it doesn't generalize even in
shape, let alone content.

**This absence is the core of the problem**, per the task framing: without
a registry, no backend has a way to know *which* argument of an arbitrary
extern call is a `text` that needs splitting, nor whether the target ABI
even wants `(ptr, len)` vs. some other convention. Every fix shape short of
adding a registry degenerates back into more per-name `elif` chains
duplicated three times (once per backend).

## 4. Design: single MIR-level choke point + shared registry (recommended shape, NOT implemented here)

### 4.1 Why MIR-level, not per-backend

All three backends already do their generic "one machine value per
`MirOperand`" `Call` lowering independently. Splitting a `text` argument
into a genuine two-`MirOperand` call **before** any backend sees it means
all three backends' existing generic lowering becomes correct for free —
this is exactly the pattern `interpreter_calls.spl`'s
`rt_mem_attr_set_owner` workaround already proves works (audit §6): two
real operands survive unmodified through generic one-word-per-operand
lowering. The choke point is `emit_resolved_direct_call` in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:259-264`,
which is where `args: [MirOperand]` is finalized before
`MirInstKind.Call(dest, func, args)` is emitted.

### 4.2 The registry (the missing piece from §3)

A new small `.spl` module, e.g. `src/compiler/50.mir/text_extern_abi.spl`,
exporting:

```
fn text_arg_indices(extern_name: text) -> [i64]?
```

mirroring Rust's `text_arg_indices` in shape and — where the same C/Rust
runtime symbol is called — in **content** (copy the index lists for
`rt_panic`, `rt_mem_attr_set_owner`, `rt_env_get`, etc. verbatim from
`src/compiler_rust/compiler/src/codegen/instr/calls.rs:2388+`, since the
underlying `.c`/`.rs` implementations are shared and their real ABI doesn't
change per compiler). This is a data table, not new logic — low risk in
isolation, but only correct if kept in lockstep with the Rust list (see
migration order, §4.4).

### 4.3 The split itself

At `emit_resolved_direct_call`, when `func` resolves to a named extern
symbol present in the registry: for each index in `text_arg_indices(name)`,
replace `args[i]` (single `Str`/`Tuple([Ptr(U8),U64])`-typed operand) with
**two** operands — a `Ptr(U8)` operand and a `U64` operand — both derived
from the same source value. This is the hard, NOT-small part: unlike a
struct/tuple built via `Aggregate`, a `text` value is not uniformly
materialized as a real two-field aggregate in any backend's representation
today:
- LLVM: a literal is a GEP-into-global pointer with a compile-time-known
  length (fine — length is a constant). A **non-literal** `text` local
  (e.g. a function parameter, a concatenation result, a field read) has no
  MIR-level "get the length" instruction — `.len()` on `text` is presumably
  lowered to a runtime call (`rt_string_len` or similar) elsewhere; the
  split must reuse that path, not invent a new one.
- Cranelift: a literal is a **boxed tagged handle**, not a raw pointer —
  extracting `(ptr, len)` requires either unboxing via a runtime call, or
  (per audit §4) accepting that Cranelift's `text` representation must
  change first. There is no `GetField`-on-text shortcut: `GetField` lowers
  real materialized aggregates (confirmed present in all 3 backends at
  `_MirToLlvm/core_codegen.spl:540`, `cranelift_codegen_adapter.spl:589`,
  `native/isel_x86_64.spl:369`), but a `text` constant/value is never
  actually constructed as one of those aggregates — so a generic
  MIR-level `GetField(0)`/`GetField(1)` on a text operand is NOT a drop-in;
  each backend's `GetField`/`translate_get_field` would need a text-base
  special case anyway, which reintroduces exactly the 3x duplication this
  design was meant to avoid.
- x86_64 isel: no string-constant handling was found at all in `isel_call`
  — the split's ptr/len source there is presently undefined territory.

So the *registry* and the *choke point* are small and can be designed with
confidence; the *value-splitting mechanism* cannot be, because it depends on
each backend's incompatible internal representation of `text` (raw pointer
vs. boxed handle vs. unimplemented), which is a second, deeper divergence
documented in audit §4 that is prerequisite work, not a detail of this fix.

### 4.4 The ~5 existing workarounds (LLVM `*_tuple`/`*_value` redirect)

Disposition: **keep, do not remove**, until the general fix lands and is
verified equivalent. They solve a distinct problem (whole-result-shape
mismatch: `SplArray*` 3-word tuple return, not just an input `(ptr, len)`
split) for `rt_process_run*`/`rt_process_spawn_guarded`, and the general
`text_arg_indices` mechanism above only covers argument splitting, not
return-value reshaping. Folding them into the new registry is plausible
future work but is a distinct axis (args vs. returns) and should not be
conflated in the same change.

### 4.5 Migration order (never half-converted)

1. Land the registry module alone (data + `text_arg_indices` lookup fn),
   unused by any codegen path — zero behavior change, trivially safe.
2. Land the MIR-level split logic gated behind an explicit env/flag
   (mirrors existing `SIMPLE_BOOTSTRAP_STAGE4`-style gates in this repo) so
   it can be toggled off instantly if it regresses call lowering broadly.
3. Fix the **value-splitting mechanism** per backend (§4.3) — this is
   itself 3 sub-changes (LLVM length lookup for non-literal text, Cranelift
   unboxing, x86_64 isel text support), each independently landable and
   independently revertable.
4. Only after all 3 backends produce a correct 2-operand split under the
   flag, flip the flag on by default; run the RED spec (should flip to
   green — `arg_count == 2`) plus a broader native-build smoke pass.
5. Only then consider whether §4.4's 5 LLVM-only redirects can be
   generalized/retired.
6. Extend `text_arg_indices` coverage from the currently-known Rust-side
   names outward to the ~490-symbol `.spl` census (audit §"Census"),
   incrementally, not in one shot — reachability from AOT native-build
   output was explicitly NOT established by the audit and needs its own
   verification per symbol.

## 5. Verdict on step 5 (patch vs. stop)

**STOPPED AFTER THE PLAN. No code was written.**

Reasons:
- Step 3 confirms no registry exists — the task's own stop condition
  ("If it is large or needs a new shared registry, STOP after the plan")
  is met directly.
- The fix is not local to the 3 cited collapse sites: the value-splitting
  mechanism depends on each backend's *different* internal representation
  of `text` (raw C pointer vs. boxed tagged Cranelift handle vs.
  unimplemented in x86_64 isel), which is a second, deeper divergence — not
  a one-line change at any of the 3 collapse sites.
- The natural choke point (`emit_resolved_direct_call` in
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl`) is shared by
  **every** call in the compiler, extern or not — a mistake there is a
  whole-compiler regression, not a localized one.
- **There is no working test runner** in this environment (deployed
  `bin/simple` refuses `test`/`lint`/`fmt`). A change to the shared
  call-lowering choke point plus three backend-specific value-representation
  changes cannot be verified at all here. Writing it blind would violate
  the explicit constraint against unverifiable codegen changes.

Nothing in the working tree was modified by this task beyond this plan
document.
