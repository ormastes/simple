# Task #173 — Class vs Struct Semantics Probe (NATIVE `--entry` path)

**READ-ONLY characterization. No source edits made. No commit.**

Worktree: `/tmp/wt_classprobe` @ `f10db44f0f477e839562654672a1531d58c881c4`.
Oracle: `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl` (interpreter/JIT-fallback).
Native: `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o OUT --clean && OUT`.

## Headline finding

The native `--entry` path conflates `class` and `struct` **at the very first
bridge from flat-AST to the HIR/MIR-facing `Module` type**
(`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`), not at
50.mir. A `class` decl produces the exact same `Struct` record as a real
`struct` and is stored under the same `module.structs` dict; `module.classes`
is a dict literal that is **always empty** (`module_assembly.spl:459`,
`classes: {}`), so nothing downstream — including 20.hir's already-written
`SymbolKind.Class` branch — ever fires for a class.

This conflation was **inert** until bug #167's fix (struct pass-by-value
correctness, landed in `50.mir/_MirLowering/function_lowering.spl:148-210`)
started **materializing a private copy of every `Named`-typed parameter**
whose type name is registered in `struct_field_order` (fed straight from
`module.structs`). Because classes live in `module.structs` too, #167
silently converted every class parameter — including the implicit `self`
receiver of methods — from "accidentally reference-like" (nothing was ever
copied before #167) to **actually value-copied**. This is the live
regression: function-argument and self-receiver mutations on class instances
are now silently dropped on the native path, while local-variable aliasing
and direct index/field-chain mutation (which never cross that copy site)
still work correctly by accident.

Two ADDITIONAL defects were found empirically while running the matrix, both
independent of the class/struct conflation:
1. **#167's copy also swallows `self` mutations on STRUCT methods** (row 6e:
   oracle 41, native 1) — the copy branch does not exempt the method
   receiver, so `fn inc(self)` on a plain struct silently no-ops on native.
2. **Struct local-alias copy is missing entirely on native** (row 6b:
   `val b = a; b.x = 41` leaks into `a` — oracle 1, native 41) — #167 only
   copies at parameter-bind time; local `val`/`var` rebinding emits no copy.
3. **The W1006 mut-capability check is silently absent on native --entry.**
   On the `run` path, every mutating shape here (rows 1, 5, 6a, 6e) trips
   `HIR lowering error: Memory safety error [W1006]: mutation without mut
   capability` and falls back to the interpreter — i.e., the JIT path
   already HAS the loud-fail these programs deserve (per
   `doc/08_tracking/bug/struct_param_mutation_semantics_2026-07-03.md`,
   plain-`fn` param mutation and `fn`-method self-mutation are *supposed* to
   be statically rejected; `mut` param / `me` method are the documented
   spellings). `native-build --entry` build logs contain **zero** W1006
   diagnostics for the same sources (verified by grep on all build logs) —
   it compiles the rejected shapes silently and then miscompiles them. This
   reframes the oracle for rows 1/5/6e: the interpreter's "41" is itself the
   documented-lax behavior (interp performs the mutation the checker
   rejects); the *specified* behavior for the exact probe sources is a
   compile-time error. The reference-semantics question proper (what `mut`
   param / `me` method / assignment sharing must do for classes) is
   unaffected: classes still need reference semantics under the sanctioned
   spellings, and native still gets that wrong.

The function_lowering.spl file **already contains a code comment
(lines 168-187) written by a previous investigation of bug #167 that
identifies this exact conflation** — this probe corroborates it empirically
end-to-end and pins the missing upstream anchor points.

## Matrix — oracle vs native

`print(a.x)` (or equivalent) is the sole observable. Expected column = the
documented spec answer (`doc/06_spec/.../memory_spec.md`: "classes are
reference types … assignment shares", `.../structs_spec.md`: "structs are
value types … copied by default").

| # | Shape | Oracle | Native | Expected (spec) | Verdict |
|---|-------|--------|--------|------------------|---------|
| 1 | `class` instance passed to `fn bump(c: C): c.x = 41`, caller reads `a.x` | **41** (correct ref semantics) | **1** | 41 | **silent-wrong (native)** — got VALUE semantics via #167 copy-on-param-bind |
| 2 | `val a=C(..); val b=a; b.x=41; print(a.x)` (`val` binding) | **1** | **41** | 41 | **oracle-itself-suspect**: interpreter's `val`-binding path for a class instance appears to deep-copy on bind (a fresh, previously-uncharacterized landmine, distinct from but adjacent to #112). Native happens to match the documented-correct answer here (local aliasing never crosses the #167 copy site) |
| 2b | Same as #2 but `var b = a` (not `val`) | **41** (correct) | **41** (correct) | 41 | CORRECT (both) — confirms the `val`-specific interp quirk in row 2; `var` avoids it |
| 3 | `class` instance in array, mutate `arr[0].x = 41` directly | **41** | **41** | 41 | CORRECT (both) — direct index mutation never crosses a function/self boundary, so #167's copy site is not triggered either way |
| 4 | `class` instance as a struct field, mutate `h.c.x = 41` through the chain | **41** | **41** | 41 | CORRECT (both) — same reasoning as #3 (in-place chain mutation, no call boundary) |
| 5 | `class` with `fn inc(self): self.x = self.x + 20`, called twice, `print(a.x)` | **41** (1+20+20) | **1** (CONFIRMED empirically — matches the static-trace prediction from `function_lowering.spl:196-207` exactly) | 41 | **silent-wrong (native)** — `self` is lowered exactly like any other `Named` parameter and hits the identical #167 copy branch; both `inc()` calls mutate a discarded per-call copy, `a.x` never changes |
| 6a | `struct` instance passed to `fn bump(c: C): c.x = 41`, caller reads `a.x` | **1** (correct value semantics) | **1** (CONFIRMED) | 1 | CORRECT (both) — this is exactly the #167 fix's intended target, working as designed |
| 6b | `struct` `val a=C(..); val b=a; b.x=41; print(a.x)` | **1** (correct value semantics) | **41** (CONFIRMED) | 1 | **silent-wrong (native)** — a SEPARATE, struct-specific defect: local variable-to-variable aliasing (`val b = a`) is never copied on the native/MIR path at all (the #167 fix only inserted a copy at *function-parameter* bind time, `function_lowering.spl:148-210`; there is no equivalent copy-on-local-rebind for `val`/`var` declarations feeding from another local — see `20.hir/hir_lowering/statements.spl` `val`/`var` decl lowering, which just aliases the RHS's MIR value/local, no aggregate copy emitted). This affects **both** classes and real structs identically for plain local aliasing; it is orthogonal to the class/struct conflation (root causes #5/#9) and needs its own follow-up if struct value semantics are meant to hold for local rebinding too, not just for fn-parameter passing |
| 6c | `struct` instance in array, mutate `arr[0].x=41` | **41** | **41** (CONFIRMED) | 41 | CORRECT (both) — direct index write, no call boundary |
| 6d | `struct` instance as struct field, mutate `h.c.x=41` | **41** | **41** (CONFIRMED) | 41 | CORRECT (both) |
| 6e | `struct` with `fn inc(self): self.x=self.x+20`, called twice | **41** (oracle: receiver mutation via method IS visible — the settled interp semantics per `struct_param_mutation_semantics_2026-07-03.md`, methods mutate the receiver in place) | **1** (CONFIRMED) | 41 | **silent-wrong (native)** — CONFIRMED second defect, NOT class-specific: the #167 copy-on-param-bind also fires for the implicit `self` receiver of a *struct* method, so each `inc()` mutates a discarded per-call copy. #167's copy is over-broad in a second dimension: it should exempt (or write back) the method receiver, independent of the class/struct conflation fix |

### Sanctioned-spelling follow-up rows (added after finding the W1006 nuance)

The plain-`fn` shapes above are statically rejected by W1006 on the JIT
path, muddying which side is "truth". These rows use the DOCUMENTED
mutation spellings (`mut` param, `me` method) — they compile clean under
W1006 on the JIT path (no interpreter fallback), so oracle here is
unambiguous language truth:

| # | Shape | Oracle | Native | Verdict |
|---|-------|--------|--------|---------|
| 7a | `class` + `fn bump(mut c: C): c.x = 41` | **41** (clean compile, no W1006) | **1** (CONFIRMED) | **silent-wrong (native)** — the single most damning row: fully sanctioned code, documented "caller observes the mutation" semantics, silently miscompiled |
| 7b | `class` + `me inc(): self.x = self.x + 20`, called twice | **41** | **1** (CONFIRMED) | **silent-wrong (native)** — sanctioned `me` self-mutation dropped |
| 7c | `struct` + `me inc(): self.x = self.x + 20`, called twice | **41** | **1** (CONFIRMED) | **silent-wrong (native)** — struct-side too: `me` receiver mutation dropped, independent of the class conflation |

*(5 class + 5 struct primary shapes + the 2b val/var landmine sub-row = the
requested 11-row matrix; rows 7a-7c are bonus sanctioned-spelling
confirmations.)*

## Test source files (preserved, not committed)
All 14 probe sources (c1..c5, c2b, s1..s5, c1m/c5m/s5m sanctioned variants)
copied to `/home/ormastes/dev/pub/simple/scratchpad/class_probe_fixtures/`
(the `/tmp/wt_classprobe` worktree was removed after the probe). Each is a
self-contained `--entry`-buildable single file; re-run with
`env -u SIMPLE_BOOTSTRAP bin/simple run FILE` (oracle) vs
`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry FILE -o OUT --clean && OUT`.

## Anchor-point inventory (file:line)

1. **`src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl:724-726`**
   — parser builds `class` and `struct` decls through the *same*
   `decl_struct_def(...)` call; the only discriminator recorded is a
   side-table flip `decl_set_is_value_type(struct_d, 0)` when `is_class`.
2. **`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:226,258,289,367-372`**
   — the `decl_is_value_type: [i64]` side table + get/set accessors (from
   bug #108). Exists, populated correctly, but only read by the flat-AST
   interpreter.
3. **`src/compiler/10.frontend/core/_Ast/module_state.spl:530-548`**
   — `decl_get(idx) -> CoreDecl` copies the bit into `CoreDecl.is_value_type`
   for the *interpreter's* decl view only.
4. **`src/compiler/10.frontend/core/interpreter/eval_calls.spl:293,350`** —
   the only consumer of `is_value_type`, gating struct-vs-class copy-on-bind
   inside the flat-AST interpreter's function-call path.
5. **`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:107-461`**
   — `flat_ast_to_module`, the flat-AST → `Module` bridge used by the
   native/HIR pipeline. `tag_text == "3"` branch (~150-256) builds a
   `Struct(...)` record for **both** class and struct decls and inserts it
   into `structs[s_name]` (line 246) with **no reference to
   `decl_get_is_value_type`/`decl_is_value_type` at all**. `classes: {}` at
   line 459 is a literal empty dict — **THE root conflation point**.
6. **`src/compiler/10.frontend/parser_types.spl:219-230`** — the `struct
   Struct` record type itself has no `is_value_type`/`is_class` field to
   carry a discriminator even if #5 were fixed to read it — needs a new
   field, or a separate `Class` record type populated into a real
   `module.classes`.
7. **`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:646-661`**
   — `declare_module_symbols` already iterates `module.classes` →
   `SymbolKind.Class` and `module.structs` → `SymbolKind.Struct` correctly.
   `SymbolKind.Class` (declared `hir_types.spl:93`, used `hir_types.spl:226`)
   is genuine, existing, and **currently dead** for real classes because of
   #5. Fixing #5/#6 makes this branch start firing with no further edits
   needed here.
8. **`src/compiler/50.mir/_MirLowering/module_lowering.spl:328-345`** —
   `struct_field_order[struct_def.name] = field_names` built from
   `module.structs.values()`; comment at line 341-343 says "structs only,
   not classes" — aspirational, contradicted by #5 in practice.
9. **`src/compiler/50.mir/_MirLowering/function_lowering.spl:148-210`** —
   **the live regression site**. `is_named_struct = struct_field_order.has(name)`
   (line 151) is true for classes too (via #8); when true, every matching
   parameter — `self` included (its type comes from
   `declaration_lowering.spl:190-207`, same `Named(class_type)` shape) —
   gets rebound to a freshly materialized field-by-field copy
   (`emit_aggregate`, lines 197-207) with **no write-back**. Comment block
   at lines 154-187 already documents this exact gap from the #167
   investigation.
10. **`src/compiler/70.backend/backend/objects.spl` +
    `backend_types.spl`'s `ObjectValue{class_name, handle}`** — the
    **already-shipped interpreter-side fix** (task #112) for the identical
    ref-vs-value conflation, using a shared `ObjectStore` + integer-handle
    model. This is the natural design template for a native-side fix:
    represent class instances as a heap-allocated record behind a pointer
    that is never copied by `emit_aggregate`, vs. structs which legitimately
    get the #167 field-copy.

## Recommended smallest sound fix (for the later fix lane)

Two independent layers need one bit of information threaded through, or a
hard gate until it is:

- **Data-model fix** (frontend → HIR bridge): add `is_value_type: bool` (or
  `is_class: bool`) to `struct Struct` (`parser_types.spl:219`); in
  `module_assembly.spl`'s `tag_text=="3"` branch, read
  `decl_get_is_value_type(idx)` (already computed, just unused here) and
  either (a) set the new field on the `Struct` record, keeping one dict, or
  (b) route `is_value_type==0` decls into a new `Class` record type and a
  real `module.classes` dict (matches what `hir_lowering/_Items/
  module_lowering.spl:646-661` already expects). Option (a) is smaller —
  no new record type, no downstream consumer changes beyond #9.
- **Codegen fix** (50.mir): in `function_lowering.spl:148-210`, only take
  the field-by-field-copy branch when the type is a genuine value type
  (`is_named_struct and is_value_type`); for classes, leave the parameter
  bound to the caller's local (current pre-#167 behavior, restoring
  reference semantics) — or, more robustly long-term, heap-allocate class
  instances at construction (mirroring `backend/objects.spl`'s handle model)
  so aliasing is correct **by representation**, not by skipping a copy.
  The same branch must ALSO exempt (a) `mut`-declared params and (b) the
  `self` receiver of `me` methods — grep confirms the current code has no
  `is_mut`/`me` check of any kind (only hit for "mut" in the whole file is
  the unrelated `Ref(inner, mutable)` type-lowering arm at lines 359-360),
  so even the documented-sanctioned mutation spellings get their mutations
  copied away today (empirical rows 7a-7c below).
- **Until the above lands**, a **loud-fail gate** is the safe stopgap: when
  `struct_field_order.has(name)` is true for a symbol whose `SymbolKind`
  cannot be verified as `Struct` (i.e., today, always — since #5 makes this
  unverifiable), native-build could refuse to compile any class with a
  mutating method or a fn taking a class parameter with a diagnostic
  ("class reference semantics not yet implemented on native path — see
  #173"), rather than silently miscompiling. This trades a hard compile
  error for silent data corruption, which matches this repo's "no
  cover-up fixes" rule.

## Parallel-lane ownership note

Files #1-#4 and #10 above are **frontend/interpreter** territory (already
touched by #108/#112, both closed). Files #5-#6 are the **frontend↔HIR
bridge** (`_FlatAstBridge/`) — currently quiet, look safe to touch. File #9
(`50.mir/_MirLowering/function_lowering.spl`) is the **exact file that
carries the #167 fix** and has an explicit in-source comment inviting this
follow-up (lines 168-187) — low risk of conflicting with other in-flight
work since it already documents awareness of the gap. Per `git status` at probe time (checked against the live main-repo working
copy, not the pinned worktree), only `src/compiler/10.frontend/core/_Ast/
decl_nodes.spl` among the files in this inventory is currently modified by a
parallel session — and that diff is an unrelated null-safety hardening for
freestanding one-binary builds (`rt_array_len_safe`, guards a raw-0-handle
read in zeroed `.bss`), touching none of the `is_value_type` machinery.
Files #5, #6, #7, #8, #9 (the actual fix-lane files: `_FlatAstBridge/
module_assembly.spl`, `parser_types.spl`, `hir_lowering/_Items/
module_lowering.spl`, `50.mir/_MirLowering/{module_lowering,
function_lowering}.spl`) are untouched in the current working tree. The many
other parallel sessions' in-flight changes are concentrated elsewhere
(`20.hir/hir_lowering/_Items/lowering_helpers.spl`, `20.hir/hir_lowering/
expressions.spl`, `50.mir/_MirLoweringExpr/method_calls_literals.spl`,
`60.mir_opt/mir_opt/var_reassign_ssa.spl`, `70.backend/*`, `80.driver/
driver_bootstrap.spl`, and various SimpleOS/boot files) — none overlapping
this fix lane's files, so it should be safe to start without a rebase
collision, modulo re-checking `git status` again at fix time since this is a
fast-moving shared repo.
