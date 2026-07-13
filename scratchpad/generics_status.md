# Generics / Monomorphization — Ground-Truth Status (#158)

Scope: `<T>` generic functions, structs, and methods on the native `--entry`
build path (`bin/simple native-build`, which interprets `src/compiler/*.spl`),
vs the interpreter oracle (`bin/simple run`). Measured on `origin/main`
(worktree `/tmp/wt_gen_probe`, detached at `54f5b35d96c`). No code changed;
worktree removed after measurement.

## 1. Ground-truth table

| # | Case | Oracle (`bin/simple run`) | Native (`native-build --entry`) | Verdict |
|---|------|---------------------------|----------------------------------|---------|
| 1 | `fn id<T>(x: T) -> T: x`; `print(id(42)+1)` | `<invalid-heap:0x151>` (broken artifact — `42<<3\|1`; `print(id(42))` alone correctly gives `42`, only `+1` arithmetic corrupts) | build OK; runs; prints **`1`** (i.e. `0+1` — bare `print(id(42))` prints **`0`**) | **SILENT-WRONG** (native) + **ORACLE-BROKEN** (separate boxing bug, arithmetic-only) |
| 2 | Same `id<T>`, two instantiations: `id(42)+1` then `id("hello").len()` | first print: same `<invalid-heap:...>` artifact; second print: `5` (correct — method-call unboxes fine) | build OK; runs; prints garbage (`1407315476975450`-class number) | **SILENT-WRONG** (native); oracle partially broken |
| 3 | `struct Box<T>: value: T`; construct `Box(value: 42)`; `print(b.value + 1)` | `0.00000000000000000` (broken — field read as `f64` zero) | build OK; runs; prints **`43`** — **correct** | **WORKS** (native) / **ORACLE-BROKEN** |
| 4 | Generic method: `Box<T>.get(self) -> T: self.value`; `print(b.get()+b.get())` with `value: 21` | `<value:0x15>` (broken — raw unboxed `21` printed as a tagged-pointer artifact) | build OK; runs; prints **`42`** — **correct** | **WORKS** (native) / **ORACLE-BROKEN** |
| 5a | Stdlib generic `Map<text, i64>.new()/insert/get` | `43` — **correct** (with a `Map.new() deprecated, use Map()` warning) | **build FAILS**: `error: HIR lowering error in g5_map: unresolved name: Map` (no explicit `use` needed for the oracle; native's prelude/global namespace doesn't register `Map` at all — tried `use std.map.Map` too: `unresolved import 'std.map.Map' ... no source file found`) | **LOUD-FAIL** (native) — separate name-resolution gap, not type-substitution |
| 5b | Builtin generic `[i64]` array `push`/index | `43` — correct | build OK; runs; **`PANIC: bounds_check intrinsic index=0 len=0`** (the `push` did not mutate `arr` — len stayed 0) | **SILENT-CRASH** (native) — likely array value-semantics/mutation bug, not a type-substitution bug (out of scope for #158 root cause below) |

**Interpreter oracle itself is broken in 4 of 5 cases** (1, 2-partial, 3, 4) —
all via the *same class* of boxing/unboxing bug: a generic-typed (`T`) return
value or field read is broken specifically when the caller does arithmetic or
plain-print on the raw value, but works when the caller invokes a method on it
(`.len()`) or when construction infers a concrete type structurally. Do not
use the oracle at face value for arithmetic on generic values — verify by
construction, same caveat as the closures investigation's named-fn-as-value
case.

## 2. Is #158 ("T parses to VOID") true?

**Partially — and precisely for one sub-case.** Bare generic **function**
parameters (`fn id<T>(x: T) -> T`) do fall through to an opaque/zero type on
native — this is real and matches #158. But generic **structs** (`Box<T>`)
and **methods on generic structs** (`Box<T>.get() -> T`) already work
correctly on native (cases 3, 4 → `43`, `42`). So "generics unimplemented" is
too broad, same pattern as #165's closures: the failure is scoped to one
lowering path, not the whole feature.

## 3. Root-cause chain (function-generic case only, cases 1–2)

1. **HIR type lowering registers `T` as a valid-looking symbol.**
   `src/compiler/20.hir/hir_lowering/types.spl:319-327` (`lower_named_kind`)
   resolves `T` to `HirTypeKind.Named(symbol_id, [])`. Because `T` was
   pre-registered as a `SymbolKind.TypeParam` symbol via `lower_type_param`
   (same file, line 336), `symbol_id.is_valid()` is true, so the
   `"unresolved type: {name}"` error path is never hit — `T` silently becomes
   a semantically-generic `Named` type instead of erroring loudly.

2. **MIR lowering has no substitution step and falls through to an opaque
   struct.** `src/compiler/50.mir/_MirLowering/function_lowering.spl:374-382`
   (inside `lower_type()`, defined at line 314): for a `Named` param type it
   calls `custom_primitive_underlying_type_tag_by_symbol(symbol)`
   (`src/compiler/10.frontend/core/types.spl:592-598`), which returns `-1` for
   any symbol not registered as a custom primitive — a bare `TypeParam` symbol
   never is. `-1` matches none of `TYPE_BOOL/TYPE_I64/TYPE_F64`, so execution
   falls through to line 382: `MirType(kind: MirTypeKind.Struct(symbol))` — an
   opaque, **zero-field** struct keyed by `T`'s symbol id. This has no LLVM
   layout, so the backend treats the param as zero-sized/zero, producing `0`
   instead of the real argument — exactly the observed behavior.

3. **Monomorphization is not wired into the native-build pipeline at all.**
   The real driver (`src/compiler/80.driver/`) never calls
   `specialize_function_with_types` or any `MonomorphizeEngine`. The only
   caller, `src/compiler/80.driver/pipeline_fn.spl`'s
   `compile_specialized_template` (lines 22-81), is a pure stub — every real
   step (monomorphize, HIR/MIR lowering, optimize, codegen) is commented out;
   it just returns an empty `CompiledUnit`. Explicit comment at line 74:
   `"Actual pipeline integration will follow as monomorphize/codegen mature"`.

4. **Both existing `type_subst.spl` files are dead/unimplemented scaffolding,
   reachable only from the dead stub above:**
   - `src/compiler/40.mono/monomorphize/type_subst.spl`: `substitute_type`
     (lines 48-50) is a literal identity no-op (`ty`); `concrete_to_hir_type`
     (lines 32-34) always returns `HirTypeKind.Error`. Called only from
     `engine.spl:183-189`, itself only reached via `pipeline_fn.spl`'s dead
     stub.
   - `src/compiler/10.frontend/core/type_subst.spl`: used by
     `monomorphize.spl`/`type_erasure.spl`, **not called from `80.driver/` at
     all**. Its `type_subst_specialize_decl` (lines 169-206) doesn't even
     clone the declaration — line 201: `val cloned_did = generic_did  # Will
     be replaced with actual clone`.

**Why the struct case (3, 4) works despite this:** `Box(value: 42)` infers
`T=i64` *structurally* from the literal initializer at HIR-lowering time —
the field gets a concrete `i64` MIR type directly from the constructor
expression's inferred type, never passing through the `Named(TypeParam)` →
`custom_primitive_underlying_type_tag_by_symbol` fallback that only the
*bare-parameter* path (`x: T` with no local inference hook) hits. This is a
different, working code path, not a symptom of monomorphization actually
happening.

**5a (`Map` unresolved) is unrelated:** it's a native-only global/prelude
name-resolution gap (`Map` isn't registered as a builtin in the native
pipeline's namespace the way it evidently is for the interpreter), not a
type-substitution issue. Not root-caused further here (out of scope /
time-boxed); flagged as a second, independent native-build gap worth its own
bug.

## 4. Phased implementation plan (mirrors `closures_plan.md` structure)

- **Phase A — Loud-fail gate (immediate, low-risk).** Until monomorphization
  lands, `function_lowering.spl:374-382`'s opaque-struct fallback for
  unresolved `TypeParam` symbols should raise a compile error instead of
  silently emitting a zero-field struct (mirrors closures Phase-A discipline:
  "must stay a loud fail, never build-and-return-garbage"). This alone fixes
  the worst failure mode (cases 1, 2: silent wrong answers) at near-zero risk,
  without implementing the feature.

- **Phase B — Call-site monomorphization (the real feature, MVP).** Wire
  `80.driver/pipeline_fn.spl`'s `compile_specialized_template` to actually
  call a substitution engine: for each generic call site (`id(42)`), infer
  concrete type args from argument types, look up/create a specialized copy
  of the function (`id_i64`) with `T` substituted by `i64` throughout the HIR
  before MIR lowering. Requires either fixing
  `10.frontend/core/type_subst.spl`'s `type_subst_specialize_decl` to actually
  clone+substitute the decl (currently a no-op clone), or replacing
  `40.mono/monomorphize/type_subst.spl`'s identity-no-op `substitute_type`
  with a real HIR-type substitution and wiring `engine.spl` into the live
  driver path. Verify against cases 1–2 → expect `43` and `5`.

- **Phase C — Struct/method generic parity (verify only, likely already
  fine).** Cases 3–4 already work via structural inference; once Phase B
  exists, add a regression test asserting struct-generic + fn-generic paths
  agree (e.g. `Box<T>.get()` feeding a generic `fn use_it<T>(x: T)`).

- **Phase D — Fix the two independent found bugs, tracked separately (not
  blocking Phase A/B):**
  - Interpreter's arithmetic/print-time boxing artifact for generic-typed
    values (cases 1, 2, 3, 4 oracle side) — same class of bug across 4 of 5
    cases; worth one shared fix in the interpreter's ANY/box-unbox path
    rather than four.
  - Native's missing `Map` builtin/prelude registration (case 5a) — separate
    bug, likely a driver-side prelude/global-namespace gap.
  - Native array `push` not mutating the caller's binding (case 5b) — likely
    array value-semantics, unrelated to generics.

## 5. Slice decision for this task: measurement only, no code landed

This was a read-only measurement task per instructions — no fixes were
applied. Phase A above (loud-fail gate) is the safest first landable slice
for a follow-up task: it is a small, single-file, low-risk change
(`function_lowering.spl`) that eliminates the silent-wrong-answer class of
bug without needing the full monomorphization engine.
