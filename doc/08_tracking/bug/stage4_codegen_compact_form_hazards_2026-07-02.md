# Stage4 (seed-compiled self-host) codegen hazards — `-c "print(1+1)"` crash chain

Task #59. Each layer is a place where the **Rust seed's native (cranelift)
codegen** mis-executes a construct that the seed itself accepts. Fixes so far
were `.spl`-side restructures at the miscompiled site; the layer below is a
genuine seed codegen bug with **no known use-site `.spl` workaround**.

## Cleared layers (committed: 85cd7c061d91, f70c200addb2)

1. **Compound bool condition nil-checked as heap pointer** (`lower_function`):
   an array-index bool result was nil-checked as if it were a heap pointer →
   SIGILL. Fixed via nested `if`s + an intermediate `bool` var.
2. **`fn_.return_type.?` gate always true**: a non-optional `Type` holding an
   `Infer` placeholder was treated as present, lowering `Infer` → SIGSEGV.
   Fixed by gating on `has_return_type` instead of `.?`.

Pattern for 1–2: the compiled stage4 mis-executes *compact* `.spl` forms;
restructuring (nested ifs, intermediate vars, field-access instead of wide
positional destructure) clears each site.

## Layer 3 (FIXED 2026-07-02, iteration 6): qualified enum pattern whose variant name collides with a struct type

### Root cause (isolated in iteration 6)
Not a runtime enum-layout offset issue. Construction (`EnumWith`/`rt_enum_new`)
was always correct. The divergence is in the seed's HIR pattern-binding
lowering: `build_pattern_binding_stmts`
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`) looked up the
pattern's **variant name** as a type, and if a struct/class of that name existed
it lowered the payload binding as a **positional struct FieldAccess (byte offset
0 on the enum object)** instead of `rt_enum_payload`. That heuristic is only
meant for the parser's *unqualified* ambiguous form
(`Pattern::Enum{name:"_", variant:"ClassName"}`). For a **qualified** pattern
`case StmtKind.Expr(pe)` where `enum StmtKind: Expr(Expr)` collides with `struct
Expr`, it read the enum header at offset 0 → corrupt payload pointer → SIGSEGV
on first field access.

Minimal (non-frontend) repro: hand-made `struct MyExpr` + `enum MyStmt:
MyExpr(MyExpr)` matched as `case MyStmt.MyExpr(pe)` (scratchpad `t6.spl`).
Previous iterations' hand-made types never reproduced because their variant
names did not collide with a struct name.

Isolation matrix (all `seed native-build`, ~4 s each): `t1` direct field match
(no enum), `t2` multi-arg/array-payload variant, `t3` `StmtKind.Throw(Expr)`
(non-colliding variant, same payload type) — **all pass**; only the
struct-named variant `StmtKind.Expr(Expr)` crashed. `t4` proved the discriminant
was correct; MIR dump showed the working case emits `Call rt_enum_payload` while
the colliding case emits `FieldGet byte_offset:0`.

### Fix (committed)
Gate the class/struct-destructure path on `enum_name == "_"`. Qualified patterns
(real enum type name) are unambiguously enum variants and always use
`rt_enum_payload`. One-file change in `stmt_lowering.rs`. rep9.spl / t6.spl now
print "OK NO CRASH" / "TAGOK"; t1–t5 still pass.

## Layer 4 (FIXED 2026-07-02, iteration 6): `effective_visibility` homonym mis-resolved during HIR lowering

After Layer 3, the chain advanced to a **controlled** trap (rc=132 SIGILL,
"runtime error: field access on nil receiver") in
`common.dependency.visibility.effective_visibility` ← `compute_visibility`
(`hir_lowering/types.spl:179`) ← `lower_function`. `types.spl` imports the
intended 3-arg `common.visibility.effective_visibility(text,text,bool)->bool`
(line 12) **and** `Visibility` from `common.dependency.visibility` (line 13).
The seed's name resolution leaked the 4-arg homonym
`common.dependency.visibility.effective_visibility(DirManifest,text,
ModuleContents,SymbolId)->Visibility` into scope and bound the call to it,
passing `false` where a `ModuleContents` was expected → nil `self.symbols` in
`ModuleContents.symbol_visibility` → trap.

Fix (committed): the 4-arg dependency copy has **zero callers in the pure-Simple
compiler** (compiler call sites are all 3-arg; 4-arg callers live only in the
Rust seed tree + `src/lib` dependency_tracker). Renamed it to
`dir_effective_visibility` (+ its export in `dependency/__init__.spl`) to
dissolve the collision. **Underlying seed bug (records for a future seed fix):**
same-named free functions in sibling modules are not disambiguated by explicit
`use` — importing only `Visibility` from a module leaks its other public
symbols into name resolution and can shadow an explicitly-imported homonym.

## Layer 5 (OPEN — root-caused 2026-07-02, iteration 6): `Dict<SymbolId, HirFunction>` indexing nil-derefs on 2nd key in interpreter `process_module`

After Layers 3+4, the chain advanced into the interpreter backend. `-c
"print(1+1)"` now fully completes frontend + HIR lowering; crash moved to:

```
#0 backend.interpreter.InterpreterBackendImpl.process_module   (interpreter.spl:50)
#1 driver.driver_types.CompileContext.create_outlined_4
#2 driver.driver.CompilerDriver.interpret_pipeline → .interpret → .compile
```

### Iteration 7 (2026-07-02): re-diagnosed — nil is the **key from `.keys()`**, worked around in `.spl` (crash CLEARED)

The iteration-6 marker theory ("2nd `module.functions[symbol]` index nil-derefs")
was **imprecise**. Corrected findings:

- **Exact fault (gdb, break on `rt_eprintln_str` before the `fields.rs:35`
  nil-guard `ud2`):** frame #1 is `process_module`, first loop, **first
  iteration**. A reordered-instrumentation build (`val kid = symbol.id` moved to
  the loop top) printed `PM iter` then trapped **before** `PM kid ok` — i.e.
  **`symbol` itself (the key yielded by `module.functions.keys()`) is a nil
  pointer**, trapping at `symbol.id` (FieldGet offset 0). In the original code
  this surfaces at `main_symbol_id = symbol.id` (only taken for the `main`
  entry), matching the disassembly's offset-0 load.
- **The seed's struct-keyed-Dict codegen is NOT the bug.** Seven `seed
  native-build` repros (~2 s each) exercised `Dict<SymbolId{id:i64}, V>` with:
  distinct keys, an `id:0` key, keys read from a value's struct field
  (`d[f.symbol]=f`), a two-module `SymbolId` name collision (`{id:i64}` vs
  `{name:text}`), collision **plus** `symbol.id`, and an **empty** dict — all
  round-trip `keys()`/index/`symbol.id` correctly (empty → `[]`, no nil). The nil
  key only appears for the **real** `HirModule.functions`; the minimal shape was
  not isolated this pass.
- **`hir_fn.symbol` is provably non-nil at insert** (`declaration_lowering.spl`
  `lower_function`: `fn_symbol_id` starts `SymbolId(id:-1)`, then
  lookup-or-`define`), so the value carries a good `SymbolId` even though
  `keys()` yields nil.

**Fix applied (iteration 7, `.spl`-side, `interpreter.spl` `process_module`,
committed):** iterate `module.functions.values()` and derive the key from each
function's own `fn_.symbol`; capture the `main` `HirFunction` directly
(`main_fn_opt`) and call it in the tail instead of re-indexing
`module.functions[SymbolId(id: main_symbol_id)]`. **Result:** `run hello.spl`
(fn main: print(1+1)) goes from **rc=132 SIGILL → rc=0** — the nil-deref crash is
cleared. The underlying seed `keys()`-returns-nil bug for this module shape
remains **open** (needs the still-unisolated minimal repro).

### Separately found (iteration 7): `.get()`→`Some(payload)`→field-access corrupts (Layer-3 family)

Cheap repro `dvc` (scratchpad): `match d.get(k): case Some(fn_): use fn_.name`
traps with the same "field access on nil receiver", while identical logic via
`val fn_ = d[k]` (index, non-optional) works (`dvb`). Extracting a **struct
payload from the `Some(...)` optional** returned by `Dict.get` yields a corrupt
pointer — same enum struct-payload family as historical Layer 3. Not on the `-c`
path (interpreter uses `[]`), but a real seed codegen bug.

NOTE: plain `-c` (without `SIMPLE_UNSTUB_HIR`) is currently a silent no-op
(stubbed), so reaching "2" requires this interpreter path to work.

## Layer 6 (OPEN — iteration 7): interpreter runs `main` cleanly but prints nothing

After the Layer-5 fix, `SIMPLE_UNSTUB_HIR=1 <stage4> run hello.spl` (`fn main():
print(1+1)`) and `-c "print(1+1)"` no longer crash — `run` now exits **rc=0**
(was rc=132) — but produce **no stdout** ("2" never appears; `print(42)` also
silent; not a flush issue — `stdbuf -o0` unchanged). So either
`module.functions.values()` is empty for the synthetic-main module (⇒ `has_main`
false ⇒ `BackendResult.Unit`, `main` never called) — which would also explain
the nil `keys()` element (degenerate dict for this shape) — or `main` is called
but the interpreter's `print`/`println` builtin does not reach real stdout.
Next step (iteration 8): instrument `process_module` to log
`module.functions.values().len()` + whether `has_main`/`call_hir_function(main)`
are reached; if `main` runs, trace the `print` builtin in
`interpreter_calls.spl`. Rebuild is incremental (~2.5 min, seed unchanged).

## Layer 3 (historical, superseded by the Layer 3 fix above): enum struct-payload extraction returns inline garbage

### Symptom
`SIMPLE_UNSTUB_HIR=1 <stage4> -c "print(1+1)"` → rc=139 SIGSEGV.
Fault (fork-aware gdb, from repo root — the crash only reproduces with cwd at
the repo root; a different cwd takes a non-crashing path):

```
#0 hir_lowering.statements.HirLowering.lower_hir_stmt   (statements.spl:69 `match expr.kind`)
   -> lower_hir_block -> lower_function (synthetic main) -> lower_module
```

Faulting instruction: `and $~7,%rdx; mov (%rdx),%rdi` then
`rt_enum_check_discriminant` with disc `0xcc861c0c` = hash("Assign") (the first
arm of `match expr.kind`). The scrutinee value is a *packed* word such as
`0x1800000007` / `0x1800000000` / `0x900000002` (two 32-bit halves), **not a
heap pointer** — masked and dereferenced → SIGSEGV.

### Root cause
Extracting a **struct-typed single payload from an enum via pattern match**
returns **inline packed data instead of the payload pointer**, for the real
recursive frontend AST types (`Expr` / `ExprKind` / `StmtKind`).

Minimal chain in `module_assembly.spl` (synthetic `fn main` for `-c`):
`init = Expr(kind: ExprKind.Call(...), span)` is valid → wrapped as
`StmtKind.Expr(init)` → later `case StmtKind.Expr(expr)` yields a **corrupt
`expr` pointer** (both `expr.kind` and `expr.span` would fault). The `StmtKind`
*discriminant* survives (matches `Expr` correctly); only the extracted payload
pointer is wrong. Construction and extraction **disagree on the enum
payload-slot offset**.

### Isolation (all via `seed native-build`, ~2–7 s each)
- Reproduces with the **real** `Expr`/`ExprKind`/`StmtKind` types.
- Does **not** reproduce with structurally-identical hand-made types, even with:
  recursion (enum contains the struct), large inline variants, multi-variant
  differently-sized enums, tuple/optional payloads, or a 40-byte payload struct.
- **Not** a cross-module name collision: reproduces building only
  `src/compiler/10.frontend` + `00.common` (no macro/lib `enum Expr`), and
  removing the `frontend -> 10.frontend` symlink does not change it.
- **No use-site `.spl` workaround**: the payload is corrupt *at extraction*.
  Reading via a free function (`fn get_kind(e: Expr) -> ExprKind: e.kind`) or an
  intermediate var still faults; un-nesting the construction
  (`val se = StmtKind.Expr(init); Stmt(kind: se, ...)`) does not help.
- Trigger is specific to the real `parser_types_expr.spl` type *definitions*
  (50-variant `ExprKind` with cross-file payload type refs). The exact
  distinguishing feature within those definitions is not yet isolated.

### Minimal reproducer (7 s build)
```spl
# rep9.spl — build: seed native-build --backend cranelift
#   --source src/compiler/10.frontend --source src/compiler/00.common
#   --source rep9.spl --entry-closure --entry rep9.spl --runtime-path <seed dir>
use compiler.frontend.parser_types_expr.*
use compiler.frontend.lexer_types.{Span}
extern fn rt_eprintln_str(s: text, n: i64)
fn say(s: text): rt_eprintln_str(s, s.len())
fn mk_span() -> Span: Span(start: 0, end_pos: 0, line: 1, col: 1)
fn main():
    val span = mk_span()
    val init = Expr(kind: ExprKind.NilLit, span: span)
    val se = StmtKind.Expr(init)
    match se:
        case StmtKind.Expr(pe):
            say("extracted")
            match pe.kind:                    # <-- SIGSEGV: pe is corrupt
                case ExprKind.Assign(a,b,c): say("assign")
                case _: say("OK NO CRASH")
        case _: say("other")
# Prints "extracted" then crashes. "OK NO CRASH" never printed.
```

### Next step (for a seed fix)
The bug lives in the seed's enum payload store/load offset for struct-typed
single payloads of these recursive types (cranelift path:
`src/compiler_rust/compiler/src/codegen/instr/pattern.rs` `compile_pattern_bind`
/ `rt_enum_payload`, and the matching `rt_enum_new` construction). Construction
and extraction must agree on the payload slot. Use `rep9.spl` as the regression
gate. A use-site `.spl` fix is not available; this requires a seed codegen fix
(or isolating and adjusting the offending `parser_types_expr` type definition).

---

## Iteration 8 (2026-07-02) — interpreter reads corrupt `HirFunction` from `Dict<SymbolId,HirFunction>.values()`

Localized exactly why `SIMPLE_UNSTUB_HIR=1 simple -c "print(1+1)"` runs silently
(rc=0, no `2`). Traced `-c` → `cli_run_code` → self-exec fallback →
`interpret_file` → `CompileMode.Interpret` → `CompilerDriver.interpret_pipeline`
→ `InterpreterBackendImpl.process_module` (src/compiler/70.backend/backend/interpreter.spl).

### Ground truth (file-append + `print`/`eprint` probes, cranelift stage4)
For the synthetic-`main` module built from `print(1+1)`:
- `module.functions.len()` == **1** (correct count).
- The symbol table reads **correctly**: iterating `module.symbols.symbols` finds a
  `Symbol` whose `name == "main"` (`has_main=T`), and `sym.id.id` is readable.
- But the single `HirFunction` obtained via `for fn_ in module.functions.values()`
  is **corrupt on field read**:
  - `fn_.name` → garbage text, `.len()` returns **-1** (so `nm == "main"` never
    matches → original code sets `has_main=false` → `main` never called → silent).
  - `fn_.symbol` → **null** (`fn_.symbol.id` traps `field access on nil receiver`).
  - `fn_.body.stmts.len()` → **0** (real body lost).
- `Dict<SymbolId,HirFunction>.has(main_sym)` / `[main_sym]` **also fail** to find
  the present entry (struct-keyed Dict lookup miscompiled), even when `main_sym`
  is taken from the (correct) symbol table.

### What this rules out
- NOT monomorphization (returns modules unchanged when no generics — our case).
- NOT the `main`-detection logic: rewriting `process_module` to locate `main` via
  the symbol table (`Symbol.name`, authoritative) correctly sets `has_main=T`, but
  the function's **body is unreadable**, so it cannot be executed.
- NOT (solely) a struct-name collision: there are duplicate `struct HirFunction`
  (85.mdsoc `hir_function.spl` `{name,param_count,return_type,body_inst_count}`,
  30.types `bidir_phase1c.spl`) and duplicate `struct SymbolId`
  (hir_types `{id:i64}` vs 00.common/dependency `{name:text}`, +lib copies).
  Renaming the `HirFunction` duplicates to unique names (`MdsocHirFunction`,
  `Phase1cHirFunction`, matching the existing `BidirHirFunction` precedent) and
  the `{name:text}` `SymbolId` duplicates (`DepSymbolId`) did **not** change the
  corruption — `body_stmts` stayed 0. (Incremental builds only recompiled the
  edited files; a full clean rebuild was not attempted and may still matter if the
  seed picks a global struct layout — but the read stayed corrupt regardless.)

### Conclusion
Same seed codegen class as the rep9.spl reproducer above (enum/struct payload
store/load offset). Here it manifests as **struct-valued `Dict.values()` / struct
field reads returning a default/empty struct** (null pointer fields, garbage text,
empty arrays) in the interpreter-backend compilation unit, while the same data
reads fine in the frontend/symbol-table path. Because the function *body* itself is
unreadable, there is **no use-site `.spl` workaround** in `process_module` — a
name-lookup workaround finds `main` but cannot obtain its statements. Requires the
seed cranelift fix for struct payload/field offsets (see rep9 "Next step").

### Probe idiom that works vs traps
- `print`/`eprint` of **string literals + integers** work (survive on clean exit;
  `eprint` unbuffered).
- Any probe that reads a nested field on a `.values()`-iterated `HirFunction`
  (`fn_.symbol.id`, `fn_.name` in `+`/interpolation) either returns garbage or
  traps `field access on nil receiver` — do not build diagnostics on those.

---

## Iteration 9 (2026-07-02) — ROOT CAUSE FOUND + FIXED: Dict type-erasure → ANY element → wrong field index on name-collision

**This was NOT a struct store/load representation bug.** The runtime pointer
stored in the dict is correct. The bug is entirely in the seed's **static
field-index resolution** for field access on an `ANY`-typed receiver.

### Root cause chain
1. The seed **erases `Dict<K,V>` to `ANY`**:
   `compiler_rust/.../hir/lower/type_resolver.rs:426` → `"Dict" => Ok(TypeId::ANY)`.
   There is no `HirType::Dict{key,value}` variant; the value type `V` is not
   tracked anywhere.
2. Therefore `module.functions` has type `ANY`, and
   `module.functions.values()` returns `ANY`:
   `compiler_rust/.../hir/lower/expr/mod.rs:962` →
   `"keys"|"values"|"items"|"entries" => Some(TypeId::ANY)`.
3. The `for fn_ in ....values()` loop variable is thus `ANY`. Field access
   `fn_.name` / `fn_.symbol` on an `ANY` receiver goes through
   `hir/lower/expr/access.rs` `get_field_info(ANY, field)` → `CannotInferFieldType`
   → falls to the **"most-fields-wins" global field resolver** (search all struct
   defs for a struct containing a field of that name, pick the one with the most
   fields). `name`/`symbol`/`body`/`span` are defined in *dozens* of structs, so
   the resolver returns some **other** struct's field index → wrong byte offset on
   the real `HirFunction` pointer → `name.len()==-1`, `symbol==null`,
   `body.stmts.len()==0`, and the enclosing function gets **stubbed** (silent `-c`).

### Why prior isolation missed it
- **Not struct size / boxing threshold.** Structs use flat `i*8` layout; the
  pointer is fine.
- **Renaming duplicate `HirFunction` structs didn't help** because the resolver
  matches by **field NAME across ALL structs**, not by struct name.
- **iteration-7's 7 dict repros passed** because their value-struct field names
  (`id`, `name` on the *only* struct with that field) did **not collide** with a
  larger struct — the global resolver returned the correct index by luck. The
  missing shape property is **field-name collision with a larger struct**, not
  size, nesting, or key type.

### Minimal repro (`scratchpad/colrepro.spl`, ~1.3 s seed native-build)
`struct Fnv{symbol,name,body}` (name @ idx 1) + `struct BigDecoy{name,a,b,c,d,e}`
(name @ idx 0, more fields) + `Dict<SymbolId,Fnv>`; `for fn_ in d.values():
say(fn_.name)`. **Prints nothing** (main stubbed). Remove `BigDecoy`
(`scratchpad/nodecoy.spl`) → prints correctly. Confirms the trigger is the
colliding decoy, and the reader path is otherwise correct.

### Fix (`.spl`-side, seed already supports it; committed ee1b0919c7a)
No feasible small **seed** fix: making `.values()` return `[V]` requires adding a
typed `HirType::Dict` variant and threading K/V through the whole type system
(large, risky). Instead, bind each element to a **typed local** so the field
access resolves against the real struct type:
```spl
for fn_ in module.functions.values():
    val f: HirFunction = fn_          # re-types ANY -> HirFunction
    ... f.symbol ... f.name ...       # correct field indices
```
Proven on `scratchpad/colfix_a.spl` (adds `val f: Fnv = fn_`) → prints
correctly despite the decoy. (Typed for-loop vars `for x: T in ...` are NOT
grammar-supported — `colfix_b.spl` fails to parse.) Applied to
`src/compiler/70.backend/backend/interpreter.spl` `process_module`.

### General hazard (records for future work)
Any `d.values()` / `d.get()` / `d[k]` result whose field name is shared with a
larger struct silently reads the wrong field across the **whole** compiler. A
real seed fix (typed Dict, or having the global resolver refuse ambiguous
name-only matches instead of guessing) would eliminate the class. Until then,
bind dict-derived struct values to a typed local before field access.

---

## Iteration 10 (2026-07-02) — `-c "print(1+1)"` under `SIMPLE_UNSTUB_HIR=1`: crash chain advanced 6 stages, hits an ANY enum-payload wall

Goal: make `SIMPLE_UNSTUB_HIR=1 simple -c "print(1+1)"` print `2`. Started from
"runtime error: field access on nil receiver" (SIGILL, rc=132). gdb on the
native stage4 binary (cranelift) localized each stage precisely (no probes
needed — `bt`, `info registers`, `x/gx` on the tagged/masked object pointers).

### Crash chain fixed this iteration (all committed, durable)
1. **`5634403261b2`** `interpreter.spl process_module` symbols loop iterated
   `module.symbols.symbols.keys()` + re-index. Switched to `.values()` + typed
   `val sym: Symbol` (mirrors the functions loop). (Was not the live crash, but
   the same hazard.)
2. **`a352c91b7773`** process_module found main via `f.symbol.id == main_id`, but
   single-file lowering leaves the synthetic `-c` main's `HirFunction.symbol`
   (boxed SymbolId at offset 0) **nil** (`*rcx==0`), so the chained deref trapped.
   Match main by `f.name == "main"` instead (name field is populated). Dropped
   `main_id`.
3. **`52a368001a21`** `eval_block`: HirBlock desugars `value: HirExpr?` to
   `has: bool` + `value: HirExpr`. Lowering emitted `has=true, value=nil`, so
   `block.value.?`(=`has`) was true and `eval_expr(nil)` trapped on `.kind`.
   Guarded the unwrapped expr against nil.
4. **`b2f181a7ad88`** + **`fdbf758444af`** `hir_lowering/expressions.spl
   lower_hir_block`: the trailing-value extraction `match last.kind: case
   Expr(expr): Some(expr)` then `if val v = value:` produced the nil value.
   Typed-bound `val last: HirStmt` and removed the intermediate `Option<HirExpr>`
   + `if val v = value` Some-unwrap (a documented seed miscompile) in favor of a
   plain `has` bool + direct `HirExpr` assignment.
5. **`0f11fbe7506b`** `mono/monomorphize_integration.spl scan_expr`: with the
   trailing value now populated, the monomorphization pass (run inside
   `interpret_file`'s `compile()` before interpretation) walked it and trapped on
   a nil/garbage sub-node. Guard: `if expr == nil: return`.

### The wall (root cause, NOT yet fixed)
After fix #4/#5, `eval_block`'s `block.value` is **non-nil but a garbage pointer**
(`0x1800000007`; real HIR exprs are `0x27xxxxx`). i.e. `case Expr(expr)` on a
typed `last.kind` still binds a **garbage** `expr`, so `-c` runs to `rc=0`
**silently** (no `2`). The seed erases `[HirStmt]` elements and `HirStmtKind` to
ANY and **mis-extracts the enum payload** (`case Expr(expr)`) — reading the
Expr variant's HirExpr from the wrong offset. **The typed-binding idiom (proven
on the minimal struct-field repro in iteration 9) does NOT fix enum-payload
extraction**, and no `.spl`-level annotation observed here recovers the real
expr. Multi-statement `-c` bodies (`print(1)\nprint(2)`) SIGSEGV (rc=139) in the
`exec_stmt` path — a parallel landmine.

### Recommendation
Reaching `2` requires a **seed (Rust) fix** to the ANY type erasure — either a
typed `HirType::Dict`/array element type threaded through, or making enum-payload
and field resolution refuse ambiguous ANY receivers instead of guessing an
offset. The pure-Simple workarounds advanced the crash 6 stages but cannot
un-garbage an ANY-mis-extracted enum payload. The `SIMPLE_UNSTUB_HIR` default
stays the empty-HIR stub (untouched); default `-c`/lint/`--version` remain
healthy (verified rc=0, no regression). Binaries: `scratchpad/stage4_fix15..19`.

### Iteration 10 addendum — the wall is enum-payload match, not array ANY (commit fdbf/`stage4_fix20`)
Restructured `lower_hir_block` to capture the trailing expr in-loop from the
FRESH `lower_hir_stmt` return value (`lowered.kind`) instead of re-indexing the
`stmts` array. Result: **identical** garbage `block.value = 0x1800000007`
(masked `0x1800000000`, unmapped). So the mis-extraction is in the
`case Expr(expr)` enum-payload match on an ANY-erased `HirStmtKind` value — it
reproduces even off a non-array, freshly-typed function return. Conclusion: no
`.spl`-level restructuring recovers the payload; the seed must stop erasing
enum/variant types to ANY (or refuse ambiguous payload offsets). Stops here for
iteration 10.

---

## Iteration 11 (2026-07-02) — TWO handoff misattributions corrected; real root is ANY method/field dispatch, not enum-payload extraction

No `-c`→`2`. But two load-bearing claims from iterations 9/10 were **disproven**
by primary evidence, which redirects iteration 12 away from a dead end.

### Correction 1: enum-payload extraction is NOT layout-misrouted
`src/compiler_rust/.../codegen/instr/pattern.rs` `compile_pattern_bind` (line
~104) emits `rt_enum_payload` **uniformly** — it never branches on scrutinee
static type. So "when scrutinee is ANY, pattern compilation picks a wrong
static-layout extraction strategy" (the pinned iteration-11 premise) is **false**.
`rt_enum_discriminant`/`rt_enum_payload` are always used. Any garbage payload is
therefore produced **upstream** (the value fed to `rt_enum_new`/read from a field
was already garbage), not by the match extraction.

### Correction 2: `lower_hir_block` is NOT on the `-c` path
`SIMPLE_UNSTUB_HIR=1 SIMPLE_BOOTSTRAP=1 <stage4> -c "print(1+1)"` prints **no**
`[hir-lower]` (the boot-branch eprints at `hir_lowering/expressions.spl:534`
never fire), and `run hello.spl` under the same env prints only `[frontend]
parsed` — never `[hir-lower]`. So iteration-10's fixes #3/#4 and "the wall"
(`lowered.kind` garbage in `lower_hir_block`) target a function the `-c` path
**does not execute**. Adding `val lowered: HirStmt = ...` there (built as
`stage4_fix21`, full trace) changed **nothing** (`-c` still silent; **0**
`SIMPLE_TRACE_FIELD_GET` hits for `kind` in `expressions.spl`). Reverted — tree
clean.

### The actual `-c` path and the real root cause (documented in-code)
`-c` runs: driver single-file lowering (`src/compiler/80.driver/driver.spl:465-477`,
gated `SIMPLE_UNSTUB_HIR=1`) → `lowering.lower_module` → `lower_function` →
`SymbolTable.lookup` (`src/compiler/20.hir/hir_types.spl:264`) → `scope.symbols.get(name)`
(line 276, a `Dict.get` on an ANY-erased Dict). The driver comment (lines 454-464)
and the `get_symbol` rename comment (`hir_types.spl:305-313`) both record the
mechanism: **method dispatch on an ANY/Dict receiver resolves `.get(text)` by
name+arity across ALL structs and can bind a user-defined `get(text)` method
instead of builtin `Dict.get`.** The primary collider (`SymbolTable.get(id:
SymbolId?)`) was already renamed to `get_symbol`, but `get(module_name: text)`
(`70.backend/linker/smf_getter.spl:199`) and `get(path: text)`
(`99.loader/loader/smf_cache.spl:269`) still match `.get(text)` and can be
mis-dispatched. This is the **same ANY-erasure class as iterations 8/9** (Dict→ANY,
`.values()`/`.get()`→ANY) but at **method dispatch**, and it has the twin `.spl`
bind that neither workaround is clean: `.get()` risks the user-method collision;
`.contains()`+`[]` re-fetch hits the interpreter's "silently yields nil" Dict
defect (comment at `hir_types.spl:270-275`).

### Reproducers status
- `rep9.spl` (real `Expr`/`ExprKind`/`StmtKind`): **no longer reproduces** — prints
  `made se / extracted / OK NO CRASH`, rc=0 (Layer-3 fix cleared it). It is a
  **stale gate**; do not treat its passing as meaningful.
- Hand-made `scratchpad/enumrepro.spl` (inferred method return) and
  `enumtyped.spl` (explicit `val x: T =`), both with a larger `kind`-field decoy:
  **both extract `PAYLOAD_OK`**. So neither method-return ANY-erasure NOR the
  decoy triggers it for hand-made types — the bug needs the full self-host context
  (cross-module `get(text)` colliders + the real Dict-typed symbol tables).

### DECISIVE ROOT CAUSE (minimal 1.4s repro) — `Dict.get()` drops the `Option` wrapper
The `get`-name collision above is a red herring: the control `scratchpad/getnocollide.spl`
(NO user `get` method anywhere) **still fails**. The true, minimally-isolated bug:

```
scratchpad/getval2.spl (seed native-build, 1.4s):
  var d: Dict<text,i64> = {}; d["hello"] = 42
  d["hello"]  == 42  -> "INDEX_OK"      (index path: correct)
  match d.get("hello"): case Some(v): v == 42  -> "GET_WRONG"  (BUG)
```

`d[key]` (index) returns 42 correctly; `d.get(key)` matched as `Some(v)` yields the
**wrong** `v`. Mechanism: `Dict<K,V>` erases to `TypeId::ANY` (type_resolver.rs:426),
so `.get()` lowers via the ANY-method path to the raw runtime builtin
`rt_dict_get` — **`int64_t rt_dict_get(int64_t dict, int64_t key)` (runtime_native.c:2154)
returns the bare stored value, NOT a tagged `Option`.** No `Some`/`None` wrapping is
synthesized, but the language types `.get()` as `Option<V>` and user code does
`match r: case Some(v)`. So the match reads a raw value as if it were an
`rt_enum_new(Some, payload)` object → wrong/garbage payload. (Same family as the
iteration-7 note "`.get()`→`Some(payload)`→field-access corrupts"; index `d[k]` works
because it returns the raw value directly with no Option contract.)

Why this is THE `-c` blocker: stage4's interpreter backend (`interpreter.spl` and
`interpreter_calls.spl`), compiled to native, resolves symbols/functions via
`Dict.get(...)`+`match Some/None` throughout. With `.get()` returning a bare value
instead of `Option`, those matches silently misfire → `main` body/print never runs →
silent `-c`. This also explains driver.spl's SymbolTable.lookup fragility.

### Recommendation for iteration 12 (fix the seed)
Make the ANY/Dict `.get()` lowering honor the `Option<V>` contract. Options:
1. **HIR/codegen**: when lowering a `.get(k)` method call on an ANY/Dict receiver,
   emit `if rt_dict_contains(d,k): Some(rt_dict_get(d,k)) else: None` (real
   `rt_enum_new` Some/None), instead of a bare `rt_dict_get`. Locate the ANY
   container-method lowering (`hir/lower/expr/mod.rs` `is_any` block maps
   `"get"|"remove" => TypeId::ANY`; the call target/codegen is in
   `codegen/instr/calls.rs` / `runtime_sffi.rs`). Mirror how the stdlib
   concretely-typed `Dict.get` wraps.
2. Or add a runtime `rt_dict_get_opt` returning a tagged Option and route `.get()`
   to it. Watch the payload boxing: index unboxes ints; the Some payload must use
   the same box/unbox convention so `v == 42` holds.

**Fast gate (all ~1.4s seed native-build, self-contained):**
`scratchpad/getval2.spl` must print `INDEX_OK` + `GET_OK` (currently `GET_WRONG`).
Then rebuild stage4 (fast path) and test `SIMPLE_UNSTUB_HIR=1 <stage4> -c "print(1+1)"`.
`stage4_fix20`/`stage4_fix21` are equivalent for `-c` (both silent; the iteration-10
`lower_hir_block` annotation was reverted — that function is not on the `-c` path).

## Iteration 12 (2026-07-02) — iteration-11 "Dict.get drops Option" root cause DISPROVEN; real `-c`/run blocker is a SEGV in `SymbolTable.lookup` (stale binary) via bare-`get` collision

**The iteration-11 fix direction (wrap `Dict.get()` in `Option`) is a misattribution
and would be actively harmful. Do NOT implement it.** Primary evidence:

- `scratchpad/getval3.spl` (seed native-build, the *nil-check* idiom the real `-c`
  path uses — `val v = d.get("hello"); if v == 42` / `if miss == nil`) prints
  **GETNIL_OK** + **MISS_NIL_OK**. So the erased/builtin `Dict.get()` **correctly
  returns the bare value with bare `nil` on miss.** The bare path works.
- The actual `-c` symbol lookup — `src/compiler/20.hir/hir_types.spl:274`
  `SymbolTable.lookup` — already uses this working idiom:
  `val found = scope.symbols.get(name); if found != nil: return found`. It expects
  `.get()` to return a **bare** value, not `Option`. Wrapping `.get()` in `Option`
  would make `found` a heap `Some/None` enum that is never `== nil`, so `lookup`
  returns a garbage enum object as a `SymbolId` → breaks the very path it was
  meant to fix.
- Blast radius of an unconditional wrap: **226** bare-assign `.get()` sites
  (`val x = recv.get(k)`) across src/{compiler,lib,app} vs only **2** `match
  recv.get(...)` sites — and those 2 are in `src/app/interpreter/expr/__init__.spl`
  on `RuntimeValue.Dict(d)` (a user/stdlib Dict whose `.get()` is a *real*
  Option-returning method), NOT the erased builtin Dict and NOT the `-c` path.
- The SEED's own Rust interpreter *also* prints `GET_WRONG` for `getval2.spl`
  (`$SEED run getval2.spl`), confirming `.get()` is bare-returning by design in
  every backend. `getval2.spl`'s `match r: case Some(v)` is simply mismatched
  usage for a builtin Dict; its `GET_WRONG` is arguably correct behavior. **The
  getval2 gate itself is invalid — retire it.**

### The real blocker (fresh gdb evidence on `run`)
`SIMPLE_UNSTUB_HIR` is irrelevant to the symptom. On the stale `scratchpad/stage4_unstub`
(Jul 2 09:04): `-c "print(1+1)"` is silent (rc 0, no output); `run hello.spl` prints
`[frontend] parsed` then **SIGSEGV**. gdb backtrace (fork-aware, repo root):

```
#0 hir__hir_types__SymbolTable_dot_get      <- SEGV (rip +825)
#1 hir__hir_types__SymbolTable_dot_lookup
#2 ...HirLowering.lower_function
#3 ...HirLowering.lower_module
#4 driver.CompilerDriver.lower_and_check_impl
#5 driver.CompilerDriver.compile
```

`scope.symbols.get(name)` (Dict.get, **text** key) mis-dispatched to the
user-defined `SymbolTable.get(id: SymbolId?)` — the exact bare-`get` name
collision documented at `hir_types.spl:305-313`. This binary is **stale**: it
predates the `get`→`get_symbol` rename and/or the `bare_builtin_collection` guard
(`closures_structs.rs:329-347`, bug #62). Current source has ONLY
`SymbolTable.get_symbol` (no colliding `get`), and the guard routes bare
`.get(1-arg)` on an erased receiver to the builtin `rt_index_get` *before* any
user-method name resolution — so a fresh stage4 build should not hit this SEGV.

### Iteration 13 direction
1. Do NOT touch `Dict.get()` Option lowering. Retire the getval2 gate; keep getval3
   (nil-check) as the correct builtin-Dict-get gate.
2. Rebuild stage4 from CURRENT source (no seed edit needed — seed already has the
   guard) and re-observe `-c` / `run hello.spl`. If the `SymbolTable.get` SEGV is
   gone, find the *next* layer with gdb on the fresh binary. If `-c` is still
   silent, trace whether the print statement reaches codegen/exec at all
   (frontend parses, but does lower_module complete and does the interpreter/exec
   run `main`?).

### Iteration 12 addendum — fresh build clears the SEGV; blocker advanced to phase5 `interpret_pipeline`
Built `scratchpad/stage4_fix22` from CURRENT source (no seed edit; ~142s,
3 compiled/985 cached). Results:
- `run hello.spl` **no longer SEGVs** (the stale-binary `SymbolTable.get`
  collision is gone in current source). But it still prints nothing and `-c
  "print(1+1)"` still emits no `2` (both rc 0).
- `SIMPLE_COMPILER_TRACE=1 stage4_fix22 run hello.spl` shows the pipeline
  completing phases 1-4 (`load_sources`, `parse`, `hir_typecheck`,
  `monomorphize` all `:done`) and reaching **`phase5:mode_dispatch:start`**,
  then exiting rc 0 with no execution.
- Phase 5 `CompileMode.Interpret` → `self.interpret()` → `interpret_pipeline()`
  (`src/compiler/80.driver/driver.spl:621-651`). The loop does
  `val hir_module = self.ctx.hir_modules[name]; if hir_module == nil: continue`
  keyed on `name = source.module_name`. If that lookup misses, EVERY module is
  skipped → `has_result` stays false → returns `Success(Unit)` silently, `main`
  never runs → no print. **This is the live `-c`/run blocker.**
- Prime suspect: `driver.spl:595` `self.ctx.hir_modules = mono_modules`
  (also `:436` for the bootstrap effect pass) REPLACES `hir_modules` with the
  monomorphization output. If `run_monomorphization` re-keys or drops the
  entry-module key, `hir_modules[source.module_name]` misses in
  `interpret_pipeline`. NOTE this is a Dict keyed by module-name text — but the
  `.get()`/index path itself is proven-good (getval3), so the fault is a
  **key mismatch / missing entry**, not a Dict-runtime defect.

### Iteration 13 concrete next step
Add a temporary trace in `interpret_pipeline` (driver.spl:~638) printing
`sources.len()`, each `name`, and whether `hir_modules[name] == nil` plus
`hir_modules.keys()`; rebuild stage4 and run `run hello.spl`. If the entry
module is absent/renamed after mono, fix the keying at `driver.spl:595`
(`run_monomorphization` key contract) so the interpret loop finds it. Do NOT
pursue Dict.get Option wrapping (disproven above).
