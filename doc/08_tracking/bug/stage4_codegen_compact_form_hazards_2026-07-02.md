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

### Iteration 12 FINAL — mono-rekey DISPROVEN; decisive root: interpreter receives an EMPTY HIR module (functions=0, symbols=0)
Instrumented `interpret_pipeline` + `InterpreterBackendImpl.process_module`
(traces since reverted; tree clean) and rebuilt stage4. On `run hello.spl`:
- `interpret_pipeline`: `idx=0 name=...hello hir_nil=false nkeys=1` — the HIR
  module **is found** (mono-rekey hypothesis DISPROVEN).
- `process_module`: `[interp-hasmain] has_main=false nfuncs=0`, and **zero**
  `[interp-sym]` lines emitted. So `module.functions.len()==0` AND
  `module.symbols.symbols.values()` iterates **zero** elements. The module
  object exists but its **functions and symbols are empty** → no `main` → silent
  `BackendResult.Unit`, `main` never called, no print. **This is THE `-c`/run
  blocker.**
- `-c "print(1+1)"` takes a *different* path: exits **rc=1** without reaching
  `process_module` (no interp traces). Investigate `-c` handling separately from
  `run`.

Root question for iteration 13: **why is `module.functions` empty when it
reaches the interpreter?** `module.functions` is `Dict<SymbolId, HirFunction>`
and `module.symbols.symbols` is `Dict<i64, Symbol>` — both **struct/int-keyed
Dicts** that `interpreter.spl:47-78`'s own comments flag as ANY-erasure hazards
(".values() yields ANY-typed elements", "struct-keyed Dict fails to find an
entry that is present"). Two candidates, distinguish first:
  (a) The Dict is genuinely empty — HIR lowering never inserted `main` into
      `module.functions` (e.g. single-file/synthetic-main lowering populates a
      different field, or lower_function's output isn't stored back on the
      module). Check where `module.functions[...]=` / symbol insertion happens in
      `hir_lowering` for the single-file `run` path.
  (b) The Dict is populated but `.len()`/`.values()` on a struct/int-keyed
      ANY-erased Dict misreport as empty in seed cranelift codegen (connects to
      the rep9 / `Dict<SymbolId{id:i64},V>` struct-keyed repros earlier in this
      doc). Add a trace that inserts a known key then reads `.len()` on the SAME
      dict instance the interpreter receives.
Do NOT touch `Dict.get` Option lowering (disproven, iter 12). getval3 (nil-check)
is the correct builtin-Dict-get gate; getval2 (Option-match) is retired.

---

## Iteration 13 (2026-07-03) — TWO methodology traps corrected; probe mechanism + test-file were the real obstacles

Ran the iteration-12 discriminating experiment (probe `lower_module` insert vs
`process_module` consumer). Two obstacles invalidated the first passes; both are
now documented so iteration 14 doesn't repeat them:

### Trap A — `rt_file_append_text` file-append probes DO NOT WRITE in this runtime
Every file-append probe (`rt_file_append_text("/tmp/lm_probe.log", ...)`) produced
an EMPTY log across builds fix23/fix24, making it look like the instrumented code
paths never executed. Direct test (`scratchpad probetest2.spl`): `val ok =
rt_file_append_text(path, s); print(ok)` prints **`false`** under BOTH the seed
(`$SEED run`) and compiled stage4. The runtime `rt_file_append_text`
(runtime_native.c:2441) delegates to `rt_file_append`, which returns 0/false here
(the `/tmp` append is not landing). **Retire file-append probes for stage4
instrumentation.** Use `eprint` (process_ops, buffered but flushes on clean exit)
or `rt_eprintln_str(s, s.len())` (unbuffered stderr) — both proven to work.
Iteration 13's fix25 re-instruments with eprint/rt_eprintln_str.

### Trap B — the `hello.spl` test file was being deleted mid-run by a parallel jj reconcile
`hello.spl` (untracked, repo root) was silently removed between runs by a
parallel-session `jj` working-copy snapshot/reconcile → the compiler read
`content_len 0` → `[load_sources] total 0` → `interpret_pipeline` returned
`CompileResult.RuntimeError("No source file specified for interpret mode")`
(driver.spl:631) with garbled spaced-out error text. This is NOT a compiler bug;
it masqueraded as one. **Always place the `-c`/run test file in `/tmp`
(e.g. `/tmp/hello.spl`), never repo root**, so parallel VCS ops can't sweep it.

### Confirmed live symptom (fix24, `/tmp/hello.spl` present, content read OK)
- `SIMPLE_UNSTUB_HIR=1 stage4 run /tmp/hello.spl`: `[frontend] parsed` (x2),
  reaches `phase5:mode_dispatch:start`, rc=0, silent (no `2`). Matches iter 12.
- Decisive new datapoint: `stage4 run /tmp/probetest.spl` where probetest's `main`
  literally does `print(99)` — prints **NOTHING** (no `99`), rc=0. So the compiled
  interpreter backend does **not execute `main` for an ordinary user file** via
  the default `run` path either (default = empty-HIR stub, functions={} →
  process_module finds no main → silent Unit). The seed runs the same file and
  prints `99` correctly.

### Iteration 13 instrumentation (fix25) — eprint probes at the branch points
Placed eprint/rt_eprintln_str probes at: driver `lower_and_check_impl` entry
(`sources.len`/`modules.len`), the `sources<=0` vs sources-loop branch, the
`is_bootstrap_entry` / `unstub_reparse` / `STUB` branch selector; `lower_module`
ENTER + else-branch `fnkeys.len` + per-insert `functions.len` + else-done; and
`process_module` entry. This will finally show, with a working probe mechanism,
which branch of the discriminating experiment fires:
  - `[DRV] branch=STUB` → UNSTUB gate not taken (env not seen / content=="" /
    low_memory) → functions never lowered → interpreter gets empty module.
  - `[DRV] branch=unstub_reparse` + `[LM] else-branch fnkeys.len=0` → the
    RE-PARSED module has no functions (parse_full_frontend drops `main`).
  - `[LM] after-insert functions.len>=1` but `[PM] entry` shows 0 → module copied
    /rebuilt between lowering and interpret, losing dict contents.
  - `[PM] entry` never prints → interpreter backend not invoked at all.
Probes are eprint-only (tree has no rt_file_append probes). Remove before final
commit. Binaries: scratchpad/stage4_fix23..25.

### Iteration 13 DECISIVE ROOT CAUSE (fix26, full eprint chain) — BackendPort.run_fn closure never dispatches to InterpreterBackendImpl.process_module
With working eprint probes the ENTIRE `run /tmp/hello.spl` chain is now visible.
Every producer stage is CORRECT — the "empty module" theory (iter 12 FINAL) is
DISPROVEN:
```
[DRV] lac-entry sources.len=1 modules.len=1
[DRV] lac-loop name=.tmp.hello content_len=28
[DRV] branch=unstub_reparse
[LM] ENTER lower_module name=/tmp/hello.spl
[LM] else-branch fnkeys.len=1          <- parser module has 1 fn (main)
[LM] loop name=main
[LM] after-insert functions.len=1      <- struct-keyed Dict INSERT works, len=1
[LM] else-done functions.len=1
[DISP] Interpret case reached
[IP] interpret_pipeline sources.len=1 backend=interpreter
[IP] idx=0 name=.tmp.hello hir_nil=false funcs=1   <- module reaches interpret WITH funcs=1
[IP] calling run_fn
      <-- [PM] entry NEVER printed; rc=0, silent
```
**Which branch of the discriminating experiment fired: NEITHER producer-empty NOR
consumer-len-0.** `module.functions.len()==1` at the producer (lower_module) AND
at the consumer boundary (interpret_pipeline, immediately before dispatch). Mono
does NOT empty it. The blocker is one level deeper: **`backend_port.run_fn(hir_module)`
is invoked but `InterpreterBackendImpl.process_module`'s body never executes**
(`[PM] entry` at the very first line of process_module never fires), returning a
silent default so `main` is never called and nothing prints.

`run_fn` is `run_fn: fn(m): interp_impl.process_module(m)` (driver_types.spl:56),
a closure stored in the `BackendPort.run_fn` field that captures `interp_impl` and
calls `.process_module(m)` on it. The empirical fact: `backend_port.run_fn(...)`
is invoked (`[IP] calling run_fn` prints) but the FIRST line of
`InterpreterBackendImpl.process_module` (`_probe_pm("[PM] entry...")`) never
prints, and the pipeline returns a silent Unit.

**Mechanism NOT yet the simple closure pattern.** Minimal seed repros DISPROVE the
first hypothesis: `scratchpad/clorepro.spl` (closure captures struct instance,
calls its method) AND `clorepro2.spl` (that closure stored in a `Port` struct
field `run_fn: fn(i64)->i64`, invoked via `p.run_fn(5)`) BOTH enter the method
(`INSIDE_METHOD` prints, `RESULT_OK`). So closure-in-field + captured-instance +
method-call works in isolation. The distinguishing factor in the real case is one
of: `process_module` returns `Result<BackendResult, BackendError>` (enum return),
takes a large `HirModule` struct by value, uses `?` internally, or the
`BackendPort` is built inside a `match options.mode` arm. Iteration 14 must
narrow the repro by adding these one at a time (Result return type first — most
likely), then fix. Until then the confirmed blocker is: **run_fn(module funcs=1)
does not reach process_module's body → silent no-op**.

### Iteration 14 direction (the real fix)
Confirm + fix the closure-captured method dispatch. Two verification probes:
(1) put an eprint as the FIRST expr inside the `fn(m): ...` closure body in
driver_types.spl:56 — if it prints but `[PM] entry` doesn't, the closure runs but
the `interp_impl.process_module(m)` call is miscompiled. (2) Minimal seed repro:
`struct S; impl S: fn hi(x:i64)->i64: <eprint>; x`; `val s=S(); val f=fn(m):
s.hi(m); f(5)` under `seed native-build` — check the impl body runs.
Candidate fixes, cheapest first:
  - **`.spl` workaround**: bypass the closure — have `interpret_pipeline` call the
    concrete backend directly (e.g. store the `InterpreterBackendImpl` on the ctx
    and call `impl.process_module(module)` inline) instead of through the
    `BackendPort.run_fn` closure. If the direct call enters process_module, the
    bug is confined to closure-captured method dispatch and this is a clean fix.
  - **seed fix** if the direct call also fails: closure/method-dispatch codegen in
    `src/compiler_rust/.../codegen/instr/{calls.rs,closure*.rs}` — the captured
    `self`/receiver is likely lost or the method target resolved to a stub.
Gate: `SIMPLE_UNSTUB_HIR=1 <stage4> run /tmp/hello.spl` must print `2`; then `-c
"print(1+1)"`. Keep the `/tmp/hello.spl` rule (Trap B) and eprint probes (Trap A).
Binaries: scratchpad/stage4_fix26 (full-chain probe build).

## Iteration 14 (2026-07-03) — the blocker is NOT the closure; `process_module`'s body is never entered by ANY caller

### DISPROVEN: closure-captured method dispatch is the cause
Iteration 13 concluded `backend_port.run_fn` (the closure) was the miscompiled
hop. Iteration 14 tested this directly:
- **fix27**: `interpret_pipeline` (driver.spl) was changed to bypass the closure
  entirely — construct a fresh `InterpreterBackendImpl` and call
  `interp.process_module(hir_module)` DIRECTLY (no closure). Added an eprint
  `[PM] entry` probe as process_module's FIRST line.
  Result: `run /tmp/hello.spl` STILL silent, `[PM] entry` STILL never printed.
  → the direct call ALSO fails to enter the body. Closure is exonerated.
- **fix28**: added eprint probes at `interpret_pipeline` ENTRY, before the call,
  and in the Ok arm. Decisive trace:
  ```
  [IP] interpret_pipeline ENTRY
  [IP] before process_module call
  [IP] process_module OK        <- the call RETURNED Ok(...)
        <-- [PM] entry NEVER printed, hello-world-42 NEVER printed
  ```
  So `interp.process_module(hir_module)` **returns `Ok(...)` without executing
  process_module's first statement.** The call is dispatched to something that
  returns `Ok(default)` immediately — a stub or the wrong sibling method — NOT
  the real interpreter body.
- **fix29/fix30**: added a uniquely-named wrapper `interpret_hir_module` on
  InterpreterBackendImpl that just does `self.process_module(module)`, and called
  THAT from the driver (unique name → no cross-struct `process_module` collision
  at the driver→wrapper hop). fix30 probes: `[WRAP] interpret_hir_module ENTRY`
  + `[PM] entry` (both switched to proven-working `eprint`, not rt_eprintln_str).
  [RESULT PENDING at write time — see run below.]

### Refined root-cause hypothesis (iteration 14)
InterpreterBackendImpl defines EIGHT `process_*` methods all with signature
`(HirX) -> Result<BackendResult, BackendError>` (interpreter.spl:42-133); SEVEN
are one-line `Ok(BackendResult.Unit)` stubs (process_function/class/struct/enum/
trait/impl). The seed appears to dispatch `interp.process_module(HirModule)` to
one of these `Ok(BackendResult.Unit)` sibling stubs instead of the real body —
explaining EXACTLY why the call returns `Ok(Unit)` with no side effects. This is
the method-dispatch analogue of the documented Dict→ANY "most-fields-wins" family:
the receiver/return is ANY-erased (BackendResult/HirModule carry Dict fields) so
the static method-target resolution picks the wrong same-signature sibling.

### Seed repro status — NOT reproducible in isolation (7 variants tried)
All PASS (correct dispatch) via 1.4s `seed native-build`:
- clorepro3: closure-in-field + Result<enum> return + big-struct(4-field) by-value
- clorepro4: + match-arm construction + class-field indirection (`self.ctx.backend`)
- clorepro5: + two DIFFERENT impl types sharing one `fn` field type
- clorepro6: + `?` operator inside the method body
- clorepro7: 4 structs each with identical `process_module(i64)->Result<enum>`
- crepo (multi-file): duplicate method names across 3 modules, cross-module call
- sib: ONE struct with 7 sibling `process_*` methods (6 `Ok(Unit)` stubs) + call
The common miss: all use small concrete param structs. The REAL trigger requires
the genuine `HirModule` (large struct whose `functions`/`symbols` are `Dict<K,V>`
erased to ANY by the seed). An isolated repro would need the full compiler HIR
tree as a dep, exceeding the fast gate. TRIGGER = same-signature `process_*`
sibling methods on one impl + an ANY-erased `HirModule` by-value arg.

### Fix applied (fix30 CONFIRMS the dispatch fix + reveals Trap C)
- driver.spl `interpret_pipeline`: bypass `backend_port.run_fn` closure; construct
  `InterpreterBackendImpl` and call the uniquely-named `interpret_hir_module`.
- interpreter.spl: added `interpret_hir_module` (unique name) → `self.process_module`.

### Trap C — the `rt_eprintln_str(s.ptr(), s.len())` probe ITSELF silently fails
fix27/28/29 used `rt_eprintln_str(_probe.ptr(), _probe.len())` as the `[PM] entry`
probe and it NEVER printed — which falsely looked like process_module's body was
never entered. fix30 switched the SAME probe location to `eprint(...)` and it
PRINTS. So the extern `rt_eprintln_str` call (or `.ptr()`/`.len()` arg passing to
it) is miscompiled/no-op in stage4 — a third silent-probe trap alongside Trap A
(rt_file_append_text) and buffered-stdout. **For stage4 instrumentation use ONLY
`eprint(...)`.** With eprint, fix30 shows the full chain runs:
```
[IP] interpret_pipeline ENTRY
[IP] before process_module call
[WRAP] interpret_hir_module ENTRY   <- unique-named wrapper dispatches correctly
[PM] entry process_module            <- real process_module body RUNS
[IP] process_module OK
```
So the uniquely-named-method fix WORKS for dispatch. Whether the closure was ever
the problem is now moot — the direct concrete call + unique name reaches the body.

### REMAINING (fix30): `[PM] entry` runs but `hello-world-42` still not printed
process_module executes and returns Ok, but `main`'s `print` produces no output.
Next: probe `has_main`, the `f.name=="main"` loop, and the call_hir_function hop
(fix31) to see whether main is found+invoked, or invoked-but-print-is-a-no-op.

### fix31: `main` IS found and called — gap is INSIDE main's body / print path
fix31 probes in process_module's main-dispatch:
```
[PM] entry process_module
[PM] has_main=true
[PM] loop fn.name=main
[PM] calling main via call_hir_function
[PM] main returned          <- call_hir_function(main) completed OK
```
So dispatch is fully fixed: main is located and invoked. But `hello-world-42`
STILL not printed. The gap moved one level deeper: inside
`call_hir_function(main)` → `eval_block(main.body)` → the `print(...)` statement.
Either main.body.stmts is empty (body not lowered) or the print builtin path
(interpreter_calls.spl try_call_builtin BuiltinTag.Print) no-ops. fix32 adds
eprint probes at Print-builtin entry + the text `case _` to discriminate.

### fix32: the `print` builtin is NEVER invoked — main's trailing print not evaluated
fix32 trace shows `[PM] main returned` but NO `[BUILTIN] Print reached`. So
`call_hir_function(main)` runs but the `print("hello-world-42")` inside main's
body is never executed. ROOT CAUSE FOUND in HIR lowering + interpreter mismatch:
- `lower_block` (20.hir/hir_lowering/expressions.spl:577-599): for a body whose
  LAST statement is an expression (main = single `print(...)` stmt), that stmt is
  extracted as the block's TRAILING VALUE, NOT pushed to `block.stmts`. So
  `main.body.stmts` is EMPTY and `main.body` = {has: true, value: <print call>}.
- `HirBlock` (20.hir/hir_definitions.spl:677) is DESUGARED: `value: HirExpr` is a
  PLAIN field (not Option) gated by a separate `has: bool` flag.
- BUT the interpreter `eval_block` (interpreter.spl:362) reads it as an Option:
  `if block.value.?: ... block.value.unwrap()` and NEVER checks `block.has`.
  On the ANY-erased single-file main HIR this `.?`/`.unwrap()` on a non-Option
  field mis-evaluates → the trailing `print` expr is never eval'd → silent.
FIX: `eval_block` must gate on `block.has` and use `block.value` directly (no
`.?`/`.unwrap()` — value is a plain HirExpr, not Option). fix33 confirms via an
`[EB] stmts.len / has_value` probe, then apply the has-gated fix.

### fix33 CONFIRMS the root cause
fix33 trace (with the OLD `block.value.?` probe): `[EB] eval_block stmts.len=0
has_value=true` then `[PM] main returned` — and NO `[BUILTIN]`. So:
- `stmts.len=0`: the `print` was extracted by lower_block as the trailing VALUE,
  not a statement (as predicted).
- `has_value=true`: `block.value.?` (Option-style non-nil check) returned true.
- Yet `block.value.unwrap()` → `eval_expr` on the unwrapped value did NOT reach
  the print builtin. The `.unwrap()` on the DESUGARED plain-`HirExpr` field (which
  is NOT an Option) is the miscompile: on the ANY-erased single-file main it
  yields a value that eval_expr silently no-ops on.

### THE FIX (fix34): eval_block gates on `block.has`, evals `block.value` directly
interpreter.spl eval_block changed from:
  `if block.value.?: ... self.eval_expr(block.value.unwrap(), ctx)`
to:
  `if block.has and block.value != nil: self.eval_expr(block.value, ctx)`
This matches the desugared HirBlock contract (has: bool gate + plain HirExpr
value). No `.?`/`.unwrap()` Option semantics on a non-Option field.

Note: `src/compiler/{backend,hir,frontend}` are SYMLINKS to `70.backend`/`20.hir`/
`10.frontend` (same inode) — editing the numbered tree is canonical, no mirror
copy to sync.

### fix34 PARTIAL: the has-gated fix reaches eval_expr but Call still not dispatched
fix34 trace: `[EB] eval_block stmts.len=0 has=true` then `[EB] evaluating trailing
value` — so the has-gate fix works and `eval_expr(block.value)` is now called.
BUT still no `[BUILTIN] Print` and no `hello-world`. So `eval_expr` on the
trailing print-Call expr does NOT reach the print builtin. Two candidates:
(a) `block.value.kind` mis-matches (ANY-erased kind) so eval_expr falls to its
`case _:` not_implemented (but no "Interpret error" surfaced, so maybe it matched
a silent case), or (b) the `Call` case IS matched but call_function's builtin
routing no-ops. fix35 probes eval_expr `Call` case entry + the catch-all `case _:`
to discriminate. NOTE: the eval_block has-gate fix is CORRECT and should stay
regardless — it's a real bug (Option semantics on a plain desugared field); the
remaining gap is a SEPARATE layer (eval_expr/Call dispatch on the ANY-erased
trailing expr).

### fix35: eval_expr(block.value) matches NEITHER Call NOR catch-all — ANY-erased kind
fix35 trace ends at `[EB] evaluating trailing value` — then NOTHING. Not the
`[EE] Call case` probe, not the `[EE] catch-all` probe, and NOT `[PM] main
returned`. So `eval_expr(block.value)`'s `match expr.kind` matched an INTERMEDIATE
case (silently) or read a garbage kind and stalled. This is the ANY-erasure
signature: `block.value` reaches `eval_expr(expr: HirExpr)` but `expr.kind` is
read off an ANY-typed receiver → wrong/garbage discriminant.

### fix36 HYPOTHESIS + LIKELY FIX: typed rebind of block.value before matching
The documented cure for ANY-erased field access in this file is to bind the value
to a TYPED local (`val f: HirFunction = ...`) so field indices resolve correctly.
fix36 applies the same: `val bv: HirExpr = block.value` then `match bv.kind` +
`eval_expr(bv)`. If the typed rebind makes the Call case match (probe shows
`trailing kind=Call`) and print fires, THAT is the fix — the trailing value must
be passed through a typed local, not the raw ANY-erased `block.value` field.

### fix36 DECISIVE: `match block.value.kind` produces NO output — the field access TRAPS
fix36 trace: `[EB] evaluating trailing value` then NOTHING — not even the
`trailing kind=OTHER` catch-all of the `match bv.kind` I added. A match that emits
nothing for ANY arm (incl `case _:`) means reading `bv.kind` HARD-TRAPS (silent
abort, rc=0). So `block.value` is a GARBAGE/nil HirExpr and dereferencing its
`.kind` crashes — the "field access on nil receiver" trap (iteration 10 family).
The typed rebind at the INTERPRETER (`val bv: HirExpr = block.value`) did NOT help
because the value was already corrupted upstream.

### TRUE ROOT CAUSE: lower_block stores a garbage trailing value (ANY extraction)
`lower_block` (20.hir/hir_lowering/expressions.spl:579-585): for a body whose last
stmt is an expression, `match lowered.kind: case Expr(expr): block_value_expr =
expr`. The seed erases the `HirStmt` (and the `Expr(expr)` payload) to ANY on the
single-file/synthetic-main HIR, so the extracted `expr` is a garbage/nil HirExpr
pointer that is stored as `block.value`. The interpreter later traps reading its
`.kind`. (This is the exact hazard the pre-existing comment at :562-571 warns about
for the OLD `.stmts`-reindex approach; it recurs for the direct-return approach in
stage4.)

### THE LOWERING FIX (fix37): typed rebind of the extracted expr
expressions.spl lower_block now binds `val lk = lowered.kind` and inside the
`case Expr(expr)` arm binds `val ve: HirExpr = expr` before `block_value_expr =
ve`. This restores the concrete HirExpr struct type so the stored trailing value
is valid (same typed-local ANY-cure idiom used for the `.values()` loops in
interpreter.spl). ALSO changed `val lowered` → `val lowered: HirStmt` (typed).
fix37 verifies whether hello-world-42 now prints.

### Applied fixes summary (iteration 14)
1. driver.spl interpret_pipeline: direct concrete InterpreterBackendImpl call via
   uniquely-named `interpret_hir_module` (bypasses closure + name-collision).
2. interpreter.spl eval_block: gate trailing value on `block.has` + `block.value
   != nil`, eval `block.value` directly (no Option `.?`/`.unwrap()` on the plain
   desugared field).
3. expressions.spl lower_block: typed rebind of extracted trailing expr — REVERTED
   (see fix37 below: it turned the silent no-op into a SIGSEGV, confirming the
   extracted expr is genuinely a bad pointer from the seed, not fixable by a .spl
   typed rebind).

### fix37: lowering typed-rebind makes it a SIGSEGV — the blocker is SEED-LEVEL
With the has-gate (fix #2) + lowering typed-rebind (#3), fix37 gets FURTHER then
crashes: trace reaches `[PM] calling main via call_hir_function` then rc=139
(SIGSEGV) inside `eval_block(main.body)` → `eval_expr(block.value)`. Previously
(garbage-nil) it silently no-op'd (rc=0); the typed rebind changed the bad value
enough to dereference into a segfault. Either way, **`block.value` is a genuinely
bad HirExpr pointer produced by the seed's destructuring of `case Expr(expr)` on
an ANY-erased `HirStmtKind`** at lower_block:581. This is a SEED codegen bug
(ANY-payload enum-variant destructure), NOT fixable in pure Simple. Reverted the
lowering change to avoid the segfault regression.

### CONCLUSION (iteration 14) — 2 sound .spl fixes landed; final blocker is seed
Two real pure-Simple bugs were found and FIXED (they are correct improvements and
should be kept, even though the end-to-end `run`/`-c` still doesn't print due to
the deeper seed bug):
1. Interpreter dispatch: driver now calls a uniquely-named `interpret_hir_module`
   on a concrete InterpreterBackendImpl (bypasses the closure + the same-signature
   `process_module` sibling-method collision that returned Ok(Unit) w/o running).
2. eval_block trailing value: gate on `block.has` + eval `block.value` directly
   (the field is a desugared plain HirExpr, not an Option; the old `.?`/`.unwrap()`
   mis-evaluated it).
REMAINING BLOCKER (for iteration 15): the seed miscompiles destructuring the
`Expr(expr)` payload of an ANY-erased `HirStmtKind` in `lower_block`
(20.hir/hir_lowering/expressions.spl:581), so a function body whose last statement
is an expression (`fn main(): print(...)`) stores a garbage HirExpr as the block's
trailing value. Fix target: the seed enum-variant destructure codegen for ANY-
typed payloads (`src/compiler_rust/.../codegen/instr/` match/destructure), OR a
lowering restructure that keeps the last expr-stmt in `stmts` (evaluated via the
stmts loop) for functions returning Unit instead of extracting a fragile trailing
value. All eprint probes removed; binaries scratchpad/stage4_fix27..38.

## Iteration 17 (2026-07-03) — Trap D found; disc probes calibrated (name-hash tags); bare no-payload patterns are IRREFUTABLE; blocker moved from silent-NilLit to mono scan SEGV on a misrouted HostGpuLane

### Trap D — env-GATED eprint probes are MUTE in hir_lowering modules
`if (hir_*_env_get("SIMPLE_INTERP_TRACE") ?? "") == "1": eprint(...)` never
fires in 20.hir/hir_lowering/* on stage4 even with the env set, while the SAME
idiom works in driver.spl/interpreter.spl. Proven by the LMW sentinel
experiment: an UNGATED eprint + a `hm.name + "+LMW"` suffix both surfaced while
every gated probe stayed silent. **Iteration 16's "lower_module may not run" is
DISPROVEN — lower_module always ran; its probes were mute.** For lowering-side
instrumentation use UNGATED `eprint` only (remove before deploy).
Consequence: iteration-17 probes in expressions.spl / statements.spl /
_Items/module_lowering.spl / _FlatAstBridge/convert_nodes.spl are UNGATED and
still in-tree — they spam stderr on every compile and MUST be removed before
any deploy.

### Disc calibration — rt_enum_discriminant returns variant-NAME-HASH tags
`[FBC] call=823890719 nil=3558872348 int=1201078288` (freshly constructed
ExprKind values). These are NOT garbage: 3558872348 is exactly the tag the
interpreter reads off a genuine HirExprKind.NilLit. Tags are name hashes shared
ACROSS enums (ExprKind.NilLit and HirExprKind.NilLit have the SAME tag). All
prior "garbage disc" readings (823890719 = "Call") were VALID values.

### DECISIVE: bare NO-PAYLOAD patterns compile as IRREFUTABLE BINDINGS
With a valid Call value (tag 823890719) reaching lower_hir_expr's big match,
`[LHE-ARM] NilLit` fired: the bare `case NilLit:` arm (variant name exists in
BOTH ExprKind and HirExprKind) swallowed the Call — every expression lowered to
HirExprKind.NilLit → whole programs ran as silent no-ops (the exact iteration
15/16 symptom `[EE] NilLit arm`, rc=0). FIXED by qualifying: `case
ExprKind.NilLit:` etc. After the fix the pipeline advances past lowering into
monomorphization.

### Fixes landed (all committed, HEAD lineage vsx/1a7)
1. driver.spl: unstub branches call uniquely-named `lower_parser_module_unstub`
   + typed `var lowering: HirLowering` locals (defensive; dispatch was later
   proven fine, harmless to keep).
2. _Items/module_lowering.spl: removed rt_file_append probe (Trap A); added
   `lower_parser_module_unstub` wrapper + ungated [LM] probe.
3. expressions.spl: qualified ALL arms of lower_hir_expr's big match
   (`case ExprKind.*`) and the gpu-lane helpers; direct typed `val
   expr_kind_value: ExprKind = e.kind` instead of `match e: case Expr(k, _)`.
4. statements.spl: direct typed `val stmt_kind_value: StmtKind = s.kind`; typed
   payload rebind + [LST]/[LSTP] probes (rt_enum_payload agrees with pattern
   extraction — both return the same valid value).
5. interpreter.spl: qualified eval_expr arms (HirExprKind.*), exec_stmt
   HirStmtKind.Assign + nested HirExprKind.Var.
6. 40.mono/monomorphize_integration.spl: qualified scan_expr arms
   (HirExprKind.*) + check_generic_call Var.
7. convert_nodes.spl: [FBC]/[FBS] construction-time disc probes (ungated).

### REMAINING BLOCKER (rc=139): print(1+1) is misrouted into HostGpuLane; mono scan SEGVs on its garbage body
Trail: `[LHE] kind_disc=823890719 (Call)` → 2nd `[LHE0]` with disc=2489634455
(believed "Binary", i.e. the 1+1 arg) WITHOUT `[LHE-ARM] Call` ever printing →
lowering completes (funcs=1) → SIGSEGV in MonomorphizationPass.scan_block ←
scan_expr ← scan_stmt (gdb, stage4_it17o). Reading: the big match's Call arm
never runs because `try_lower_host_gpu_lane_expr` INTERCEPTS the Call first:
its qualified patterns now match, but the EXTRACTED payloads (callee/args) are
garbage on stage4 — `name == "host"` passes on a garbage text, `args.len()`
reads 2, the Lambda arm matches garbage, and it returns
Some(HostGpuLane(..., body=garbage HirBlock)). The mono scan then walks that
garbage block → SEGV. KEY INSIGHT for iteration 18: **qualified pattern
payload EXTRACTION from a matched ExprKind is still garbage in expressions.spl**
(while the same extraction works in interpreter.spl on HirExprKind). Next
steps, cheapest first:
  a. Typed-rebind the extracted payloads in try_lower_host_gpu_lane_expr
     (`val callee_t: Expr = callee`) before `.kind` reads — the .kind read on
     the extracted (ANY-ish) Expr is likely the most-fields-wins misread, NOT
     the extraction itself (LST/LSTP showed extraction returns the right box).
  b. If (a) fails: make try_lower_host_gpu_lane_expr bail early unless the
     module actually contains host/gpu lane syntax (text scan), or gate it off
     for the -c/unstub path; it is an optional fast-path.
  c. Then expect the SAME extraction hazard inside the big match's Call arm
     ([LHE-ARM] Call will print, then callee/args handling must be typed-rebound).
  d. eval_expr side is already qualified; verify with the [EE] trail once
     lowering emits a real HirExprKind.Call.
Binaries: scratchpad/stage4_it17{,b..o}; build cmd unchanged (NEVER omit
--target). PROBE CLEANUP (ungated eprints listed above + [FBC]/[FBS]/[LM]/
[LBU]/[LHE*]/[LST*]) is a DEPLOY PRECONDITION.

## Iteration 18 (2026-07-03) — GOAL REACHED: `SIMPLE_UNSTUB_HIR=1 <stage4> -c "print(1+1)"` prints `2` (rc=0); `run hello_it15.spl` prints hello-world-42; `--version` OK

### Root causes found and fixed (chain of SEVEN distinct stage4/seed hazards)
1. **Struct-shadowed variant patterns compile as ALWAYS-TRUE tests.** When a
   variant pattern's name is also a struct/class name ANYWHERE in the program
   (`struct Field` parser_types.spl:232, `struct Block` parser_types_expr.spl:427,
   `struct Expr` parser_types_expr.spl:159), the seed compiles the qualified
   `case ExprKind.Field(...)` TEST via the struct/tuple fallback in
   compiler_rust codegen/instr/pattern.rs (`_ => iconst 1`), while payload
   BINDINGS still extract enum payloads. The Field arm swallowed every Call in
   lower_hir_expr's big match ([LHE-ARMX] Field on a Call disc); the Block arm
   swallowed a NamedVar in mono scan_expr. NOTE: the shadow is GLOBAL — mono
   has no local Field/Block structs. FIX: discriminant PRE-DISPATCH — read
   `rt_enum_discriminant` (= DefaultHasher(variant name) truncated u32:
   hash("Field")=21232742, hash("Block")=1138084884) before the match, handle
   Field/Block in a verified nested match, and REMOVE those arms from the big
   match (expressions.spl lower_hir_expr; monomorphize_integration.spl
   scan_expr; scan_stmt reordered Let/Assign before the shadowed Expr arm).
   Disc constants verified: 823890719=Call, 2489634455=Ident (NOT Binary as
   it17 believed), 1764299124=Binary, 1201078288=IntLit, 465620071=Add,
   2735847868=Error, 1337030607=NamedVar. Hash fn: rust DefaultHasher
   (runtime/src/value/objects.rs hash_variant_discriminant), deterministic.
2. **try_lower_host_gpu_lane_expr misroute** (it17 blocker): typed rebinds of
   extracted payloads (`val callee_t: Expr = callee` etc.) fixed the
   `name == "host"` garbage compare — [LGL] then read name=print correctly.
3. **Partial named struct construction fills POSITIONALLY.** `HirCallArg(name:,
   value:, span:)` omitted the hand-desugared `has_name` field; the seed
   placed `value` in the `name` slot → `arg.value` read the span (disc=-1) in
   BOTH mono scan and interp. FIX: pass ALL fields in declaration order
   (expressions.spl Call/MethodCall arms; declaration_lowering.spl
   lower_function HirFunction ctor gained has_export_attr/
   has_driver_manifest_attr/has_doc_comment).
4. **`.?` on a plain (non-optional) empty array is TRUE** → is_generic_function
   classified `-c main` as generic and dragged the whole mono machinery in
   (mono scan should never have run). FIX: nil-guarded `.len() > 0` in
   is_generic_function/struct/class + typed Dict-value rebinds in
   collect_generics/scan_call_sites.
5. **Same-name same-shape static methods dispatch to the WRONG type** (it14
   class): `Value.int(v)` collided with `SdnValue.int(v)` — eval produced a
   non-Value box so `case Value.Int(l)` never matched. FIX: construct enum
   variants DIRECTLY (`Value.Int(v)` etc.) throughout interpreter.spl /
   interpreter_calls.spl.
6. **Struct payload lost through the Value.Function channel** ([CF] f_nil=true
   even for a freshly constructed, hoisted FunctionValue) + the
   rt_value_int→rt_value_print pointer round-trip SEGVs. FIX: builtin
   fast-path in the interp Call arm dispatches by the callee NamedVar NAME
   (try_call_builtin) before evaluating the callee as a value; Print's scalar
   cases print via pure Simple ("{iv}") instead of rt_value_print.
7. **`int(text)` builtin returns the FIRST character's char code** on stage4
   (int("1")==49, int("12")==49) → print(1+1) printed 98. FIX: manual decimal
   accumulation loop in parser_guarded_int_text (10.frontend/core/parser.spl).

### Also fixed / added
- Ident lowering: unresolved names that are known interpreter builtins are
  defined into the symbol table and lowered to NamedVar (lower_unresolved_ident
  + is_interp_builtin_fn in expressions.spl); the HIR interpreter gained a
  NamedVar eval arm (env lookup, Function-by-name fallback).
- Qualified ALL bare patterns in interpreter.spl/interpreter_calls.spl
  (Value.*, HirBinOp.*, HirUnaryOp.*, HirAssignOp.*, MethodResolution.*) and
  lower_binop/lower_unaryop (BinOp.*/UnaryOp.*). Unknown flat/AST binary
  operators now fail before backend execution instead of using a defensive
  `Add` value.
- eval_binop: a missing HIR operator now returns a span-bearing internal error
  instead of silently executing `Add`; fresh stage4 execution remains pending.
- Probe cleanup done (deploy precondition): all ungated [LHE*]/[LGL]/[LBO]/
  [LBU]/[LST*]/[LM]/[FBC]/[FBS]/[MS*] eprints removed; the `[frontend] parsed
  module` STDOUT print is now gated behind SIMPLE_COMPILER_TRACE
  (frontend.spl); interpreter/driver probes remain itrace/dtrace-gated
  (SIMPLE_INTERP_TRACE=1).

### Verification (stage4_it18z, clean build)
- `SIMPLE_UNSTUB_HIR=1 <bin> -c "print(1+1)"` → stdout exactly `2`, rc=0.
- `SIMPLE_UNSTUB_HIR=1 <bin> run /tmp/hello_it15.spl` → `hello-world-42`, rc=0.
- `<bin> --version` → `Simple v1.0.0-beta`, rc=0.

### Known follow-ups (NOT blockers for the smoke)
- The `?` operator did not propagate an Err mid-chain in one observed case
  (flow continued into call_function after eval_binop returned Err) — masked
  now that the happy path returns Ok end-to-end, but worth its own iteration.
- `int(text)` builtin lowering (first-char-code result) is a SEED codegen bug;
  the parser now avoids it, but other int() call sites on stage4 remain
  suspect.
- rt_value_int→rt_value_print round-trip SEGV in the compiled interpreter
  remains unexplained (bypassed via pure-Simple print).
- Struct-shadowed variant names (Field/Block/Expr) remain hazardous in every
  OTHER match on stage4; the pre-dispatch idiom in expressions.spl /
  monomorphize_integration.spl is the template.
Binaries: scratchpad/stage4_it18{,b..z}. Coordinator: stub-default flip +
deploy are YOURS; this iteration stops here per instructions.

### Iteration 18 addendum — probe-cleanup regression + final verification
The first cleanup build (it18z) regressed to the silent no-op (funcs=0): two
[LM] probes lived INSIDE `if (... SIMPLE_INTERP_TRACE ...) == "1":` gates and
deleting only the eprint lines left ORPHANED if-headers that captured the
function-lowering `while` loop / `val fn_` as their bodies. Removing the
orphaned headers fixed it. LESSON: when stripping probes, delete the gate
header WITH the probe. Final verification on stage4_it18z2 (clean, probe-free):
`-c "print(1+1)"` → `2` rc=0 (stderr only carries the pre-existing gated-off
frontend notice), `run /tmp/hello_it15.spl` → hello-world-42 rc=0, `--version`
→ Simple v1.0.0-beta rc=0.
Second cleanup follow-up: interpreter_calls.spl's local itrace gate
(`rt_env_get(key.ptr(), key.len()) != 0`) is ALWAYS TRUE (ptr-based env get
returns a non-zero runtime value even for an unset var) so its probes leaked
ungated; replaced with an import of interpreter.spl's text-based gated itrace.
FINAL verified binary: scratchpad/stage4_it18z3 — `-c "print(1+1)"` → stdout
exactly `2`, stderr EMPTY, rc=0; `run` and `--version` clean.

## Iteration 19 (2026-07-03) — multi-function run files: ROOT CAUSE FOUND + FIXED (dict collapse) + user-fn call fixed

Task #85: any run file with 2+ top-level functions silently no-ops (rc=0, no
output); single-fn and `-c` worked. Fresh build reproduced (twofn_min: `fn
helper()->text; fn main(): print("m1"); print(helper())`).

### Root cause (decisive, ungated eprint probes in module_lowering)
Both functions lower successfully, but `HirModule.functions`
(`Dict<SymbolId, HirFunction>`) ends with **one** entry. Probe trail:
```
name=main   sym_is_nil=false eq_prev=false  after_insert idx=0 dict_len=1
name=helper sym_is_nil=false eq_prev=TRUE   after_insert idx=1 dict_len=1
```
`helper`'s `hir_fn.symbol == main`'s `hir_fn.symbol` (`eq_prev=true`) even though
the symbol table assigned DISTINCT ids (`next_symbol_id=2` for the 2 fns). So the
second `functions[hir_fn.symbol]=hir_fn` OVERWRITES the first — `main` is dropped,
`process_module` finds no `main` in `.values()` (only `helper`), returns Unit,
nothing runs. Confirmed by a control: keying with a fresh `SymbolId(id: lower_idx)`
made `dict_len` go 1→2 and `m1` printed.

**Why the keys collide:** `SymbolTable.lookup(name)` returns a **shared/corrupt
SymbolId struct instance** for every top-level function on stage4 (the seed's
`Dict<text,SymbolId>.get()` struct-value corruption, Layer-5 family) — the real
ids are distinct in the table but the looked-up struct HANDLE is shared, so as a
Dict key they compare equal. Reading `.id` off the looked-up SymbolId
nil-derefs (ANY-erasure), confirming the handle is degenerate.

### Fix 1 (committed 95f504162fc / 370e379b6a0): distinct synthetic key
`module_lowering.spl` non-bootstrap loop keys `functions` by
`SymbolId(id: lower_idx)` instead of `hir_fn.symbol`. Every HIR-functions
consumer (monomorphize_integration, backend translate, interpreter
main-by-name scan) iterates `.keys()`/`.values()` and re-indexes with the
yielded key, so distinct synthetic keys preserve all entries and all consumers.

### Fix 2 (committed 370e379b6a0): user-defined fn calls by name
After Fix 1, `main` ran and printed `m1`, then `print(helper())` crashed rc=132.
itrace: `[CF] Function arm f_nil=TRUE` — the env-hit `Value.Function` payload is
nil on stage4 (iteration-18 payload-loss channel), so `call_function`'s
`f_t.name` nil-derefs. Added a NamedVar user-fn fast-path in the interpreter
`Call` arm: after the builtin fast-path misses, resolve the HirFunction by NAME
from `ctx.module.functions.values()` and call it directly, bypassing the
nil-payload Function value. Also made `call_function`'s fallback resolve by name.

### Verified (fresh probe-free build scratchpad/stage4_it19)
- twofn_min → `m1` / `plain-helper`, rc=0 (WAS silent no-op) ✓
- threefn (3 fns) → `main`, rc=0 ✓
- single-fn run (hi-single) → rc=0 ✓
- import `use std.text` → `imports-ok`, rc=0 ✓
- lint src/app/cli/main.spl → rc=0 clean ✓
- test target_presets_spec.spl → PASS rc=0 ✓

### Struct/class SIGSEGV — PARTIALLY diagnosed, NOT yet resolved (separate deeper defect)
A run file containing any struct or class SIGSEGVs during HIR lowering (rc=139).
Bracketing probes localised it precisely, in order:
1. `lower_struct` reached `[LS-PROBE] field-start` but never `field-done` → crash
   is the FIRST field of the FIRST struct, inside `lower_field`. (A `class` parses
   into `module.structs` on this frontend — `class_only` showed
   `classes_count=0 structs_count=1` — so both class- and struct-bearing files hit
   the same `lower_field` path.)
2. Inside `lower_field`, probes showed `enter` and `got-type` printed but not
   `lowered-type` → the crash is `self.lower_type(fld_type)`, not the Field field
   access.
3. `lower_type` matches `t.kind` and destructures `case Named(name, args)` — the
   ANY-erased **enum-payload extraction** of the field-extracted `Type` crashes in
   the Named arm.

Two typed-rebind attempts (committed 855d038b447 `lower_field`: bind `f` to a
`Field` local + both caller loops; f14b0f2db43 `lower_type`: bind `t`/`t.kind` to
`Type`/`TypeKind` locals) each ADVANCED the crash but did NOT resolve it — a fresh
build still SIGSEGVs on `struct_only`/`class_only`. The residual crash is the
ANY-erased enum-payload extraction in `lower_type`'s `Named(name, args)` arm; it
needs the disc-pre-dispatch / `rt_enum_payload` treatment (Layer-3 family, iters
6/10/15) rather than a plain typed rebind. LEFT FOR A FOLLOW-UP ITERATION — it is a
SEPARATE defect from #85 (the struct/class HIR-lowering path was never exercised on
the unstub path before; all prior iterations tested functions only). The
lower_field/lower_type rebinds are kept (correct hardening, no regression).

### Remaining SEPARATE pre-existing defect (NOT the #85 multi-fn bug; unstub path)
- **`-c "print(1+1)"` → rc=1, no output** on this fresh build (baseline before
  any it19 edit already showed this — pre-existing, not caused by it19; `-c`
  does not traverse the modified non-bootstrap functions loop — it goes through
  the `is_bootstrap_entry` branch that calls `lower_module` directly). Left for a
  follow-up iteration.

### #85 STATUS: FIXED. Extended matrix on scratchpad/stage4_it19 (probe-free):
single-fn `run` rc=0; twofn_min → `m1`/`plain-helper` rc=0 (WAS silent no-op);
threefn rc=0; `use std.text` rc=0; lint src/app/cli/main.spl rc=0 clean;
test target_presets_spec.spl PASS rc=0. Struct/class + `-c` are the two separate
open defects above — coordinator should NOT re-flip the unstub default until at
least struct/class lowers, since real programs use structs.

## Iteration 20 (2026-07-04) — #87 FIXED; #86 SIGSEGV FIXED (decls lower + run); struct-prints-5 blocked by a deeper interpreter-runtime cascade

### #87 (`-c "print(1+1)"`): FIXED — was printing `98`, not rc=1
On the current-HEAD build `-c "print(1+1)"` printed **98** (= 49+49 = char('1')
+char('1')), NOT rc=1 as handed off. Root cause: `parser_guarded_int_text`
(10.frontend/core/parser.spl) called bare `int(t)`, and the stage4 `int(text)`
builtin returns the FIRST character's char code (iteration-18 hazard #7). The
iteration-18 manual-decimal-accumulation workaround had been **reverted by
commit bb9aa222509** ("stage4 parse surface at ZERO errors"), which replaced the
loop with `int(t)`. Restored the char_code accumulation loop. `-c "print(1+1)"`
now prints `2`. LESSON: bb9aa222509 also ADDED bug docs noting int() misdispatch
yet removed the workaround — never remove a stage4 int()-avoidance without a
replacement.

### #86 (struct/class run files SIGSEGV rc=139): the SIGSEGV is FIXED
Struct/class DECLARATIONS now lower and run (`struct P: x:int` + `main` printing
a literal → rc=0). Chain of root causes fixed (gdb-localized each hop):

1. **`lower_type` multi-arm `match lt_kind` MIS-ROUTES on stage4** (types.spl).
   Struct/class field types lower to `TypeKind.Infer` (confirmed by disc probe:
   field disc == Infer reference disc 3031551406; Named ref = 2288079638), but
   the multi-arm qualified `match` routed the Infer value into its FIRST arm
   `case TypeKind.Named(...)` (irrefutable — `Named` also names a HirTypeKind
   variant), extracting garbage `args` and SIGSEGV in `lower_type_list`
   (gdb: lower_type_list ← lower_type ← lower_field ← lower_struct). The IDENTICAL
   match works for function param/return types (twofn's `-> text`), so it is
   **value-specific irrefutable-first-arm mis-routing**, NOT a corrupt value.
   FIX: disc-dispatch `lower_type` — reference discs from freshly constructed
   TypeKind values + isolated single-arm guarded extraction (the
   expressions.spl/statements.spl idiom). Qualifying the arms alone did NOT fix
   it; disc-dispatch did (rc=139 → advanced).
2. **`lower_field` default used Option `.?`/`.unwrap()` on a plain desugared
   field** (declaration_lowering.spl). `Field.default` is a plain `Expr` gated by
   `has_default` (NOT Optional); `if fld.default.?:` mis-evaluated true and
   unwrapped a nil Expr → `lower_hir_expr(nil)` → "field access on nil receiver"
   SIGILL. FIX: gate on `fld.has_default`, use `fld.default` directly (same class
   as the iter14 eval_block fix).
3. **`lower_hir_stmt` multi-arm match MIS-ROUTES `StmtKind.Val/Var/Return/Assign`**
   (statements.spl) — SAME class as #1. A genuine `StmtKind.Val` matched NONE of
   the qualified arms and fell to `case _:` → `HirExprKind.Error` (disc
   2735847868 = hash("Error")), so **every val-decl (and non-Expr statement)
   lowered to Error** and crashed the interpreter. Only Expr-statement bodies
   (`print(...)`) were ever exercised on the unstub path — that is why `-c`,
   `hello`, and `twofn` all worked while `val n = 5` did not. FIX: disc-dispatch
   Val/Var/Return/Assign before the match (reference discs + single-arm
   extraction). Repurposed the unused `hir_stmt_expr_disc`(ExprKind) extern to
   `hir_stmt_kind_disc`(StmtKind) — a file may declare `rt_enum_discriminant`
   only once (extern name == C symbol; no aliasing), and different files already
   use different enum-typed copies. After this fix `val n = 5` no longer crashes.
4. Also: `lower_struct`/`lower_class` switched from `match struct_: case
   Struct(...)` destructure to direct field access (defensive; harmless), and
   `module_assembly.spl` struct-Field construction switched positional → named
   (defensive; the field type was already Infer, so this was a no-op for the
   crash — recorded so a future reader does not re-chase it).

### GENERALIZED HAZARD: irrefutable FIRST-ARM mis-routing in multi-arm matches
`match kind: case Enum.FirstVariant(...)` on stage4 can (a) swallow OTHER
variants (irrefutable), or (b) fail to match its OWN value which then falls to
`case _`. Occurs when the variant name is shared across enums (Named in
TypeKind+HirTypeKind; Expr in StmtKind+HirStmtKind) even when QUALIFIED. The
reliable cure is **disc-dispatch**: `rt_enum_discriminant` of the scrutinee vs a
reference disc from a freshly-constructed value, then an isolated single-arm
guarded `match` for payload extraction. Applied to lower_type, lower_hir_stmt;
the same template already lives in expressions.spl / statements.spl. Whole-match
qualification is NOT sufficient.

### REMAINING BLOCKER for the struct-prints-5 DONE gate (interpreter runtime, NOT lowering)
With the above, `struct P: x:int; val p = P(x:5); print(p.x)` no longer SIGSEGVs
in lowering — the crash moved to the **HIR interpreter**, which was only ever
exercised with print-only bodies and is incomplete for real programs. Precisely
localized, in order (all on scratchpad/stage4_it20h, gdb + itrace):
- **Env variable resolution mis-keys.** `val n = 5; print(n)` now lowers fine and
  runs rc=0 but prints nothing; `val a=3; val b=4; print(a+b)` → "invalid
  operands for +". The env (env.spl) scopes are `Dict<SymbolId, Value>`; the Let
  defines with the define-site SymbolId while the Var reads with the lookup-site
  SymbolId (the iter19 shared/corrupt-handle), so struct-keyed lookup misses or
  returns a wrong Value. Candidate fix: key the env by `symbol.id` (i64) — but
  the looked-up SymbolId's `.id` may itself be degenerate (iter19), so verify.
- **Struct construction is unimplemented.** `Value.Struct(type_, fields)` exists
  (backend_types.spl) but `P(x:5)` is a `HirExprKind.Call` whose callee `P`
  resolves to a struct symbol; the Call arm has no struct-constructor path, so it
  eval's the callee as a value (NamedVar fallback → nil-payload `Value.Function`)
  → `call_function` → `eval_block(nil)` → SIGILL. Needs: detect a struct-typed
  callee (by name/symbol against `ctx.module.structs`) and build
  `Value.Struct(name, {argname: argvalue})` from the named `HirCallArg`s.
- **Field access is unimplemented.** `eval_expr` has NO `HirExprKind.Field` arm
  (only IntLit…Call…Block…). `p.x` would hit `case _: not_implemented`. Needs a
  Field arm; `Field` is struct-shadowed (struct Field) so it must be
  DISC-PRE-DISPATCHED (hash("Field")=21232742) like expressions.spl, not a plain
  match arm.
These are three separate interpreter features (each with its own stage4 hazard),
not codegen hazards — left for iteration 21 with the localization above.

### cfg @cfg-same-name dispatch (coordinator repros) — NOT resolved
`scratchpad/cfg_arch_dispatch_repro_a.spl`/`_b.spl` (two `@cfg(x86_64)`/
`@cfg(arm64)` `fn arch_name()` + `fn main() -> i32`) still silently no-op (rc=0).
Not investigated to root this iteration. Note: `_pp_extract_cfg_condition`
handles only the COMMA `@cfg("k","v")` form; the spaced `@cfg(target_arch =
"x86_64")` form is tokenized into 3 tokens and the atom "target_arch" alone
evaluates false (separate cfg-eval gap). And `main() -> i32` exit codes are not
propagated by the run path (rc stays 0). Left for a follow-up.

### Verified on scratchpad/stage4_it20h (probe-free, all committed)
`-c "print(1+1)"` → `2` rc=0; `run` single-fn/twofn/threefn/`use std.text` rc=0;
struct/class DECLARATION (no construction) rc=0; `val n = 5` no longer crashes
(rc=0); lint src/app/cli/main.spl rc=0; test
test/01_unit/compiler/target_presets_spec.spl PASS 23/0 rc=0. Struct CONSTRUCTION
(`P(x:5)`), variable READBACK, and the cfg repros remain open (interpreter-runtime
cascade above). Commits: parser int-accum; lower_type disc-dispatch; lower_field
has_default; lower_hir_stmt disc-dispatch; module_assembly named + lower_struct/
class direct-access. Coordinator: do NOT re-flip the unstub default — real
programs use variables and structs, which do not yet execute.
 
 ## Task #70 (2026-07-04) — local `val`/`var` declarations + read-back in the unstub interpreter; #70 dict-struct mutation is gated behind this + struct lowering
 
 Task #70 framed the crash as "typed struct value in dict mutation SIGILLs on
+stage4". Isolation showed that is only the OUTER victim. Repro matrix (all
 `SIMPLE_UNSTUB_HIR=1 <stage4> run <f>`; deployed `bin/simple` = healthy baseline,
+prints correct output for every case below):
 
 | repro | before (it19/it20a-c, deployed) | after 4 fixes (stage4_t70) |
 |-------|--------------------------------|----------------------------|
 | `print(1)\nprint(2)` (no locals) | rc=0 | rc=0 |
 | `var d: Dict<text,i64> = {}` + `print(1)` | **rc=132 SIGILL** | **rc=0** ✓ |
 | `var d={}; d["k"]=5; print(2)` (index-assign) | **rc=132** | **rc=0** ✓ |
 | `var a:[i64]=[]; print(1)` (empty array) | **rc=132** | **rc=0** ✓ |
 | `val x=5; print(x)` (scalar read-back) | rc=132 SIGILL | rc=0 but prints EMPTY (value corrupt) |
 | `val x=d["k"]; print(x)` (dict read-back) | rc=139 | rc=139 (Index read-back, still) |
 | struct-bearing / dict-of-struct (#70) | rc=139 SEGV → rc=132 (it20f) | rc=132 (struct lowering, it20 territory) |
 | `--version` | rc=0 | rc=0 (no regression) |
 
 ### Root cause A (FIXED, in 70.backend territory): local declarations SIGILL
 `InterpreterBackendImpl.exec_stmt` (interpreter.spl) matched `HirStmtKind.Expr`
+FIRST. `Expr` is a struct-shadowed variant name (`struct Expr`) whose pattern
+test compiles ALWAYS-TRUE on stage4 (iteration-18 hazard #1), so EVERY statement
+— including every `Let`/`Assign` — was swallowed by the Expr arm and fed to
+eval_expr with a garbage payload (extracted disc reads "Error" = 2735847868) →
+"field access on nil receiver" SIGILL. So NO local `val`/`var` declaration ran;
+this blocks #70 (and essentially every real program) long before any dict logic.
+Three cumulative `.spl` fixes (all committed, 70.backend only — verified the
+first two ALONE were insufficient, the disc pre-read was the decisive one):
 1. **Reorder** exec_stmt arms so the sound non-shadowed `Let`/`Assign` come
    BEFORE the always-true `Expr`; `Block` last (mirrors 40.mono scan_stmt).
    *Reorder alone did NOT fix it* — the Let arm still failed to match.
 2. **eval_block** typed rebind `val stmt_t: HirStmt = stmt` of the `block.stmts`
    loop element before `exec_stmt` (the iter-9 cure 40.mono scan_block already
    has). *Also insufficient alone.*
 3. **DECISIVE:** explicit load-bearing `val stmt_disc =
    rt_enum_discriminant(stmt.kind)` pre-read BEFORE `match stmt.kind` (fed into
    itrace so it is not DCE'd). This iteration-18 disc-pre-dispatch materializes
    the discriminant so the qualified `Let`/`Assign` arms test correctly — the Let
    stmt (disc 2163764024 = hash("Let")) then matches its arm. After this, local
    declaration, empty/populated dict-literal init, empty-array init and
    index-assign all run rc=0. **Idiom to reuse: any struct-shadowed-variant
    `match` on stage4 needs an explicit `rt_enum_discriminant(x)` pre-read of the
    scrutinee kind before the match, not just qualified arms + reorder.**
 
 ### Root cause B (PARTIALLY fixed, then WALL): variable read-back corrupts the Value
 `val x=5; print(x)` still didn't print `5`. The interpreter env is
 `Environment.scopes: [Dict<SymbolId, Value>]` (env.spl). `define` stores the
 `Value` enum into a dict that is itself an array element; `lookup` returns
 `Some(scope[symbol])`. Fix B (committed, env.spl): typed-rebind
 `val scope: Dict<SymbolId,Value> = self.scopes[i]` and `val v: Value =
+scope[symbol]` before `Some(v)` — this advanced `print(x)` from **SEGV (rc=139)
+→ rc=0** (no longer crashes). BUT it prints EMPTY: the Print builtin's
 `match arg` reads **`rt_enum_discriminant(arg) == -1`** (diagnostic probe, since
+reverted). A valid `Value.Int(5)` would carry hash("Int"); **disc == -1 means the
+enum tag+payload were DESTROYED at the Dict store/load boundary.** Typed rebinds
+prevent the field-offset crash but cannot recover a value whose discriminant is
+already -1 in the stored representation.
 
 ### THE WALL (seed-level, shared with it20 / not fixable in pure Simple here)
 Storing an enum/struct `Value` into a `Dict<K, Value>` and reading it back on
+stage4 yields a degenerate value (disc = -1, payload lost). This is the same deep
+ANY-erasure store/load corruption documented in iterations 8/9/19 (`Dict.values()`
+/ struct-keyed dict), now proven at the **Dict VALUE store/load** for enum values.
 It is exactly task #70's user pattern (`Dict<text, MyStruct>`) — and it also
 corrupts the interpreter's own variable environment. No pure-Simple typed-rebind
 recovers it because the discriminant is genuinely -1 after retrieval. A real fix
 needs the seed cranelift Dict-value store/load to preserve the enum tag+payload
+(box the value, or thread a typed `HirType::Dict{K,V}` so the value isn't erased
 to ANY) — `src/compiler_rust/.../codegen` Dict value channel + `rt_dict_get`/set
 boxing. Until then, #70's read-back (`val v = d["k"]; v.field`) and the
 interpreter's `print(local_var)` cannot round-trip a struct/enum value.
 
 ### Territory / handoff
 - FIXED in 70.backend (mine): exec_stmt reorder + typed rebind + disc pre-read
   (commits 47fa555, 03f0947, 95deefc); env.lookup typed rebind (commit 4abbcbf).
   These are correct, no-regression hardening (deployed/healthy compiler unaffected
   — the rebinds/pre-read are no-ops on a correct backend). `--version` rc=0.
 - BLOCKED on it20 (20.hir): struct/class HIR lowering still crashes (rc132 on
   it20f) — every dict-of-struct repro dies there first, before dict logic.
 - BLOCKED on SEED: the Dict<K, enum/struct-Value> store/load corruption (disc=-1)
   — the true #70 root and the interpreter env read-back blocker.
 Repros: scratchpad `p1_valscalar.spl`, `n1_declonly.spl`, `n2_assign.spl`,
 `n3_read.spl`, `c70_dictscalar.spl`, `r70_read.spl`, `r70_mutfield.spl`.
 Binary: scratchpad/stage4_t70.

## Iteration 22 (2026-07-04, task #105) — @cfg spaced key=value tokenizer bug FIXED; full-scale "lowered funcs=3" gate NOT closed, entangled with #104

Task #105 scope: filter @cfg-inactive fn decls before HIR lowering (pure
Simple, `src/compiler/10.frontend` / `20.hir` only).

### Real bug found + fixed: `_pp_parse_primary` only consumed the first token of a multi-token @cfg condition
`src/compiler/10.frontend/core/parser_preprocessor.spl` `_pp_parse_primary`
took exactly one token off `_pp_tokens` and evaluated it via `_pp_eval_atom`,
ignoring the rest. The SPACED key/value form `@cfg(arch = "x86_64")`
tokenizes (whitespace-delimited) as `["arch", "=", "\"x86_64\""]`; only
`"arch"` reached `_pp_eval_atom`, which falls through every known keyword to
`false` regardless of the real value — so a spaced `@cfg(key = value)`
condition ALWAYS evaluated false (both matching and non-matching variants
dropped). Fixed by reassembling one or more adjacent `"="` tokens plus the
following value token into a single `key=value`/`key==value` atom before
calling `_pp_eval_atom` (which already had the `cfg_eval_key_value` split
logic for that shape). Verified via cheap seed `native-build` repros
(`t105_frontend_probe2.spl` + `cfg_arch_dispatch_repro_spaced.spl`,
~10s each): before fix, `@cfg(arch = "x86_64")`/`@cfg(arch = "arm64")`
variants of `arch_name()` BOTH dropped (`module.functions.len()`==1, only
`main`); after fix, exactly the matching variant survives
(`module.functions.len()`==2) for both `SIMPLE_TARGET_ARCH=x86_64` and
`=aarch64`. Landed: commit `061b99782e61` (main).

### Host-arch-detection fallback is ALSO broken in this sandbox (separate, unfixed)
`cfg_detect_arch()`'s Linux fallback reads `/proc/sys/kernel/arch` via
`rt_file_read_text`. In this sandbox that file's `stat()` size is 0 (proc
pseudo-files don't report real size) so the read returns `""` even though
`cat /proc/sys/kernel/arch` and `wc -c` show real 7-byte content — a
size-based native `rt_file_read_text` bug, NOT fixable from pure Simple.
`rt_process_run("uname", ["-m"])` is also unusable as a substitute fallback:
verified it silently drops ALL args (`uname -m`/`uname -s`/`echo hello
world` all ran as bare `uname`/`echo` with no argv) — a separate native
runtime bug. Both are out of scope for #105 (native runtime, not
`src/compiler/**`); recorded here as a concrete follow-up, not silently
dropped. Use `SIMPLE_TARGET_ARCH=<arch>` to force correct detection when
testing @cfg-arch dispatch until a native-side fix lands.

### The exact task #105 gate ("lowered funcs=3" -> expect 2) is NOT closed by any preprocessor-side fix
Full self-hosted stage4 rebuild (993 modules, `native-build --backend
cranelift`, current HEAD + the tokenizer fix above) on
`cfg_arch_dispatch_repro_a.spl` (bare-atom `@cfg(x86_64)`/`@cfg(arm64)`
`arch_name()` variants + `main`), `SIMPLE_UNSTUB_HIR=1
SIMPLE_INTERP_TRACE=1`:
- `SIMPLE_TARGET_ARCH=x86_64` -> `[DRV] lowered funcs=3` (unchanged from
  pre-fix baseline).
- `SIMPLE_TARGET_ARCH=aarch64` -> `[DRV] lowered funcs=3` (IDENTICAL count).
- Spaced-form repro (`cfg_arch_dispatch_repro_spaced.spl`) -> also
  `lowered funcs=3` at full scale, despite the SAME source producing the
  CORRECT `functions.len()==2` on the small-scale seed-compiled probe
  binary (`t105_frontend_probe2.spl`) with the identical `.spl` sources.

This is a genuine seed-vs-stage4 divergence: the @cfg text-preprocessor is
verifiably CORRECT (both bare-atom and, after this iteration's fix, spaced
key=value forms) when compiled by the seed and run standalone, but produces
an UNFILTERED result (both arch variants survive, identically regardless of
forced arch) only on the 993-module self-hosted binary. Getting the exact
same "3" independent of which arch is forced rules out a mere
detection-value bug (that would change WHICH variant is kept, not whether
BOTH survive) and points at either (a) a global same-bare-name dispatch
collision — `preprocess_conditionals` is defined in TWO places
(`frontend.spl`'s local unique-name wrapper AND
`core/parser_preprocessor.spl`'s public wrapper, both delegating to
`_pp_preprocess_conditionals`) though `core/parser.spl`'s own top-level
entry points (`parse_module`/`parse_module_file`, NOT on the live
`parse_and_build_module` path) call `_pp_preprocess_conditionals` directly
so this specific double-definition was not confirmed as the live cause; or
(b) a #104-class Dict/struct-field ANY-erasure corruption of
`Module.functions: Dict<text, Function>`'s duplicate-key overwrite at scale
(each `functions[fn_.name] = fn_` assignment should collapse both
same-named `arch_name` decls to one dict entry; getting a HIR-level
`lowered funcs=3` for main+2-duplicate-name-variants is only possible if
that overwrite itself misbehaves at scale, independent of whether
preprocessing blanked either declaration).

Root-causing (a) vs (b) needs stage4 gdb/eprint probing inside
`_pp_preprocess_conditionals` and `flat_ast_to_module`'s
`functions[fn_.name] = fn_` at full scale — the same instrumentation class
already walled by trap D (env-gated eprint probes are mute in some
stage4-compiled modules; must use ungated eprint) and by the #104
ANY-erasure wall this task was scoped to avoid. Handing off to the #104
lane / a future iteration with a narrower repro
(`scratchpad/cfg_arch_dispatch_repro_a.spl`,
`scratchpad/cfg_arch_dispatch_repro_spaced.spl`) and this gate
(`SIMPLE_UNSTUB_HIR=1 SIMPLE_INTERP_TRACE=1 SIMPLE_TARGET_ARCH=x86_64 <bin>
run <repro> 2>&1 | grep 'lowered funcs'`, expect 2).

### Regression matrix (full-scale stage4 rebuild with the tokenizer fix, all PASS)
| case | result |
|------|--------|
| `-c "print(1+1)"` | `2` rc=0 |
| hello | `hello` rc=0 |
| twofn (helper + main) | `m1`/`plain-helper` rc=0 |
| lint src/app/cli/main.spl | rc=0, "Lint passed: all files clean" |
| cfg_arch_dispatch_repro_a (informational, gate not closed) | rc=0, `lowered funcs=3` |

## Task #107 (2026-07-04) — env `Value` round-trip disc=-1 PRECISELY LOCALIZED to the seed Dict-value box channel (shared root with #109)

Successor to #104. Built the #107 seed fresh from HEAD (includes #104's typed
`HirType::Dict{K,V}`) into `target/bootstrap_task107`; stage4 = 993/0. Repros
UNCHANGED: `val x=5; print(x)` SIGSEGV; `val a=2; val b=3; print(a+b)` →
"invalid operands for +" (the looked-up operands are not `Value.Int`). Direct
disc measurement (probes, since reverted) is the decisive new evidence:

- STORE: in `env.spl::define`, `rt_enum_discriminant(value)` on the incoming
  param = **2375492728** (a valid `Value.Int` Enum heap object; interpreter.spl
  `[LET]` shows the same at the call site). Keys match (store `a` → read `a`).
- LOAD: interpreter.spl NamedVar `ctx.env.lookup("a")` returns a HIT whose
  `rt_enum_discriminant` = **-1**. `rt_enum_discriminant` (runtime
  `value/objects.rs:282`) returns -1 **iff** `get_typed_ptr::<RuntimeEnum>` fails,
  i.e. the value is NOT an Enum heap object. So the enum's heap-tag is destroyed
  by the `Dict<text,Value>` store→load round-trip.

### Hypotheses TESTED and RULED OUT (each a full stage4 rebuild)
1. **Cross-kind struct/enum `Value` name collision** (4 types named `Value`:
   enum in 70.backend/backend_types + std di.spl + gc_async_mut evaluator.spl;
   struct in app/interpreter/core/value.spl). Added a seed census in
   `pipeline/native_project/imports.rs` (`SIMPLE_CENSUS_COLLIDE`) flagging any
   name present in BOTH `struct_defs` and `enum_defs`. Result: **ZERO** cross-kind
   collisions in the entry closure — the imports walker only collects
   closure-reachable files, and the peripheral `Value`s aren't reachable from
   `main.spl`. Guard reverted (no-op). Enum discriminants are hash-based
   (`variant_name.hash`, order-independent), so even the variant-merge in
   `enum_defs.entry(name).or_default()` is disc-safe.
2. **Method-name-collision mis-dispatch.** Three modules declare identical
   `define(name:text,value:Value)` / `lookup(name:text)->Value?` (Environment,
   pure evaluator, expression_evaluator). Probe anomaly (`[ENV-DEF]` fired but
   `[ENV-LK]` did NOT while a hit still returned) suggested `ctx.env.lookup`
   bound to a foreign body. Renamed all Environment value methods to unique
   `env_define_value`/`env_lookup_value`/`env_assign_value`/
   `env_define_global_value` (iteration-14 cure) across env.spl + interpreter.spl
   + interpreter_calls.spl + jit_interpreter.spl, consistently. Rebuilt: **still
   SIGSEGV / invalid operands.** Method-collision DISPROVEN as the cause. (The
   rename is sound hardening but was swept by a parallel hourly-sync reconcile
   before it could be re-landed; not re-attempted.)
3. **Store-side typed rebind** (`var scope: Dict<text,Value> = self.scopes[i];
   scope[name]=value; self.scopes[i]=scope`) — no change. Confirms `.spl`
   typed-rebinds cannot recover the value; the erasure is in the seed codegen.

### ROOT (seed codegen, shared with #109 — coordinator-verified)
The enum heap pointer (`ptr | TAG_HEAP=0b001`, tags in
`runtime/src/value/tags.rs`) is mis-boxed through the `Dict<text,Value>` ANY
value channel: it round-trips as a NON-heap value → disc -1. Same family as
#109's generic/ANY enum-payload double-untag (scalar `Ok(42).unwrap()`=`42>>3`=5).
Fix locus is the seed Dict-value box/unbox convention:
- `compile_index_get`/`compile_index_set` (`codegen/instr/collections.rs:338-378`)
  pass values verbatim, deferring box/unbox to `MirInst::Box*/Unbox*` keyed on
  `element_expr_ty` (`mir/lower/lowering_expr_struct.rs:307-317, 536-548`).
- For a `Dict` receiver, `element_expr_ty` derivation only handles
  `HirType::Array` (307-317), so a dict-get stays ANY→verbatim (no unbox). The
  corruption is therefore on the **STORE**: the index-assign lowering emits a
  `BoxInt` on the value operand when the value's static type resolves to
  I64/scalar through the ANY channel — `rt_box_int(enum_ptr)` wraps the heap
  pointer as a boxed-int object; the get returns that boxed-int verbatim (dict
  element type is Value/heap → no compensating unbox) → disc -1.
- Sibling site: single-payload enum construction stores the payload RAW
  (`get_vreg_or_default`, `codegen/instr/calls.rs:2287` and Ok/Err at 2747-2748)
  while multi-arg uses `runtime_payload_value` (tags scalars). The asymmetry is
  #109's `>>3` bug and must be aligned in the same pass.

### Handoff
Fix belongs in the seed native codegen with #109: at the ANY/generic container
value boundary, boxing and unboxing must agree — do NOT `BoxInt` a value that is
already a heap RuntimeValue on dict/array store, and align single- vs multi-arg
enum-payload boxing. Verify with `p2_add` (expect 5), `p1_valscalar` (5), AND
#109's `scratchpad/payload_check.spl` (expect 42) on a stage4 rebuild.
Repros: scratchpad `p1_valscalar.spl`, `p2_add.spl`; seed `target/bootstrap_task107`.

## Task #117 (2026-07-04) — both #107/#109 mechanisms FIXED in seed codegen (landed a5893c615fc); gate NOT closed — residual localized to a THIRD, pre-existing corruption in `interpreter_calls.call_function`

### Fixes landed (seed Rust, all three sites; swept into `a5893c615fc` by a
parallel hourly sync together with #113's `rt_enum_discriminant`
interpreter_extern registration — content verified at HEAD by git grep)
1. **Dict element-type derivation, GET** (`mir/lower/lowering_expr_struct.rs`
   `element_expr_ty`): added `HirType::Dict { value } => Some(*value)` parallel
   to the Array arm, so scalar V unboxes and heap V passes verbatim.
2. **Dict element-type derivation, SET** (`mir/lower/lowering_stmt.rs` index
   assign): derive `recv_elem_ty` from `HirType::Array/Dict`; when the element
   type is a heap type, suppress `BoxInt`/`BoxFloat`/`rt_value_bool` on the
   value operand (was wrapping heap RuntimeValues as boxed-int → tag destroyed).
3. **Enum single-payload boxing asymmetry** (`codegen/instr/calls.rs` 2287 and
   Ok/Err ~2748): single-payload construction now goes through
   `runtime_payload_value` (tags scalars) exactly like the multi-arg path.

### A/B verification (stage4 from SAME HEAD: `stage4_t107base` = pre-fix #107
seed vs `stage4_t117` = #117 seed; both 993/0)
| gate | t107base (pre-fix) | t117 (post-fix) |
|---|---|---|
| p1_valscalar (want 5) | SIGSEGV core dump | rc=0, prints BLANK line |
| p2_add (want 5) | invalid operands for + | invalid operands for + |
| payload_check (want 42) | SIGILL nil-receiver | SIGILL nil-receiver |
| r70_read (want 1/hi) | SIGILL nil-receiver | SIGILL nil-receiver |
| m4 struct P(x:7) (want x=7) | SIGILL nil-receiver | SIGILL nil-receiver |
| -c "print(1+1)" | 2 | 2 |
| hello / twofn / lint main.spl | pass | pass |
| cfg_min2 | silent (pre-existing) | silent (pre-existing) |

**No regressions**; p1 advanced SIGSEGV→no-crash. But the #107 repros are NOT
closed: the two fixed mechanisms were necessary but not sufficient.

### Residual root (gdb, stage4_t117, `run m4.spl` — the SIMPLEST failing case:
plain `struct P{x:i64}; P(x:7); print("x={p.x}")`, no Dict/enum in user code)
```
#0 backend__backend__interpreter_calls__InterpreterBackendImpl_dot_call_function  <- ud2 (+2157, nil-receiver guard)
#1 eval_expr  #2 exec_stmt  #3 eval_block  #4 call_hir_function  #5 process_module
```
The stage4-compiled interpreter faults inside `call_function`
(`src/compiler/70.backend/backend/interpreter_calls.spl`) while dispatching the
struct-constructor call — a field access on a nil receiver, i.e. some
Dict/struct lookup inside call_function still round-trips to nil in seed
cranelift output. Pre-existing (identical on t107base); NOT introduced by the
#117 fixes and NOT one of the two #107-cited sites. Next task: instrument
`call_function`'s lookup chain (fn-name → HirFunction / struct-def dict) the
way iteration 13 probed process_module, or gdb `x/gx` the receiver at the
faulting FieldGet to identify which lookup returns nil.

### Also discovered (interpreter-side #109 analog — SEPARATE bug)
The SEED's own Rust interpreter (`$SEED run payload_check.spl`) and the
deployed rolled-back stage4 BOTH print `payload=5` + `5` for `Ok(42)` — the
`42>>3` double-untag exists in the seed INTERPRETER path too, not only in
cranelift codegen. `payload_check` therefore cannot gate at 42 under `run`
(interpret mode) until the interpreter-side convention is also aligned.

### Standalone-harness note
Small `native-build --source repro.spl` builds at repo root JIT/interpret the
`.spl` native_build_worker whose closure spans src/app+src/compiler; before
`a5893c615fc` they died on `semantic: unknown extern function:
rt_enum_discriminant` (#113, fixed); they now fail in the worker itself
(`semantic: undefined field 'id' on nil` / `cannot convert object to int`)
while the FULL stage4 build (explicit --source src/{compiler,app,lib}) builds
993/0 — use full stage4 builds, not standalone repro builds, to gate this work.
Binaries: scratchpad `stage4_t117`, `stage4_t107base`; seed
`src/compiler_rust/target/bootstrap_task117/bootstrap/simple` (built at HEAD
0fae3e69bb0-era with all three fixes + #113).

## Task #121 (2026-07-04) — BOTH defects PRECISELY ROOT-CAUSED; both naive point-fixes REGRESS self-host (clean-build proof); no net seed change landed

Successor to #117. Built the #121 seed fresh from HEAD into
`target/bootstrap_task121`. **Key methodology correction that unblocked both
diagnoses:** the `SIMPLE_DUMP_MIR=<fn>` env dumps post-inline MIR; using it on
the seed's own JIT (`$SEED run`, default `ExecutionMode::Jit`) gives instant
primary evidence with NO stage4 rebuild. Also isolate stage4 builds from the
shared `.simple/native_cache` (content-keyed, NOT seed-keyed → any seed-codegen
change yields a FRANKEN binary of new+old-seed objects) with
`native-build --cache-dir <isolated>`; a `993 compiled, 0 cached` line confirms a
true clean build.

### DEFECT B — `$SEED run payload_check.spl` prints `payload=5` — is CRANELIFT JIT, NOT the interpreter
The #117 doc mis-attributed `$SEED run` to "the interpreter." Ground truth:
`SIMPLE_EXECUTION_MODE=interpret $SEED run payload_check.spl` → **42 (correct)**;
default (JIT) and `=cranelift` → **5**. The Rust tree-walker is fine; the bug is
seed cranelift codegen. **Root (MIR-confirmed):** `Ok(42)` lowers to
`MirInst::ResultOk`, whose codegen `create_enum_value`
(`codegen/instr/result.rs:36-38`) stores the scalar payload **RAW** via
`get_vreg_or_default`, but extraction (`rt_enum_payload` + MIR `UnboxInt`)
unconditionally untags → `42 >> 3 = 5`. #117 fixed the *calls.rs* Call-based
Ok/Err construction (`runtime_payload_value` tags scalars) but MISSED this
dedicated `MirInst::ResultOk/ResultErr/OptionSome` path (`compile_option_some` /
`compile_result_ok` → `create_enum_value`).
**Fix attempted + REVERTED:** tagging the payload in `create_enum_value` via the
shared `runtime_payload_value` made `$SEED run payload_check=42` / `b_unwrap=42`
/ `b_some=42` (all verified), but a **clean full stage4 rebuild (993/0) with the
tagging seed made `-c "print(1+1)"`/`hello`/`run` SILENT (no-op)** — the
self-hosted compiler's enum-payload consumers rely on the RAW convention.
Control `stage4_ctrl117` (task117 seed, same source, shared cache) → `-c`=2,
`hello`=hello; the ONLY variable is the seed. So the tag-construction fix is
net-negative and was reverted (commit landed then reverted; net zero seed diff).

### DEFECT A — stage4 `run m4.spl` (`struct P{x:int}; P(x:7); print("x={p.x}")`) nil-receiver — env `Dict<text,Value>` round-trip NILs the nested `Value.Function` heap payload
`SIMPLE_INTERP_TRACE=1` (the compiled-in `itrace`, no rebuild needed) pinpoints
the fault: `call_function` (`interpreter_calls.spl:110-114`) `case
Value.Function(f)` binds **f=nil** (`[CF] Function arm f_nil=true`) → crash at
line 114 `f_t.name`. `P` is registered by `process_module`
(`interpreter.spl:117-120`) as `Value.Function(FunctionValue{symbol,name})` via
`define_global` into the env `Dict<text,Value>`, and resolved back by
`NamedVar env-hit` → `.unwrap()`.
**Decisive read-back probe** (temporarily inserted right after `define_global`,
since removed): `[REG] store name=P gfv_nil=false` then `[REG] readback name=P
disc=Function rbf_nil=true`. So the **store is good; the immediate
lookup→unwrap read-back preserves the `Function` discriminant but NILs the
nested `FunctionValue` heap payload.** This is the #107 env-channel family
(enum-with-heap-struct payload lost through the `Dict<text,Value>` ANY value
channel), NOT construction, and NOT fixed by #117's scalar Dict box/unbox.

### A separate, REAL, non-stage4 bug found while isolating DEFECT A (minimal repro `scratchpad/enumdict3.spl`)
`Some(heap_enum).unwrap()` corrupts the wrapped enum: `A CORRUPT` / `B CORRUPT`
(dict) / `C ok` (direct match, no Option). MIR shows `.unwrap()` emits
`rt_enum_payload` **+ `UnboxInt`** on the heap enum pointer (`>>3` mangles it →
wrong disc). Root (probe-confirmed, `hir/lower/expr/mod.rs:57`
`enum_payload_type_for_builtin_method`): an optional `T?` is `HirType::Pointer{
inner:T }`; the Pointer arm **recurses into `T`** and, for `T = enum Val:
Int(i64)|Func(FV)`, returns `Val`'s FIRST variant payload (`i64` → `TypeId(5)`),
so a scalar `payload_ty` is stamped on the `rt_enum_payload` BuiltinCall and the
MIR emits `UnboxInt` on the heap pointer.
**Fix attempted + REVERTED:** making the Pointer arm `return Some(*inner)` fixed
`enumdict3` (A/B/C ok) but ALSO made a clean stage4 (993/0) `-c`/`hello` SILENT:
self-host optionals are pervasively **nullable pointers** (`unwrap` == identity),
and forcing `Pointer{inner}` unwrap through `rt_enum_payload` breaks them.
**Note this is NOT stage4's m4 mechanism:** enumdict3 CORRUPTS the disc, whereas
stage4 m4 PRESERVES the `Function` disc and only nils the nested payload — two
distinct manifestations of the same seed enum/Value convention family.

### Unifying constraint (the wall for point-fixes)
Seed cranelift codegen has several enum/`Value` payload-convention mismatches
(construction RAW vs extraction `UnboxInt`; nullable-pointer optional vs
`OptionSome` heap enum; `Dict<text,Value>` nested-heap-payload loss). The
self-hosted compiler (src/compiler, compiled BY the seed) pervasively depends on
the CURRENT (partially-buggy) form of each, so any point-fix to one convention
regresses the whole self-host (`-c`/`hello` go silent). **Proven twice this task
with clean 993/0 rebuilds.** A correct fix must make construction and extraction
agree GLOBALLY (all of: `ResultOk/OptionSome` vs calls.rs Ok/Err; match-binding
`UnboxInt` vs direct `.spl` `rt_enum_payload`; nullable-pointer vs enum optional
representation) in ONE coordinated change, then full-rebuild + regate — not the
incremental point-patches that cleared earlier layers.

### Gate table (stage4 = clean 993/0 build with the HEALTHY task117 seed = current-source baseline; all seed fixes reverted)
| gate | result |
|---|---|
| build 993/0 | PASS |
| `-c "print(1+1)"` | 2 (PASS) |
| `hello` | hello (PASS) |
| `$SEED run` (interpret) payload_check | 42 (PASS) — tree-walker is correct |
| `$SEED run` (JIT/default) payload_check | 5 (DEFECT B, open) |
| stage4 `run m4` (struct x=7) | nil-receiver core (DEFECT A, open) |
| stage4 `run payload_check` | core (DEFECT A + env family, open) |
| stage4 `run p1`/`p2` (val x=5 / a+b) | silent / "invalid operands" (#107 env family, open) |

**Net seed change landed: ZERO** (both fixes reverted; seed stays healthy at the
task117 state). Repros: `scratchpad/{payload_check,p1_valscalar,p2_add,m4,
b_unwrap,b_some,enumdict,enumdict2,enumdict3}.spl`. Diagnostic binaries (isolated
cache): `scratchpad/stage4_ctrl117` (healthy baseline), `scratchpad/stage4_probeA`.
Seed with reverted source: rebuild from HEAD or reuse task117.

## Task #45 (2026-07-04) — source-driven verification: fix confirmed correct in source; deployed-binary gap is the SAME iteration-22 divergence, not a new bug

Task #45 asked to verify the "@cfg arch-variant symbol collision (last-write-wins)"
fix from source, independent of the deployed binary (`bin/simple run
scratchpad/cfg_arch_dispatch_repro_b.spl` still prints `arm64`/FAIL — confirmed,
baseline reproduces on this deployed binary and under
`SIMPLE_EXECUTION_MODE=interpret` identically).

### Two candidate "fix" commits — only one is real
- `d4ae10aeb3c` "fix(interpreter): evaluate @cfg conditions at registration time
  (#45)" touches `src/app/interpreter/module/evaluator.spl`
  (`evaluate_module`/`cfg_decorators_active`). **This is dead code**:
  `grep -rn "evaluate_module(" src/ test/` finds zero call sites outside the file
  itself and its `__init__.spl` re-export, and its item types (`Node`/`FunctionDef`
  with a `.decorators` field, a `Decorator` struct) match no struct/enum defined
  anywhere in the `.spl` tree — `src/app/interpreter/core/eval.spl`'s `eval_stmt`
  (the one real caller chain from `src/app/interpreter/main.spl`) doesn't even have
  a Function-statement arm. `bin/simple run` never touches `src/app/interpreter/*`.
- `cb8d9df703558` "fix(frontend): activate @cfg stripping (was inert) + native
  host arch/os detection" (one day earlier) is the real, LIVE fix, confirming this
  section's own "candidate (a)" hypothesis: `src/compiler/10.frontend/frontend.spl`
  had a local `fn preprocess_conditionals(source): source` passthrough that
  bare-name-shadowed its own `use compiler.core.parser_preprocessor.
  {preprocess_conditionals}` import, so stripping was inert and (per that commit's
  own message) "the FIRST-defined won" — exactly the order-B symptom. Fixed by
  delegating to the uniquely-named `_pp_preprocess_conditionals` so the shadow
  can't happen. Traced live call chain: `bin/simple run` -> `cli_run_file` ->
  `interpret_file` (`driver_api_interpret.spl`) -> `CompilerDriver.compile()`
  (`driver.spl`) -> `parse_full_frontend` (`frontend.spl:39`, calls
  `preprocess_conditionals` before parsing) -> HIR -> `InterpreterBackendImpl`.

### Source-driven spec: PASS — added to `test/01_unit/compiler/semantics/preprocessor_when_cfg_spec.spl`
New `describe "Task #45 residual — same-name arch dispatch (source-driven)"`
imports `compiler.frontend.frontend.{preprocess_conditionals}` (the exact
function `cb8d9df703558` fixed) directly from source and drives it with same-name
`@cfg(x86_64)`/`@cfg(arm64)` `arch_name()` pairs in both declaration orders, plus
an `@when(arm64)`/`@when(x86_64)` block-form pair (residual sweep below). All 3
new assertions PASS via `bin/simple test` (18/0 total in the file, ~850ms, no
OOM) — **the fix is correct in current source**: `preprocess_conditionals` keeps
only the host-matching variant regardless of declaration order, in both the
`@cfg` and `@when` forms.

### Interpret-mode cross-check
| mode | repro_a (x86_64 first) | repro_b (arm64 first) |
|---|---|---|
| default (`bin/simple run`) | PASS (`x86_64`) | **FAIL** (`arm64`) |
| `SIMPLE_EXECUTION_MODE=interpret` | PASS (`x86_64`) | **FAIL** (`arm64`) |

Both modes behave identically — consistent with the shared `parse_full_frontend`
front door for both JIT and interpret (`driver.spl` phase5 dispatch), so this
isn't an interpret-vs-JIT-specific gap.

### @when sibling-path residual: same shared mechanism, no NEW gap found
`cfg_eval_key_value`/`cfg_detect_arch` (`compiler.core.cfg_platform`) is shared
between the per-declaration `@cfg` pass and the block-scoped `@when` pass inside
`_pp_preprocess_conditionals`. Repro (`scratchpad/cfg_when_dispatch_repro.spl`,
`@when(arm64)`/`@when(x86_64)` block form, arm64 first) reproduces the identical
order-dependent symptom on the deployed binary (`arch_name() = arm64`, FAIL) —
but the source-driven spec assertion above proves the CURRENT
`preprocess_conditionals` already handles this same-name `@when` case correctly.
So this is not a distinct/unfixed bug: it is the same deployed-binary gap as
`@cfg`, not a separate residual.

### The deployed-binary gap is this doc's own iteration-22 "gate NOT closed" divergence, not new
This section's "Iteration 22" already proved the preprocessor is "verifiably
CORRECT... when compiled by the seed and run standalone" but produces an
unfiltered result "only on the 993-module self-hosted binary" (candidates (a)
same-bare-name collision — now resolved/ruled out by the `cb8d9df703558` fix
landing cleanly — vs (b) a `Module.functions: Dict<text, Function>` duplicate-key
overwrite misbehaving at full self-host scale, independent of preprocessing).
Task #45's deployed-binary repro failures are that same open item, not a new one:
the currently-deployed `bin/simple` predates `cb8d9df703558` and/or still hits
divergence (b) at full scale. **Verification-only outcome: no code change made
here** — fix is confirmed correct from source; final closure is gated on a
redeploy (fresh self-hosted rebuild) plus resolving iteration 22's (b) if the
divergence persists post-redeploy. Repros: `scratchpad/cfg_arch_dispatch_repro_a.spl`,
`_repro_b.spl`, `_repro_spaced.spl`, `cfg_when_dispatch_repro.spl`,
`cfg_when_dispatch_repro_a.spl`.
