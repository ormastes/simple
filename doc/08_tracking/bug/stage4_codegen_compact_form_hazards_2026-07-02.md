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

## Layer 3 (OPEN — root-caused 2026-07-02, iteration 5): enum struct-payload extraction returns inline garbage

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
