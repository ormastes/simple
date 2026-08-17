# Bare identifier in `case` position is an irrefutable binding, silently

- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  "Rust-seed fix" below). Still OPEN for the pure-Simple compiler seams
  (`50.mir/_MirLoweringExpr/expr_dispatch.spl` `lower_match_case`,
  `10.frontend/_FlatAstBridge/convert_nodes.spl` `convert_flat_pattern`).
- **Date:** 2026-08-01
- **Severity:** CRITICAL (silent wrong-code, whole-language scope)
- **Component:** language / pattern matching; lint `35.semantics/lint/match_exhaustiveness.spl`
- **Confirmed by:** execution on `src/compiler_rust/target/bootstrap/simple` (154MB, LLVM build)

## Summary

A bare identifier in `case` position that is **not a variant of the scrutinee's
enum type** does not produce a compile error and is not a dead arm. It parses as
an **irrefutable binding pattern**: it matches EVERY remaining value, binds it to
a local of that name, and runs that arm's body. Every subsequent arm — including
`case _:` — becomes unreachable and is silently dropped.

This is not limited to typo'd variants. A **defined, in-scope `val` constant**
in `case` position is also treated as a binding, not as a constant pattern. The
compiler consults the scrutinee enum's variant set and nothing else; consts are
never consulted.

Nothing is reported: no error, no warning, no lint. The program simply computes
the wrong answer.

## Reproduction (both probes include a deliberately-failing SENTINEL row so the
harness is provably falsifiable)

### Probe A — unknown identifier vs. an enum

```
enum Color:
    Red
    Green
    Blue(shade: i64)

fn classify(c: Color) -> text:
    match c:
        case Color.Red: return "RED"
        case NotAVariant: return "BOGUS-ARM-CAPTURED"   # <-- no such variant
        case Color.Green: return "GREEN"
        case _: return "WILDCARD"
```

Observed (`simple probe_casearm.spl`), expectations written assuming the bogus
arm is inert:

```
--- CONTROL (no bogus arm) ---
PASS  control(Red) = RED
PASS  control(Green) = GREEN
PASS  control(Blue) = WILDCARD
--- PROBE (expectations assume bogus arm is INERT / dead) ---
PASS  classify(Red) = RED
FAIL  classify(Green) = BOGUS-ARM-CAPTURED  (expected GREEN)
FAIL  classify(Blue) = BOGUS-ARM-CAPTURED  (expected WILDCARD)
--- SENTINEL (deliberately wrong expectation; MUST report FAIL) ---
FAIL  sentinel = RED  (expected THIS-EXPECTATION-IS-WRONG)
```

The control rows pass and the sentinel fails, so the harness is live. `Red` still
matches because its arm precedes the bogus one; `Green` and `Blue` are both
swallowed. `case _:` is dead. **Compilation emits no diagnostic at all.**

### Probe B — const in `case` position (the ws_parser shape)

```
val WS_OPCODE_TEXT: i64 = 1
val WS_OPCODE_BINARY: i64 = 2
val WS_OPCODE_CLOSE: i64 = 8

fn dispatch(opcode: i64) -> text:
    match opcode:
        case WS_OPCODE_TEXT: return "TEXT"
        case WS_OPCODE_BINARY: return "BINARY"
        case WS_OPCODE_CLOSE: return "CLOSE"
        case _: return "UNKNOWN"
```

Observed:

```
PASS  opcode=1 TEXT -> TEXT
FAIL  opcode=2 BINARY -> TEXT  (expected BINARY)
FAIL  opcode=8 CLOSE -> TEXT  (expected CLOSE)
FAIL  opcode=0 CONTINUATION -> TEXT  (expected UNKNOWN)
FAIL  opcode=99 garbage -> TEXT  (expected UNKNOWN)
--- SENTINEL (deliberately wrong; MUST FAIL) ---
FAIL  sentinel -> TEXT  (expected NEVER-EQUAL)
```

`opcode=1` "passes" only by coincidence — the first arm captures everything.
**Every WebSocket frame is dispatched as TEXT.** This shape is live in three
copies of `ws_parser.spl` (see table).

## Precise rule (as implemented)

For a bare identifier `N` in `case` position:

1. If `N` is a variant of the scrutinee's enum type → variant pattern. Correct.
2. Otherwise → **irrefutable binding pattern**. Silently catches everything.

Step 2 has no guard. Constants, typo'd variants, variants of a *different* enum,
and variants that exist only in the Rust seed's AST all land in step 2.

## Victims already fixed today (commit `35ad8595c8ac` and siblings)

| File | Symptom |
|---|---|
| `wat_codegen.spl` `translate_const` | `case Unit:` / `case Nil:` swallowed Zero/Tuple/Array/Struct; emitted NOTHING |
| `wat_codegen.spl` `translate_call` | `case Constant(name)` / `case Use(local_id)`; no call emitted |
| `wat_codegen.spl` `emit_operand` | nothing pushed to the WASM value stack |
| `tco.spl:127` `is_self_call` | `case Constant(...)` / `case FunctionRef(...)` ALWAYS returned false — tail-call optimization was silently dead for every function in the compiler |
| `isel_x86_64.spl`, `isel_aarch64.spl` | `mirconstvalue_Str` undefined; arm never selected |

Note `tco.spl` and `isel_*` show why a name-existence grep is insufficient:
`Constant` and `FunctionRef` *are* real variants — of a different enum.

## Sweep results (2026-08-01)

Method: harvest every `case <BareCapitalizedIdent>` arm under `src/**` (excluding
`vendor/**`), then test the identifier against the union of all `.spl` enum
variant names, all declared type names, and every `.Name` used in qualified
position. Counts via `/usr/bin/grep` (default `grep` here is ugrep).

| Bucket | Count |
|---|---|
| Bare `case <Capitalized>` arms scanned | 20,505 |
| **CONFIRMED — identifier exists nowhere in any `.spl` as a variant/type/qualified name** | **85** (60 distinct identifiers, 15 files) |
| ...of those, also absent from the Rust seed's enums | 70 |
| UNRESOLVED — name exists somewhere, but **not verified against the scrutinee's type** | 20,360 |

**The 85 are a floor, not the true total.** The `tco.spl`-class defect (a real
variant name belonging to the wrong enum) is invisible to name-existence
matching and sits somewhere inside the 20,360 unresolved arms. Only a
scrutinee-type-aware check can resolve those — which is precisely why the
deliverable is a compiler-side diagnostic rather than a grep.

Two additional sweep caveats, both found and corrected mid-sweep:
- `pub enum X:` was initially missed (regex anchored on `^enum`), inflating the
  count to 905.
- Multi-line variant declarations (e.g. `InlineAsm(` with lowercase continuation
  lines) terminated the enum-body state machine early, losing every variant
  declared after them. Corrected by ending an enum body only on a real dedent to
  column 0.

### Confirmed hits, in full

| File | Line | Arm |
|---|---|---|
| `src/app/interpreter/core/contract.spl` | 114 | `case ContractOld(inner):` |
| `src/app/interpreter/core/contract.spl` | 182 | `case ContractOld(inner):` |
| `src/compiler/10.frontend/desugar/desugar_async.spl` | 56 | `case State0: ...` |
| `src/compiler/10.frontend/desugar/desugar_async.spl` | 57 | `case State1(...): ...` |
| `src/compiler/10.frontend/desugar/desugar_async.spl` | 58 | `case State2(...): ...` |
| `src/compiler/10.frontend/desugar/poll_generator.spl` | 142 | `case State0:` |
| `src/compiler/10.frontend/desugar/poll_generator.spl` | 216 | `case State1(a, future):` |
| `src/compiler/30.types/type_system/bidirectional.spl` | 133 | `case IfExpr(let_pattern, condition, then_branch, else_branch):` |
| `src/compiler/30.types/type_system/bidirectional.spl` | 461 | `case ValBinding(name, type_annotation, initializer):` |
| `src/compiler/30.types/type_system/bidirectional.spl` | 485 | `case VarBinding(name, type_annotation, initializer):` |
| `src/compiler/30.types/type_system/expr_infer_ops.spl` | 222 | `case ChannelRecv:` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 161 | `case IfExpr(let_pattern, condition, then_branch, else_branch):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 179 | `case VecLiteral(elements):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 371 | `case UnwrapOr(expr, default):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 381 | `case UnwrapElse(expr, fallback_fn):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 392 | `case UnwrapOrReturn(expr):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 417 | `case OptionalMethodCall(receiver, method, args):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 429 | `case CastOr(expr, target_type, default):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 435 | `case CastElse(expr, target_type, fallback_fn):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 440 | `case CastOrReturn(expr, target_type):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 447 | `case MacroInvocation(name, args):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 453 | `case Spread(expr):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 457 | `case DictSpread(expr):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 464 | `case FunctionalUpdate(target, method, args):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 474 | `case ContractResult:` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 478 | `case ContractOld(expr):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 497 | `case DoBlock(stmts):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 505 | `case GridLiteral(rows, device):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 515 | `case TensorLiteral(dtype, dims, mode, device):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 51 | `case TypedInteger(_, suffix):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 520 | `case BlockExpr(kind, payload):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 530 | `case I18nTemplate(_, _, _):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 533 | `case I18nRef(_):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 64 | `case TypedFloat(_, suffix):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 74 | `case TypedString(_, _):` |
| `src/compiler/30.types/type_system/expr_infer.spl` | 95 | `case ExprPart(e):` |
| `src/compiler/30.types/type_system/_StmtCheck/bindings_check.spl` | 216 | `case ForNode(for_stmt):` |
| `src/compiler/30.types/type_system/_StmtCheck/bindings_check.spl` | 219 | `case WhileNode(while_stmt):` |
| `src/compiler/30.types/type_system/_StmtCheck/bindings_check.spl` | 365 | `case EnumPattern(enum_name, variant, payload):` |
| `src/compiler/35.semantics/lint/primitive_api.spl` | 191 | `case Qualified(module_path, _):` |
| `src/compiler/35.semantics/lint/primitive_api.spl` | 204 | `case ExprInt(_): true` |
| `src/compiler/35.semantics/lint/primitive_api.spl` | 205 | `case ExprFloat(_): true` |
| `src/compiler/35.semantics/lint/primitive_api.spl` | 208 | `case SuffixedInt(_, _): false` |
| `src/compiler/35.semantics/lint/primitive_api.spl` | 209 | `case SuffixedFloat(_, _): false` |
| `src/compiler/35.semantics/lint/primitive_api.spl` | 249 | `case Qualified(module_path, _): path = module_path` |
| `src/compiler/50.mir/mir_aop_injection.spl` | 97 | `case Unwind:` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 422 | `case FAdd: builder.emit("f64.add")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 423 | `case FSub: builder.emit("f64.sub")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 424 | `case FMul: builder.emit("f64.mul")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 425 | `case FDiv: builder.emit("f64.div")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 426 | `case FEq: builder.emit("f64.eq")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 427 | `case FNe: builder.emit("f64.ne")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 428 | `case FLt: builder.emit("f64.lt")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 429 | `case FLe: builder.emit("f64.le")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 430 | `case FGt: builder.emit("f64.gt")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 431 | `case FGe: builder.emit("f64.ge")` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 458 | `case FNeg:` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 474 | `case SignExtend:` |
| `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | 530 | `case CondBranch(cond, then_target, else_target):` |
| `src/compiler/90.tools/desugar_async.spl` | 55 | `case State0: ...` |
| `src/compiler/90.tools/desugar_async.spl` | 56 | `case State1(...): ...` |
| `src/compiler/90.tools/desugar_async.spl` | 57 | `case State2(...): ...` |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl` | 141 | `case WindowEvent::CloseRequested:` |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl` | 145 | `case WindowEvent::Resized(width, height):` |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl` | 152 | `case WindowEvent::KeyEvent(key_code, pressed):` |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl` | 168 | `case WindowEvent::MouseButton(button, pressed):` |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl` | 177 | `case WindowEvent::Focused(focused):` |
| `src/lib/gc_async_mut/http/ws/ws_parser.spl` | 250 | `case WS_OPCODE_TEXT:` |
| `src/lib/gc_async_mut/http/ws/ws_parser.spl` | 258 | `case WS_OPCODE_BINARY:` |
| `src/lib/gc_async_mut/http/ws/ws_parser.spl` | 266 | `case WS_OPCODE_CONTINUATION:` |
| `src/lib/gc_async_mut/http/ws/ws_parser.spl` | 274 | `case WS_OPCODE_CLOSE:` |
| `src/lib/gc_async_mut/http/ws/ws_parser.spl` | 276 | `case WS_OPCODE_PING:` |
| `src/lib/gc_async_mut/http/ws/ws_parser.spl` | 278 | `case WS_OPCODE_PONG:` |
| `src/lib/nogc_async_mut/http/ws/ws_parser.spl` | 250 | `case WS_OPCODE_TEXT:` |
| `src/lib/nogc_async_mut/http/ws/ws_parser.spl` | 258 | `case WS_OPCODE_BINARY:` |
| `src/lib/nogc_async_mut/http/ws/ws_parser.spl` | 266 | `case WS_OPCODE_CONTINUATION:` |
| `src/lib/nogc_async_mut/http/ws/ws_parser.spl` | 274 | `case WS_OPCODE_CLOSE:` |
| `src/lib/nogc_async_mut/http/ws/ws_parser.spl` | 276 | `case WS_OPCODE_PING:` |
| `src/lib/nogc_async_mut/http/ws/ws_parser.spl` | 278 | `case WS_OPCODE_PONG:` |
| `src/lib/nogc_sync_mut/http/ws/ws_parser.spl` | 250 | `case WS_OPCODE_TEXT:` |
| `src/lib/nogc_sync_mut/http/ws/ws_parser.spl` | 258 | `case WS_OPCODE_BINARY:` |
| `src/lib/nogc_sync_mut/http/ws/ws_parser.spl` | 266 | `case WS_OPCODE_CONTINUATION:` |
| `src/lib/nogc_sync_mut/http/ws/ws_parser.spl` | 274 | `case WS_OPCODE_CLOSE:` |
| `src/lib/nogc_sync_mut/http/ws/ws_parser.spl` | 276 | `case WS_OPCODE_PING:` |
| `src/lib/nogc_sync_mut/http/ws/ws_parser.spl` | 278 | `case WS_OPCODE_PONG:` |

### Highest-value clusters in that list

- **`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/http/ws/ws_parser.spl`
  (18 arms)** — `match header.opcode:` with `case WS_OPCODE_*:` const arms. Per
  Probe B, every frame dispatches as the first arm. This is live library code,
  not compiler internals. Highest user-facing impact in the list.
- **`src/compiler/70.backend/backend/wasm/wat_codegen.spl` (13 arms)** — the
  integer-op arms (`Add`, `Sub`, ... `BitXor`) are real variants, then
  `case FAdd:` is not. Every operand reaching `FAdd` or later — including
  `FNeg`, `SignExtend`, `CondBranch` and the wildcard — emits `f64.add`. This
  file was partially fixed today; the float-op block survived.
- **`src/compiler/30.types/type_system/expr_infer.spl` (~22 arms)** — arms named
  for `VecLiteral`, `TypedInteger`, `IfExpr`, `UnwrapOr`, `CastElse`, `DoBlock`,
  `MacroInvocation` etc. These exist as variants in the Rust seed's
  `parser/src/ast/nodes/core.rs` but not in any `.spl` enum. The first such arm
  captures every expression form the earlier arms did not.
  **ESCALATED 2026-08-01 — see
  `doc/08_tracking/bug/expr_infer_matches_struct_against_enum_variants_2026-08-01.md`.**
  Audit of these 22 found the defect is one level up: `infer_expr` does
  `match expr:` on the **struct** `Expr` rather than `match expr.kind:` on
  `ExprKind`, so *all 63* top-level arms are dead — proven by execution, a
  constructor arm placed *above* the bare `case Nil:` is still swallowed. Only
  18 of 63 arm names are real `ExprKind` variants, and all 13 helper functions
  the arm bodies call (`engine_fresh_var`, `type_Str`, `env_contains`, ...) are
  undefined repo-wide. The module is not wired into the driver and has never
  executed; a per-arm fix would have changed nothing. Filed rather than
  rewritten.
- **`src/compiler/{10.frontend/desugar,90.tools}/desugar_async.spl`,
  `poll_generator.spl` (8 arms)** — `case State0/State1/State2:` in the async
  state machine.
- **`src/compiler/35.semantics/lint/primitive_api.spl` (6 arms)** — the lint
  subsystem itself.

## Interaction with a DISTINCT defect — do not conflate

Nested payload sub-patterns such as `Const(MirConstValue.Str(x), _)` **always
match and never bind** under native and JIT codegen. That is a separate bug
(payload sub-pattern lowering), tracked separately. The two compound: an outer
irrefutable binding hides the inner never-binding sub-pattern, so fixing one can
leave the other producing wrong values with no new symptom. When repairing any
arm from the table above, verify the payload bindings actually bind — do not
assume a corrected variant name is sufficient.

## Fix: diagnostic `MEXH006`

### Seam chosen: `src/compiler/35.semantics/lint/match_exhaustiveness.spl`

Justification:

1. **The information is already there.** `analyze_match` already collects every
   arm pattern, already builds `enums: {text: [text]}` (enum name -> variant
   names) from `DECL_ENUM`, and already performs reverse type inference from arm
   patterns (`infer_type_from_arms`). Determining "is this bare ident a variant
   of the inferred scrutinee type" needs no new analysis.
2. **The gap is already documented in the code and never closed.** Lines 268-275
   say verbatim: *"Could be an enum variant name or a binding variable... We
   resolve this below after type inference."* It is never resolved — the name is
   pushed into `covered_variants` unconditionally and the distinction is
   dropped. This bug is that unfinished sentence.
3. **Reverse inference beats grep.** Because the type is inferred from the
   *other* arms, the check catches the `tco.spl` class — a real variant of the
   wrong enum — which no name-existence sweep can see. That is the 20,360-arm
   unresolved bucket.
4. **Existing warning family and reporting path.** `MEXH001`-`MEXH005` already
   exist with severity, code, hint and `fmt()`; `MEXH006` needs no new plumbing.
5. **Not the type checker.** Making this a hard error in `30.types` changes
   pattern semantics and would need a bootstrap rebuild plus a migration of all
   85+ sites at once. The lint lands the signal immediately and can be promoted
   to a hard error once the sites are clean.

### Rule

Emit `MEXH006` when a bare `case <Ident>` (or `case <Ident>(...)`) arm satisfies
all of:

- the identifier is not `_`;
- the identifier's first character is uppercase, **or** the identifier is
  `SCREAMING_SNAKE_CASE` (catches the const case in Probe B);
- the scrutinee type is known **and** the identifier is not among that type's
  variants — or the scrutinee type is unknown and the identifier is not a
  variant of any known enum.

Scrutinee type is resolved in three escalating steps:

1. `infer_scrutinee_type` — direct, from the scrutinee expression.
2. `infer_type_from_arms`, fed only the arm names that are variants of *some*
   enum. The existing helper requires every name to belong to the candidate
   enum (`is_subset_of`), so a single bogus name makes it return `""` — the
   defect hiding itself. Filtering to known-good names first removes that.
3. `_mexh_infer_owner_enum` — **majority vote**: score each enum by how many arm
   names it owns, take the unique winner backed by at least two arms. Returns
   `""` on a tie or weak support, so an unclear match is left alone.

Step 3 is what catches the `tco.spl:127` class, where the offending name
(`Constant`, `FunctionRef`) is a real variant of a *different* enum. Steps 1-2
and every name-existence grep are blind to it.

Simple's convention is Capitalized = type/variant, lowercase = binding. A
capitalized or SCREAMING identifier in `case` position is therefore almost
certainly an intended variant or constant, never an intended binding. Lowercase
identifiers are left alone — those are genuine bindings.

Message must name the consequence, not just the unknown name:

```
[MEXH006] ERROR: 'FAdd' is not a variant of enum 'MirBinOp' — this arm is an
irrefutable BINDING that matches every remaining value in 'translate_binop'
— rename to a real variant, or use a lowercase name if a binding was intended;
all arms after it (including '_') are unreachable
```

Severity `ERROR`, not `WARNING`: per repo precedent an unknown/unsupported case
must fail loudly rather than produce a plausible value. The four other MEXH codes
are advisory; this one reports code that is already wrong.

### Follow-up work (not in this pass)

- Promote `MEXH006` to a hard type-check error in `30.types` once all 85
  confirmed sites are repaired.
- Decide whether Simple should support **constant patterns** at all. Probe B
  shows `case WS_OPCODE_TEXT:` reads naturally and is silently wrong; either
  support const patterns or make this shape an error. Until then `MEXH006`
  flags it.
- Re-run the sweep with the `MEXH006` implementation to resolve the 20,360
  unverified arms; report the delta against the 85 found by grep.

## Implementation status (this pass)

**LANDED — lint diagnostic only. The language defect itself is still OPEN.**

- `src/compiler/35.semantics/lint/match_exhaustiveness.spl` — `MEXH006`
  detection: suspect collection in the arm loop, three-step scrutinee
  resolution, `_mexh_is_suspect_case_name`, `_mexh_is_variant_of_any`,
  `_mexh_infer_owner_enum`. Emitted **before** the `has_wildcard` short-circuit,
  because an irrefutable binding is worst precisely when a `case _:` follows it
  — that wildcard is what the binding kills.
- `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` — `MEXH006` registered
  at `LintLevel.Deny` (MEXH001-005 are `Warn`; this one reports code that is
  already wrong, not a style risk).

Validation: the decision logic was replicated verbatim in `probe_mexh006.spl`
and executed. 8 of 8 real rows pass, including the `wat_codegen` shape, the
`tco.spl` wrong-enum shape, the lowercase-binding negative case, and dedup; the
deliberately-wrong SENTINEL row is the only failure, so the harness is live.

Compile check: `simple compile` on the edited file reports the pre-existing
`cannot compile to standalone SMF: 32 function(s) require the interpreter`. The
**same error with the same count** appears when the pristine origin content is
compiled at the same path, so the edit introduces no new failure and none of the
three added functions is interpreter-bound.

Staleness: both edited files were byte-identical to the fresh origin tip before
editing, re-verified across two fetches while origin moved. Nothing was reverted.

### Real fix, deferred (needs a rebase first)

The authoritative seam is `lower_match_case` in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`. It already computes
`owner_count` from `self.enum_variant_index` and promotes `Binding` -> `Enum`
only when `owner_count == 1`. The missing branch is `owner_count == 0` with a
capitalized name, which should be a hard error instead of falling through to
`Binding`. The lexical fallback is `convert_flat_pattern` in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:1181-1185`, where a
bare `EXPR_IDENT` becomes `PatternKind.Binding(nm, false)` unconditionally.

**That file was not touched this pass because the working copy is BEHIND
origin there** — origin carries a +102-line fix (`dict_get_preserve_flat_nil`,
bug `native_dict_get_miss_returns_zero_not_nil_2026-07-28`) that editing from
current WC content would delete. Rebase before taking that seam.

## Adjacent defect found while implementing (separate, needs its own triage)

A character-range test silently evaluates to `false` when the operand comes from
`.substring()` and is combined with `and`:

```
fn f(name: text) -> bool:
    val first = name.substring(0, 1)
    first >= "A" and first <= "Z"     # always false, for every input
```

Measured on the bootstrap seed 2026-08-01. `"F" >= "A"` used directly in an
`if` with plain parameters is correct, so the fault involves the
substring-derived operand in the compound expression, not `>=` itself.
Additionally, `.to_text()` on such a bool inside the function printed `false`
for a comparison that is true — so a debug print here *lies*, which is how this
nearly produced an inert lint that looked correct.

### ROOT-CAUSED AND FIXED 2026-08-01 — and the triage above was wrong twice

Fixed in `6469d70eb4e`
(`src/compiler_rust/compiler/src/codegen/instr/core.rs:358-404`). Regression
spec: `test/01_unit/bugs/text_ordering_cmp_spec.spl`.

**Real cause.** Under the **Cranelift JIT only**, text ordering (`<` `<=` `>`
`>=`) compared the operands' heap handle **ADDRESSES** instead of their byte
content whenever codegen could not statically prove that BOTH operands were
`TypeId::STRING`. The 2026-07-22 P0 fix had added the correct `rt_text_cmp_any`
arm but guarded it with `&&`, so a runtime-produced text (a `.substring()`
result, whose vreg type is not threaded) failed the guard and fell back into the
raw-integer `icmp` arm. `==` was never affected, because `Eq`/`NotEq` already
fall back to the tag-aware `rt_native_eq`; ordering had no counterpart. That
asymmetry is exactly why the failure read as "`>=` behaving like `==`".

**Two corrections to the triage above — both matter more than the fix.**

1. **`and` and `.substring()` were red herrings.** Neither is required. Because
   the comparison result depended on *allocation addresses*, it was deterministic
   for a given program but flipped when unrelated, unconnected code was added or
   removed. A single-call, no-`and`, no-helper repro fails; the *same* code with
   one extra function present passes. That instability is what made the original
   bisect land on `and`.

2. **`.to_text()` does NOT lie. Bug #2 is FALSIFIED.** Re-measured with a probe
   that prints a branch side-effect (distinct strings from the `if` and `else`
   arms) *alongside* `.to_text()`, on both engines, with a deliberately-failing
   sentinel row. `branch=` and `to_text=` **agreed on every row of every run,
   including every wrong one**. `to_text` faithfully reported `false`; the
   comparison had genuinely computed `false`. There is one bug here, not two, and
   no evidence produced by printing a bool was invalidated.

   This distinction is worth keeping: "the output lies" and "the computation is
   wrong" demand completely different responses, and only a branch side-effect
   can tell them apart. Note this is NOT the known
   `to_text`-on-erased-`Any`-bool defect; that one is distinct and still open.

**Verification** (seed rebuilt 2026-08-01 14:07, `SIMPLE_EXECUTION_MODE` =
`interpreter` and `jit`): all previously-failing repros now agree across both
engines, and the sentinel rows still report `FALSE`, so the probe stayed
falsifiable.

**Open follow-up — the regression spec cannot reach the engine that broke.**
`test/01_unit/bugs/text_ordering_cmp_spec.spl` picks the right operand shapes
(receiver arriving as a fn parameter, so no static typing survives), but it runs
on the `bin/simple test` path, which hard-defaults to the tree-walk interpreter
and has no JIT variant (`.claude/rules/testing.md`, "run and test are DIFFERENT
ENGINES"). The interpreter was correct throughout this bug, so that spec would
have stayed green for the entire defect window and would stay green through a
reintroduction. A genuine guard needs a JIT-path
(`SIMPLE_EXECUTION_MODE=jit bin/simple run`) assertion. Filed here rather than
left implicit.

**Blast radius and full root-cause writeup:**
`doc/08_tracking/bug/jit_text_ordering_pointer_compare_2026-08-01.md` (~1,150
`src/**` sites; that doc is authoritative). An independent narrower sweep
(`/usr/bin/grep`, not the default ugrep; single-char-literal range checks across
`src/` + `test/` + `scripts/`) found **811 sites across 389 files** — same
population, tighter pattern. It lands in exactly the code that classifies
characters: `src/lib/common/validation.spl` (15),
`src/lib/common/json/parser.spl` (9), `src/lib/nogc_sync_mut/http/url.spl` (6),
hex decoding in `src/lib/gc_async_mut/http/common.spl` and
`src/lib/nogc_sync_mut/replay/process/checkpoint.spl`, the JS engine lexers, and
the compiler's own `src/compiler/10.frontend/core/interpreter/eval_calls.spl:116`.
All are fixed by the codegen change; no call-site edits are needed.

`_mexh_is_suspect_case_name` therefore uses set membership
(`"ABC...XYZ".contains(first)`), verified across `FAdd`, `Add`, `other`,
`WS_OPCODE_TEXT`, `_`, and `""`. A comment at the call site forbids
"simplifying" it back to a range comparison without re-measuring. This is
recorded rather than normalized silently, per the repo rule on workarounds.

## Artifacts

- Probe A: `probe_casearm.spl` (enum form)
- Probe B: `probe_constcase.spl` (const form)
- Sweep script and classified output: `sweep.sh`, `confirmed.txt`

## Disposition of the remaining 29 rows (2026-08-01, second pass)

`ws_parser.spl` (18), `wat_codegen.spl` (13) and `expr_infer.spl` (25) were
handled earlier. The 29 rows left were each checked against the **scrutinee's
actual type definition** and against **wiring** (importers anchored on
`use`/`import`/`export use` lines, never a bare basename grep). Result: **one
real, wired production defect; 13 harvester false positives; 15 rows inside
unwired islands.**

| Cluster | Rows | Wired? | Verdict |
|---|---|---|---|
| `50.mir/mir_aop_injection.spl` | 1 | **YES** — `80.driver/driver_pipeline_aop.spl`, `driver_aot_vhdl_output.spl`, 3 specs | **REAL — FIXED** (`33b57c515f39`) |
| `desugar/desugar_async.spl`, `90.tools/desugar_async.spl`, `poll_generator.spl` | 8 | n/a | **FALSE POSITIVE** — all 8 are inside `"""` docstrings |
| `compiler_rust/lib/std/examples/vulkan_gui_demo.spl` | 5 | no | **FALSE POSITIVE** — `case WindowEvent::CloseRequested:` is `::`-qualified, not a bare identifier; the file is Rust-syntax pseudocode (`::`, `\|e\| ...`, `println("{}", x)`) that cannot parse as Simple |
| `app/interpreter/core/contract.spl` | 2 | **no** — zero `use` lines in the file, zero importers, zero callers of `collect_old_exprs`/`substitute_old_exprs` | dead module |
| `35.semantics/lint/primitive_api.spl` | 6 | module yes, **these functions no** | phantom-AST island — see below |
| `30.types/type_system/{bidirectional,expr_infer_ops,_StmtCheck/bindings_check}.spl` | 7 | **no** — whole package is a closed island | phantom-AST island — see below |

### FIXED: `inject_after_error_advice` injected advice into EVERY block

`match block.terminator: case Unwind:` — `MirTerminator` is
`Goto/Ret/If/Switch/Unreachable/Abort/CallTerminator`; there is no `Unwind`.
The bare identifier bound irrefutably, so every basic block of every advised
function received an after-error advice call and the `case _:` pass-through was
dead. Note the *reported* symptom was wrong in the usual direction: the same
file's `apply_weaving_result` (`case Execution:` on `JoinPointKind`) looks
identical but is **correct** — `Execution` is a real variant. Measured, not
assumed.

Execution control, 4-block function (Ret / Abort / Goto / Unreachable):

```
before   ret=1  abort=1  goto=1  unreach=1     <- every block advised
after    ret=0  abort=1  goto=0  unreach=0     <- only the error exit
```

Fixed to qualified `case MirTerminator.Abort(_):`. `CallTerminator`'s `unwind`
edge is deliberately not a join point: the handler is the unwind TARGET block,
and injecting at the calling block would also fire the advice on the
normal-return path.

### Mechanism boundary, re-measured

A bare `case N:` swallows **only** when `N` is not a variant of the scrutinee's
enum. Verified by execution both ways:

```
enum JPK: Execution / FunctionCall / Error
bare arms   -> "exec call err"      (identical to qualified arms)
sentinel: a leading `case Unwind:`  -> "SWALLOWED SWALLOWED"
```

So the ~20,505 bare arms are not suspect as a class; only the name-resolution
failures are. Equally important: a row with a **payload** (`case Qualified(p,_):`,
`case ForNode(s):`) naming a nonexistent variant is *refutable* — it never
matches rather than swallowing. Those are dead arms, a real but different bug,
and the confirmed-85 list mixes both kinds.

### ESCALATED: two phantom-AST islands, same class as `expr_infer.spl`

Not repaired per-arm, for the same reason `expr_infer.spl` was not: the arm
names are the least of it, and a "fix" would be inventing a feature.

**`lint/primitive_api.spl` — the `raw_unit` sub-lint (6 rows).** Written against
an AST that does not exist. `is_unit_type`/`unit_type_short` do `match ty:` on
the **struct** `Type` (rule: must be `ty.kind`) and name `Qualified`/`Simple`,
neither of which exists anywhere in `src/compiler/**`; the real `TypeKind` is
`Named/Tuple/Array/Function/Optional/Reference/Atomic/Isolated/Union/Projection/
Infer/Error`. `is_raw_primitive_expr` matches `Expr` not `Expr.kind` and names
`ExprInt`/`ExprFloat`/`SuffixedInt`/`SuffixedFloat` (none exist; `ExprKind` has
`IntLit`/`FloatLit` and no suffixed form at all). `check_call_site` reads
`param.ty` — `Param` has `has_type_`/`type_` — and takes `callee: FunctionDef`,
whose `params` field is `[text]`, i.e. carries no types whatsoever. The group has
no caller outside the file; `test/01_unit/lib/unit/unit_raw_warning_spec.spl`
says "RED until `lint_raw_unit` + `lint_allow_list` + `check_call_site` land".
The rest of `primitive_api.spl` is wired via `lint/__init__.spl` and unaffected.

**`30.types/type_system/**` — `bidirectional` (3), `bindings_check` (3),
`expr_infer_ops` (1).** The package is a closed import island: every importer of
`checker`, `stmt_check`, `module_check`, `expr_infer*`, `bidirectional` is
*inside the package*, the only exceptions being `effect_pass` (genuinely wired
into `driver_hir_pipeline_lowering.spl`) and a `TypeError`-only import in
`90.tools/query_helpers.spl`. The driver's real inference is
`compiler.types.type_infer.*`. Inside the island the same phantom AST recurs:
`check_stmt(stmt: Node)` matches `ValBinding/Assignment/Return/If/Match/ForNode/
WhileNode/Loop/Break/Continue/Pass` while `ast.Node` has exactly
`Function/Struct/Class/Enum/Trait/Other`; `bind_pattern(pattern: Pattern)`
matches the struct, not `pattern.kind`, and names `EnumPattern` where
`PatternKind` has `Enum`. `expr_infer_ops.infer_unary` is the one near-miss —
`UnaryOp` is real and `Neg/Not/BitNot/Ref/RefMut/Deref` are correct — but
`case ChannelRecv:` (line 222) and `case Move:` (line 245) are not `UnaryOp`
variants, so `Transpose` and the tail are swallowed; its body also references an
undefined `has_args`. Left as-is with the island.

Recommended follow-up: run `MEXH006` over `src/**` once the pure-Simple
`bin/simple` is redeployed. The name-existence sweep cannot see the
`tco.spl`-class defect (a real variant of the *wrong* enum), which is where the
remaining 20,360 unresolved arms live.

## Rust-seed fix (2026-08-02) — both engines now refuse

The lint (`MEXH006`) reports; it does not stop the wrong code from running. The
seed's own two engines now refuse the shape outright.

### Why fixing one engine was not enough — measured, and it matters

The first attempt fixed only the HIR seam
(`hir/lower/stmt_lowering.rs` `lower_pattern_condition_stmt`), which is the
JIT/native lane. Measured result on Probe A's shape:

```
[jit-fallback] HIR lowering error: `case NotAVariant:` is not a variant ...
              : whole module dropped to the interpreter (~100-1000x slowdown)
RED
BOGUS      <- still the wrong answer
BOGUS
rc=0
```

The JIT refusal is **caught by the `[jit-fallback]` path**, which drops the whole
module to the tree-walk interpreter — which still had the defect. So the
"fix" bought nothing and cost a 100-1000x slowdown. A refusal on one engine of a
pair with automatic fallback is worse than no refusal at all. Both seams were
therefore changed together:

| Seam | Keyed on | File |
|---|---|---|
| JIT / native | subject's static `TypeId` | `hir/lower/stmt_lowering.rs` `lower_pattern_condition_stmt` |
| interpreter | runtime `Value::Enum` | `interpreter_patterns.rs` `Pattern::Identifier` |

The shared spelling predicate lives in one place so the two cannot drift:
`compiler/src/pattern_case_naming.rs` (`case_name_is_spelled_like_a_variant`,
with unit tests).

### Rule, deliberately narrow

Refuse only when ALL hold, so under-reporting is the failure mode:

- the subject resolves to an enum (static type on the HIR side, `Value::Enum` on
  the interpreter side), **and**
- that enum's variant list is known and **non-empty** (an empty list means the
  summary was never populated, not that the enum has no variants), **and**
- the identifier is not one of those variants, **and**
- the identifier is spelled `Capitalized` or `SCREAMING_SNAKE_CASE`.

Consequently a lowercase `case other:` is untouched, and **Probe B's const shape
(`match opcode: case WS_OPCODE_TEXT:`, subject `i64`) is deliberately NOT
reported here** — this seam cannot tell a const pattern from a binder without
const resolution, and a false positive would reject valid code. Probe B remains
open and is still the highest user-facing item; `MEXH006` continues to flag it.

### Verification (execution, not reading)

| Fixture | base binary | fixed binary |
|---|---|---|
| Probe-A shape (`case NotAVariant:`) | `RED / BOGUS / BOGUS`, **rc=0** | loud refusal, **rc=1**, both engines |
| lowercase `case other:` | `RED / BOUND` | `RED / BOUND` (unchanged) |
| bare `case Red:` where `Red` IS a variant | correct | correct (still a variant TEST) |
| qualified `case Color.Red/Green/_` | `10 / 20 / 30` | `10 / 20 / 30` |
| `c is Color.Red` | `1 / 0` | `1 / 0` |
| payload `case Shape.Line(n)` | binds `7`, and `3` | binds `7`, and `3` |

Regression fixture: `test/fixtures/compiler/bare_case_ident_binding_controls.spl`
— 14 rows, `BADCOUNT 0` on JIT **and** interpreter, `[jit-fallback]` = 0. It
guards the *opposite* direction (shapes that must keep working), because the
refusal aborts the module and cannot be a row in a running fixture.

Rust suite: `cargo test -p simple-compiler --lib` = **3457 passed / 118 failed**
against the 3455/118 baseline — the +2 are this change's own unit tests, and the
118 failure **name sets are byte-identical** (`diff`, not counts).
`-- hir:: compilability::` = **327 / 7**, exactly baseline.
