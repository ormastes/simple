# Task #168 (native side): operator overloading on struct operands — report

Worktree: `/tmp/wt_opover` @ f10db44f0f4 (GREEN base). Single file changed:
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (+126 lines, one site: the
`case Binary(op, ...)` generic arm in `lower_expr`). Patch: `scratchpad/op_overload.patch`.

NOTE (coordinator): origin main HEAD moved to ed26f0f0159 during this task (outage
revert). Base-sensitivity flags at the bottom.

## Method-name convention (checked first)

Repo convention is Python-style dunders: `__add__`, `__sub__`, `__mul__`, `__div__`,
`__eq__`, `__lt__`, `__gt__` — established by:
- `test/01_unit/compiler/newtype_ops_spec.spl` (#LANG-043, newtype auto-derive)
- parser auto-derive for `newtype` (`10.frontend/core/_ParserDecls/enum_module_body.spl:577-627`)
- `@derive(Eq)` generates `__eq__` (`fn_struct_decls.spl:472-497`)
No `__le__`/`__ge__`/`__ne__` anywhere in the repo; the 7 ops above are the full set.

## Characterization (BEFORE the fix), native `--entry` path

Program shape: `struct V: val x: i64` + `impl V: fn __op__(self, o: V) -> ...` + `val c = a OP b`.

| Operator | Before fix | Detail |
|---|---|---|
| `+` | SILENT-WRONG build, runtime SIGBUS/garbage | builds clean; `a + b` integer-ADDs the two struct POINTERS; `c.x` derefs garbage → SIGBUS (exit 135) |
| `==` | SILENT-WRONG | raw `icmp eq` on pointer bit patterns → always false for distinct values regardless of content |
| `<` | SILENT-WRONG | raw pointer compare — allocation-order dependent garbage |
| `*` | SILENT-WRONG build, runtime crash/garbage | pointer multiply |

Root cause: struct values on the native path are aggregate POINTERS
(`lower_struct_construct` → `emit_aggregate`), and the generic Binary arm in
`expr_dispatch.spl` fell through to `emit_binop` (raw i64 op on the pointer words).
HIR `.type_` is nil on this path, so no upstream layer ever routed the op to the impl
method. Interpreter oracle unusable (seed-gated `__add__` SIGSEGV) — all expected
values below are hand-computed BY CONSTRUCTION.

## Scope achieved: 1 (FULL dispatch) + loud-fail backstop

Wiring site: `lower_expr` `case Binary`, generic (`case _`) arm, immediately after both
operands are lowered, BEFORE the string-concat/str-eq/float interceptions:

1. Detect a struct operand: the operand local's MIR type must be `MirTypeKind.Struct`
   AND its name must be registered in `struct_value_syms` (the #156/#166 registry —
   construction sites, self-param copies, nested-field reads).
2. Map op → dunder (`Add→__add__ … Gt→__gt__`; 7 ops, matching the repo convention).
3. Resolve `"{Struct}::{dunder}"` in `struct_method_syms` (module_lowering's
   impl-derived registry, built for #156), honoring `struct_method_ambiguous` — the
   exact same guard set the Unresolved MethodCall fast dispatch
   (`method_calls_literals.spl`) uses. Emit a direct call
   `__op__(left, right)` with `resolved_call_return_type`.
4. Result registration: the call result's local is registered back into
   `struct_value_syms` (declared return type if Named; else operand's struct name for
   arithmetic dunders, which return Self by convention) so `c.x`/`c.y` after
   `val c = a + b` resolve the correct field index instead of defaulting to 0.
5. Backstop (loud-fail, replaces the old silent-wrong): a struct operand with NO
   matching (or an ambiguous) dunder now emits
   `self.error("unresolved method call: operator overload for struct {S} (no matching …)")`
   — prefix `unresolved method call:` is already allowlisted in `_mir_error_is_fatal`
   (`80.driver/driver_pipeline.spl:73`). Verified empirically: build exit 1, NO binary
   emitted, error printed. No loud→silent conversion anywhere.

### Two collision hazards found & guarded during implementation

- **LocalId cross-function collision (real, hit in testing):** `struct_value_syms` is
  keyed by LocalId but local numbering restarts per function. A plain `i64` local in a
  later function (`r * r` inside an unrelated `area()` fn) numerically collided with a
  stale `Vec2` entry from `main`, falsely triggering struct dispatch. Fix: gate the
  name lookup on the local's own MIR type being `Struct(_)`. Without this gate the
  patch would have broken arbitrary integer arithmetic in multi-function programs.
- **Bare-name link ambiguity:** reused `struct_method_ambiguous` — if two structs each
  define `__add__`, the bare name is ambiguous (backend links direct calls by bare
  name) and dispatch refuses, falling to the loud error instead of silently calling
  whichever body won the link. Same accepted #156 limitation as named methods.

## Battery (native output vs hand-computed; native print has no newlines)

| Test | Program | Expected (by construction) | Native output | Verdict |
|---|---|---|---|---|
| add | `V(3) + V(4)`, print `c.x` | 7 | `7` | PASS |
| eq in if | `V(3)==V(3)` →1, `V(3)==V(4)` →0 | 1,0 | `10` | PASS |
| mul + lt + plain i64 | `V(3)*V(4)`→12; `a<b`→1; `b<a`→0; plain `5+6`→11 | 12,1,0,11 | `121011` | PASS (i64 ops stayed native — no regression) |
| no dunder impl | `a + b` with no `__add__` | loud build fail | exit 1, no binary, `unresolved method call: operator overload for struct V …` | PASS |
| 2-field add, locals-first | `Vec2(1,2)+Vec2(3,4)`; cx,cy | 4,6 | `46` | PASS (field-order registration works) |
| MULTI-CONSTRUCT | Vec2 `__add__`+`__eq__`, cx,cy, `a==b`→0, `a==Vec2(1,2)`→1, `10+20`→30, match: Circle(2)→12, Square(5)→25 | 4,6,0,1,30,12,25 | `4601301225` | PASS |

### Pre-existing gap (NOT introduced; flagged per repo rule)

`print(c.x); print(c.y)` directly on a CALL-RETURNED struct: first read correct, second
garbage (`4` + junk). Verified with a PLAIN method call `a.add_method(b)` on the
UNPATCHED behavior path — identical failure. Root: the call-result struct pointer is
not preserved across an intervening call (backend regalloc/spill; 70.backend is owned
by a parallel lane, not touched). Workaround: read fields into locals before calling
(`val cx = c.x` …), which is what all passing tests use. Operator results now have
exact parity with written-out method-call results — same bug, same workaround.
**Concrete bug to file: "native: call-returned struct pointer clobbered by intervening
call; second field read garbage" (repro: p7/p10 shapes above).**

## Smoke matrix

`sh scripts/check/native-smoke-matrix.shs` from /tmp/wt_opover (patched tree):
**total=15 pass=14 fail=1, codegen_fallback_hits=0** — the single FAIL is
`option_nil_check` (rc got=1 want=7), the one allowed failure. GATE MET (>=14/15,
0 fallback hits, only allowed fail). Notably `struct_field`, `enum_match`,
`arith_fn_call`, `string_concat_len` all PASS — no regression from the new
Binary-arm interception.

## Base-sensitivity check against ed26f0f0159 (VERIFIED)

- `git apply --check` of `scratchpad/op_overload.patch` on a fresh ed26f0f0159
  worktree: **applies cleanly**.
- Dependencies present on that base: #156 registries (`struct_method_syms` in
  `mir_lowering_types.spl`) and the `unresolved method call:` fatal prefix in
  `driver_pipeline.spl` `_mir_error_is_fatal`. No blockers found; functional
  re-verification (battery re-run) still recommended since apply-clean is not
  behavior-proof.
