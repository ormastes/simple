# UI001 Unblock Plan — Field-Load Codegen Bug

**Status:** active — blocker identified, fix not yet applied
**Created:** 2026-04-18
**Owner:** TBD (compiler-internals task)
**Master plan:** `doc/01_research/ui_modernization_plan.md`
**Sister RFC:** `doc/05_design/compiler_rfc_ufcs.md` (audit history + dedup patches)

## Scope Boundary

This document is only about the compiler/self-host field-load bug that blocks
`UI001` verification.

It does **not** track the assistant/dashboard child-task or spawn-agent work.
That work is tracked separately in
`doc/08_tracking/todo/kairos_like_simple_mcp_llm_dashboard_follow_up_2026-04-15.md`.

## 1. What we're trying to verify

```
$ printf 'val x = WidgetNode.new("root", "panel")\n' > /tmp/test_ui001.spl
$ bin/simple lint /tmp/test_ui001.spl
/tmp/test_ui001.spl:1:1: warning: Raw string literal as WidgetNode kind — use WidgetKind.X.to_wire() [UI001]
  fix: available (use --fix to apply)
```

Currently fails. UI001/UI002/UI003 lint rules were added in Phase 8 of the
typed-core migration (committed in `05c2280ae6` — see
`src/compiler/90.tools/lint/main.spl:1049-1180`). The rule code is correct
(verified by `test/unit/compiler/lint_ui_rules_spec.spl`, 22/22 passing).
The blocker is in the compiler self-host.

## 2. Why it currently fails

Three problems chained together. Two are fixed; the third is the active blocker.

### 2.1 ✓ FIXED — UFCS resolver was stubbed

`src/compiler/35.semantics/resolve.spl:572` was a 3-line stub returning
`(module, [])`. Unstubbed in commit `8c091c140c` to construct an empty
`SymbolTable` + invoke `MethodResolver` with always-falls-through-to-UFCS
behaviour.

### 2.2 ✓ FIXED — Spurious method-dispatch ambiguity warnings

`declare_functions` in `src/compiler_rust/compiler/src/codegen/common_backend.rs:425-429`
intentionally double-registers each function (raw `Type.method` + mangled
`module__Type_dot_method`) for local-call resolution. The downstream
candidate-collection in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:258-269`
treated these as separate candidates and emitted
`[CODEGEN-AMBIGUOUS-METHOD]` for every dual-registered function.

Fixed in commit `ea8ec1f2b0` by adding a HashSet-by-FuncId dedup
*immediately before* the ambiguity warning fires (line 340-348 area,
preserving type-qualifier lookup at line 271-289 which needs both forms).

**Empirical effect**: ambiguity warnings on Stage 4 self-host
**154 → 6** (96% reduction). The 6 remaining are TRUE ambiguities
(`check_expr`, `emit_object`, `to_sdn`, `to_text` — distinct types
defining same method name).

### 2.3 ✗ ACTIVE BLOCKER — Wrong-typed field load in struct codegen

After §2.1 + §2.2, building Stage 4 succeeds and produces a 27.5MB
self-host binary. But `lint`/`check`/`format` commands in the new binary
fail with:

```
Runtime error: Function 'level' not found
Runtime error: Function 'line' not found
```

The `level`/`line` references are **field accesses** on the `Lint` and
`LintResult` classes (`src/compiler/90.tools/lint/main.spl:363, 401`),
not method calls. Initial guess (function dispatch failure) was wrong.

**Real bug class**: pinned down 2026-04-18 via minimal reproducer:

```
class Box:
    line: i32
    name: text
    fn show() -> text:
        self.line.to_string() + ":" + self.name

fn main() -> i32:
    val b = Box(line: 42, name: "hello")
    println(b.show())
    0
```

Built with the new self-host (1 compiled, 0 stubs in user code). Ran:

```
$ /tmp/field_repro
0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002:hello
```

Two facts established:
1. `self.name` (text) reads correctly — `:hello` is the right tail
2. `self.line` (i32) reads as f64 — the bytes are interpreted as a
   tiny float close to zero, then `.to_string()` formats it

The runtime "Function 'level'/'line' not found" error in lint is
downstream noise: after the wrong-type read, the `.to_string()` call
dispatches to the wrong implementation, eventually failing to find some
helper function in the resulting call chain.

## 3. Recommended fix path

### Step 1 — Trace struct field offset/type codegen

Likely failing layer in `src/compiler_rust/`:

- `src/compiler_rust/compiler/src/types/` — type-layout pass (struct
  field offset and width computation)
- `src/compiler_rust/compiler/src/codegen/instr/` — field-load IR
  emission (the load that should be a 32-bit integer load and isn't)

Investigation commands:
```
RUST_LOG=trace src/compiler_rust/target/bootstrap/simple native-build \
    --no-incremental --backend cranelift \
    --source /tmp --entry-closure --entry /tmp/field_repro.spl \
    --runtime-path src/compiler_rust/target/bootstrap \
    -o /tmp/field_repro 2>&1 | grep -E "Box|line|field|load" | head -30
```

### Step 2 — Apply fix

Likely fix shape: when emitting `LoadField(struct, field_index)`, ensure
the load's CL IR type matches the field's declared type
(`I32` for `i32`, `I64` for `i64`, `F64` for `f64`, `R64` for pointers).
A regression where all field loads use a fixed type (e.g., always F64)
would explain my repro's exact symptom.

### Step 3 — Verify with the minimal repro

After the codegen fix, rebuild the seed and Stage 4:

```
cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all
src/compiler_rust/target/bootstrap/simple native-build --no-incremental \
    --backend cranelift --source /tmp --entry-closure \
    --entry /tmp/field_repro.spl --runtime-path src/compiler_rust/target/bootstrap \
    -o /tmp/field_repro
/tmp/field_repro
# Expected: 42:hello
```

### Step 4 — Run full bootstrap chain

```
cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all
# Stage 2 → Stage 3 → Stage 4 (~30s each):
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

### Step 5 — Verify UI001 fires

```
printf 'val x = WidgetNode.new("root", "panel")\n' > /tmp/test_ui001.spl
bin/simple lint /tmp/test_ui001.spl
# Expected: warning fires with [UI001] code
```

## 4. Files committed in this session

UI typed-core migration (Phases 0–10 + Phase 11 prelude):
- `src/lib/common/ui/widget.spl` — `WidgetKind`/`LayoutKind` enums + 26 fluent methods on `WidgetNode`
- `src/lib/common/ui/color.spl` — typed `Color` with `from_hex`/`to_hex`/`to_rgba_css`
- `src/lib/common/ui/action.spl` — `Action`/`CommonAction`/`IntoAction`
- `src/lib/common/ui/theme_registry.spl` — dep-inversion hub
- `src/lib/common/ui/design_tokens.spl` — `Spacing`/`Radius`/`Elevation`/`SurfaceRole`/`TextRole`
- `src/lib/common/ui/{ios,glass}/{theme,builder,tokens,numeric_tokens}.spl` — Phase 7 module rename
- `test/unit/app/ui/wire_golden/wire_golden_spec.spl` — wire byte oracle (4/4)
- `test/unit/app/ui/{token_resolution,typed_action,responsive_widget,color}_spec.spl` — Phase 4-6 + 11
- `test/unit/compiler/lint_ui_rules_spec.spl` — Phase 8 lint rule logic (22/22)
- `src/compiler/90.tools/lint/main.spl:1049-1180` — UI001/2/3 implementations

Compiler infra:
- `src/compiler/35.semantics/resolve.spl:572` — UFCS partial unstub
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:340` — method-dispatch dedup

RFCs / docs:
- `doc/05_design/ui_typed_core_rfc.md` — master RFC
- `doc/05_design/compiler_rfc_{ufcs,bare_enum_literals,method_chain_fix}.md` — Phase 9 compiler RFCs
- `doc/05_design/ufcs_propagation_experiment.md` — Stage 4-6 propagation results
- `doc/01_research/ui_phase11_roadmap.md` — Phase 11+ tracking
- `doc/01_research/ui_remaining_strings_audit.md` — 8 stringly-typed surfaces remaining
- `.claude/skills/ui.md` + 6 other docs — typed authoring + fluent chain docs

## 5. Verification gates after the fix lands

| Gate | Command | Expected |
|---|---|---|
| Wire stability | `bin/simple test test/unit/app/ui/wire_golden/wire_golden_spec.spl` | 4/4 |
| Backend matrix | `bin/simple test test/unit/app/ui/backend_matrix_spec.spl` | 7/7 |
| IPC protocol | `bin/simple test test/unit/app/ui/ipc_protocol_spec.spl` | 15/15 |
| Token resolution | `bin/simple test test/unit/app/ui/token_resolution_spec.spl` | 45/45 |
| Typed actions | `bin/simple test test/unit/app/ui/typed_action_spec.spl` | 19/19 |
| Responsive | `bin/simple test test/unit/app/ui/responsive_widget_spec.spl` | 22/22 |
| Color codec | `bin/simple test test/unit/app/ui/color_spec.spl` | 50/50 |
| Lint logic | `bin/simple test test/unit/compiler/lint_ui_rules_spec.spl` | 22/22 |
| Field-load repro | `/tmp/field_repro` (after rebuild) | `42:hello` |
| UI001 fire | `bin/simple lint /tmp/test_ui001.spl` | UI001 warning |

## 6. Estimated effort

- Field-load codegen fix: medium-large (4–8 hours of compiler-internals
  tracing + targeted patch + bootstrap-chain verification)
- All UI follow-ups in `doc/01_research/ui_phase11_roadmap.md` after
  the field-load fix lands: incremental, can be done piecemeal

## 7. References

- `doc/01_research/ui_modernization_plan.md` — master plan
- `doc/05_design/ui_typed_core_rfc.md` — typed-core RFC (Phases 0–10)
- `doc/05_design/compiler_rfc_ufcs.md` — UFCS investigation + dedup patches
- `doc/01_research/ui_phase11_roadmap.md` — Phase 11+ items
- `feedback_sync_bundling_clobbers_commits.md` (memory) — git history hazard from sync skill
