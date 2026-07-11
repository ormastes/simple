# Bootstrap MIR: string interpolation `{expr}` printed literally, not evaluated

**Date:** 2026-07-11 · **Status:** OPEN — confirmed root cause in bootstrap desugaring strategy.
**Found:** Standalone compiled binary probe (dynamic_text_probe_result.md). When compiling
via `SIMPLE_BOOTSTRAP=1 native-build --backend=llvm-lib`, a string with interpolation syntax
prints the raw braces, e.g., `print("DYN_INTERP_{n}")` outputs `DYN_INTERP_{n}` instead of
`DYN_INTERP_42`.

## Failing construct (probe: `p3`)

```spl
fn main():
    val n = 42
    print("DYN_INTERP_{n}")
```

**Expected output:** `DYN_INTERP_42`
**Actual output (compiled bootstrap):** `DYN_INTERP_{n}`
**Actual output (interpreted):** `DYN_INTERP_42` ✓

The interpreter desugars correctly; the bootstrap-compiled lane prints the literal `{n}`.

## Variant test matrix

| Construct | Type | Status |
|-----------|------|--------|
| `print("DYN_INTERP_{n}")` where `n: i64 = 42` | simple var interp | ❌ BROKEN (literal braces) |
| `print("DYN_INTERP_{n}")` where `n: text = "TEXT"` | text var interp (untested) | ❌ expected BROKEN |
| `print("DYN_INTERP_{n + 1}")` where `n: i64 = 42` | expr interp (untested) | ❌ expected BROKEN |

## Root cause: HIR layer nullifies interpolations during SIMPLE_BOOTSTRAP

**File:** `src/compiler/20.hir/hir_lowering/expressions.spl` (lines 280-286)

```spl
val hir_interps = if (hir_expr_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1":
    nil  # <-- DISCARD INTERPOLATIONS DURING BOOTSTRAP
elif interps.?:
    self.lower_interpolation_list(interps)
else:
    nil
HirExprKind.StringLit(value, hir_interps)
```

When `SIMPLE_BOOTSTRAP=1`, the HIR layer unconditionally discards the interpolation list,
setting it to `nil`. This is the intentional bootstrap workaround (see Bug #136 note below).

## Evidence: MIR layer emits raw string when interps is nil

**File:** `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (lines 501-521)

```spl
case StringLit(value, interps_opt):
    # Bug #136: ... previously discarded and the raw literal (with `{...}` verbatim) emitted.
    var has_interps = false
    var interp_list: [HirInterpolation] = []
    if val il = interps_opt:
        interp_list = il
        if interp_list.len() > 0:
            has_interps = true
    if has_interps:
        self.lower_string_interpolation(value, interp_list)
    else:
        # Store string as constant; runtime resolves pointer
        var b = self.builder
        val dest = b.new_temp(MirType(kind: MirTypeKind.Opaque("str")))
        b.emit_const(dest, MirConstValue.Str(value), MirType(kind: MirTypeKind.Opaque("str")))
        self.builder = b
        dest
```

When `interps_opt` is `nil`, the MIR emits the string **as-is** via `emit_const`, preserving
the raw `{expr}` syntax verbatim (lines 517-520). The constant reaches the binary unchanged.

**Verdict (a) vs (b):** **(a) Never desugars** — HIR layer throws away interpolation
structures during bootstrap, so MIR sees `nil` and emits raw literal. No call to
`lower_string_interpolation()` is ever made in the bootstrap path.

## Disassembly confirmation (from dynamic_text_probe_result.md)

```
100000914: adrp x0, 0x100001000          ; load literal-data page
100000918: add  x0, x0, #0xa40           ; x0 = &"DYN_INTERP_{n}" (RAW, WITH BRACES)
10000091c: bl   _rt_print                ; CALL with raw pointer
```

No intervening instruction to substitute or evaluate `{n}`. The pointer points directly to
a `.rodata` string containing the literal characters `D`, `Y`, `N`, `_`, `I`, `N`, `T`, `E`, `R`, `P`, `_`, `{`, `n`, `}`.

## Impact

- **High:** Any compiled code (including error messages, user-facing strings with data
  substitution) using `"text {var}"` syntax prints garbage in bootstrap-compiled binaries.
- **Scope:** Affects stage-2/stage-3 bootstrap chain. Stage-4 uses self-hosted compiler
  (interps desugared correctly) but stage-1/stage-2 affected.
- **Relation to join() bug:** Same lane (bootstrap MIR codegen); sibling symptom class
  (expression not lowered). Cross-link: `stage4_compiled_dict_no_growth_2026-07-11.md`
  documents the `.join()` builtin silent-drop bug (also bootstrap MIR, also silent fallback
  to null/zero constant).

## Required fix

**Root choice:** During SIMPLE_BOOTSTRAP, either:

1. **Desugaring path:** Populate `hir_interps` normally (lines 281 → copy from `interps`);
   MIR will then call `lower_string_interpolation()` correctly. Requires confirming
   string-concat lowering works in stage-1/2 (likely does; p2 concat test passes).
2. **Constant-fold path:** If runtime concat is not available during early bootstrap,
   pre-evaluate literal interpolations at compile-time (where possible, e.g., constant
   operands like `"prefix_{42}"` → `"prefix_42"`).
3. **Staged path:** Move interpolation lowering to a post-HIR pass that is not gated
   by `SIMPLE_BOOTSTRAP`, so it fires for all codegen paths.

**Owner:** compiler 50.mir bootstrap desugaring strategy (20.hir layer implements the
gating; 50.mir layer implements the lowering). Current comment (Bug #136) suggests this
was a known workaround for an earlier bootstrap stage. Verify whether the original blocker
still exists before un-gating interps.

## Related issues

- **Bug #136** (referenced in code): Earlier work on string interpolation; gating mechanism
  was added as workaround.
- **stage4_compiled_dict_no_growth_2026-07-11.md:** `.join()` builtin also silently fails to
  lower in bootstrap; similar pattern (expression not lowered → null/zero constant emitted).
- **print_loss_bisect_report.md:** Interpreter-side `.join()` produces corrupted pointer
  (upstream of this bug in severity; this one is raw-literal loss).
