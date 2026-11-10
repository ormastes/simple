# HIR drops members of one explicit import list, nondeterministically
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN — worked around at the single call site, compiler defect NOT fixed
**Filed:** 2026-09-04
**Severity:** was the sole remaining Stage-3 self-host blocker on aarch64

## Symptom

Stage 3 (`stage2 -> bootstrap_main.spl`) fails in phase 3 with **exactly one**
error across all 771 modules:

```
[ERROR] phase 3 FAILED
HIR lowering error in src/compiler/driver/driver_compile_vhdl_expr.spl:
  unresolved name: _is_decimal_digit
```

## Why it is a compiler defect and not a source defect

- `_is_decimal_digit` IS defined:
  `src/compiler/80.driver/driver_compile_vhdl_util.spl:17`, a plain
  `fn _is_decimal_digit(ch: text) -> bool`.
- It IS imported by the failing file, explicitly and by name:
  `driver_compile_vhdl_expr.spl:14-15`,
  `use compiler.driver.driver_compile_vhdl_util.{ _is_decimal_digit, ... }`.
- **Other names in that same `use` statement resolve fine in that same
  function.** `_simple_is_wrapped_parenthesized`, `_simple_param_vhdl_name` and
  `_simple_vhdl_identifier` are all used inside `_simple_operand_to_vhdl`
  (the function containing the failing call at `:353`) and none of them errors.
  So the import statement itself resolved; one member of it did not.
- The util module is loaded and lowered BEFORE the consumer: phase-3 order is
  `driver_compile_vhdl_util` at 355/771 and `driver_compile_vhdl_expr` at
  535/771. No ordering inversion.
- No `[hir-reexport-chase-unresolved]` or facade warning mentions that module.

## Does not reproduce at smaller scale

Reproduced attempts, all with the admitted Stage-2 compiler on the same host:

| probe | result |
|---|---|
| two-file module, multi-line brace import, first name used | **compiles, runs correctly** |
| same, with the imported name as the file's FIRST declaration preceded by a 16-line comment header (mirroring the real file's shape) | **compiles, runs correctly** |
| real tree, `--source src/compiler --source src/app --source src/lib`, entry importing `_simple_operand_to_vhdl` from the real `compiler.driver.driver_compile_vhdl_expr` | **compiles and links, rc=0, zero errors** |

So the smallest reproduction found so far is the full Stage-3 closure. That
points at something scale- or order-dependent in HIR import/export
registration, not at the syntax of the declaration or of the import.

Candidate worth checking first: `_is_decimal_digit` is the **first declaration
in its file** (line 17, preceded only by comments). Both isolated probes above
failed to reproduce that, so if it is the cause, the trigger needs the full
closure as well — an off-by-one in a per-module export table would fit, and
would be invisible whenever a module's first declaration is never referenced
across a module boundary, which is the common case.

## Workaround applied (must be reverted when the defect is fixed)

`driver_compile_vhdl_expr.spl:353` now calls `_is_decimal_literal(first)`
instead of `_is_decimal_digit(first)`. That is **exactly** equivalent here and
is not a behaviour change:

- `first` is either `""` (when `value.len() == 0`) or a one-character string.
- `_is_decimal_digit("")` is false (every `==` arm fails);
  `_is_decimal_literal("")` is false (explicit `len() == 0` guard).
- For a one-character string `_is_decimal_literal` loops once and returns
  `_is_decimal_digit(ch)`.

`_is_decimal_literal` comes from the same module and the same `use` statement
and resolves correctly, which is itself further evidence that the import is
sound and only this one member is lost.

This is recorded rather than normalised silently, per CLAUDE.md: a workaround
forced by a compiler defect must be logged as a concrete bug. Reverting the call
site is the regression test — once the resolver is fixed, `_is_decimal_digit`
must resolve there again.


## UPDATE 2026-09-05: it is not one name, and it is not deterministic

The "first declaration" hypothesis above is REFUTED, and so is the idea that a
single name is at fault.

Run A (call site using `_is_decimal_digit`): exactly ONE error in 771 modules —
`unresolved name: _is_decimal_digit`. `_simple_integer_width`, from the same
import list and used 12 times in the same file, resolved fine.

Run B (that one call site changed to the equivalent `_is_decimal_literal`, same
tree otherwise): `_is_decimal_digit` no longer referenced, and now
`_simple_integer_width` is unresolved — 12 errors, one per use site. A name that
had resolved in run A did not resolve in run B.

So the resolver loses SOME member of that 18-name explicit list, and which member
it loses changes between runs on otherwise-identical source. Patching call sites
one name at a time cannot converge; each fix just exposes the next victim. That
also rules out anything about the declaration itself (`_simple_integer_width` is
at util.spl mid-file, not the first declaration).

### What was done instead

`driver_compile_vhdl_expr.spl` now imports that module with the WILDCARD form,
`use compiler.driver.driver_compile_vhdl_util.*`, and the per-name workaround at
the `_is_decimal_digit` call site has been REVERTED — the call site is back to
its original spelling. The wildcard is not a workaround dressed up: 863 imports
under `src/compiler` already use it, including `bootstrap_globals.spl:2`, and it
removes the construct that is being mishandled rather than dodging one symptom
of it.

### Still open (this is a real compiler defect)

The explicit multi-name import list is still mishandled in the full-closure
build. Not reproduced yet at smaller scale — a two-file probe with a multi-line
brace import resolves correctly, as does the real module tree under
`--source src/compiler --source src/app --source src/lib` with a targeted entry.
The nondeterminism between runs A and B is the strongest lead: whatever registers
explicit import members is order- or state-dependent at closure scale. Fixing it
should restore the explicit list here, which is the regression test.

## Addendum 2026-11-11 — P3 lane compiler3 verdict: NOT REPRODUCED on refreshed seed; full-closure verification BLOCKED (heavy build)

Triage on refreshed seed (build-commit 0791c2b7f4a7, bin/simple.exe 37577216 bytes)
at release/1.0.0 tip 7d4140c1a6b3 (work/p3-compiler3-20261111).

- The wildcard workaround is still in the tree
  (`src/compiler/80.driver/driver_compile_vhdl_expr.spl:20`,
  `use compiler.driver.driver_compile_vhdl_util.*`); no commit lands an explicit
  fix for the resolver defect itself (f870118eb1a4 and b702a9398e48 are the two
  workarounds). Bookkeeping row remains "open".
- The registration machinery has since been extensively reworked: RISDONE memo
  (2026-08-21) plus the BOOT-20 scalar-chain replacements for Dict membership
  mis-reporting under Stage-2 native codegen (2026-09-18) in
  `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl` — the
  same defect class as this bug, fixed adjacent to the failing path.
- Seed-smoke stress probe (2026-11-11, scratch, not committed): a 102-module
  synthetic closure (util module with 20 pub fns whose FIRST declaration is the
  first imported name — the `_is_decimal_digit` shape; consumer with an explicit
  20-name brace import using every member in one function; 100 cross-glob-importing
  filler modules) lowered through the real `module_surfaces_from_modules` +
  `hirlowering_for_module` + `begin_module` + `lower_module` path, 5 fresh
  lowerers: all 20 members resolved every round, zero lowering errors. On the
  refreshed Rust seed the explicit list survives closure-scale registration.
- The original failure was on the Stage-2/3 NATIVE self-host lane (aarch64,
  771-module closure); that repro is a heavy entry-closure native build, which
  this lane is forbidden from running. Exact command needing grant (from the
  doc's own repro, updated to this worktree):
  `SIMPLE_LIB=$PWD/src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe native-build --backend cranelift --source src/app --source src/lib --source src/compiler --entry-closure --entry src/app/<tmp>/i_owner.spl --runtime-bundle core-c-bootstrap --timeout 1200 --output <out>`
  run to `hir N/N` completion — but the authoritative discriminator is reverting
  `driver_compile_vhdl_expr.spl:20` to the explicit 20-name list and rebuilding
  the full stage-3 closure; any `unresolved name` from that import list = LIVE.
- Verdict: NOT REPRODUCED on the refreshed seed at 102-module scale (x5 lowerers);
  likely repaired by the Aug–Nov registration rework but UNVERIFIED on the failing
  lane. Status: keep OPEN; verification blocked on the heavy full-closure build.

