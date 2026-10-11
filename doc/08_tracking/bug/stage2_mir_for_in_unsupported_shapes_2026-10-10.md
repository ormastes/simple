# BUG-IT-9 — 50.mir: four `for` iteration shapes do not lower on stage2

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests. release/1.0 @ b68c0c65708.
Spec: `test/01_unit/compiler/50.mir/for_in_unsupported_shapes_spec.spl` (`@tag:in-development`, one
example per shape, each asserting the correct zero-diagnostic behaviour; the shapes that DO lower are
in `for_in_variant_lowering_spec.spl`). Runner: seed-head `simple.exe run <spec>`.

| shape | diagnostic | call sites in src/ (compiler/app/lib) |
|---|---|---|
| `for i in (0..n).step(2)` / `(n..0).step(-1)` | `unresolved method call: step` | 0 / 0 / 0 |
| `for (i, x) in xs.enumerate()` | `unresolved method call: enumerate` | 6 / 5 / 7 |
| `[x * x for x in xs if x > 0]` | `E-MIR-EXPR-Comprehension: MIR lowering does not support this comprehension expression` | ~1 / 0 / 0 |
| `for w in make(n).reversed()` | `unresolved method call: reversed` | 0 / 2 / 0 |

Scope note: stage2 ladder builds run with `SIMPLE_BOOTSTRAP=1`, under which MIR lowering is SKIPPED
for every module except the entry, so these holes bite the entry module today and every module in a
stage4 / non-boot build. When a shape is wired, move its example back to the green spec.
