# HIR unresolved-name diagnostics are unclassified, some point at 1:1, and undeclared imports pass

- id: hir_unresolved_name_diagnostic_unclassified_2026_10_20
- status: open
- found: 2026-10-20, triaging the phase-4 `src/os` HIR failure list
  (`C:/dev/simple-bootstrap-storage/p4-phase2-20261020/<backend>/hir-errors-bootstrap.txt`, 67 errors / 27 files)
- owner: HIR lowering (20.hir)

## Defects
1. Unclassified. Every `unresolved name:` / `unresolved type:` is pushed through
   `HirLowering.error` (`src/compiler/20.hir/hir_lowering/types.spl`), which stamps
   `LoweringErrorKind.Other`, although `LoweringErrorKind.UnresolvedName` exists. The catalogue
   (`src/compiler/00.common/error_explanations.spl`) has `E1001 Undefined Variable` and
   `E1002 Undefined Function`; nothing in HIR attaches them. Gates and triage have to grep text.
2. Imprecise span. Two of the 67 rows point at `:1:1` / `:0:0`
   (`ssh_session_kex.spl: unresolved name: _bytes_to_hex at ...:1:1`,
   `ssh_session_channel.spl: unresolved name: rt_bytes_u8_at at :0:0`). Reproduced with producer8:
   a name used only inside a text interpolation on line 2 is reported `at <file>:1:1`.
3. Undeclared import accepted. `use p.{gone}` where `p` exists but does not declare `gone`
   compiles with no diagnostic when `gone` is unused; it fails only at a use site. Several of the
   67 rows were imports of names whose provider had been deleted
   (`use os.compositor.text_render.{draw_text_shadow}`), stubbed/restored by the p4p2 lane in
   `2830694a792` (bug p4p2_os_deleted_providers_stubbed_2026-10-20).

Not a defect: resolution itself is eager. A missing name fails HIR in a never-called function,
in every body position probed (branch, loop, lambda, method, match arm, interpolation, module
initializer, after a field read), in a provider module of the closure, and when the name lives
in a sibling module that was not imported (producer8, 2026-10-20). An import of a missing
MODULE fails at the driver with `unresolved import '<module>'`.

## Specs
- Contract (in-development): `test/01_unit/compiler/20.hir/bootstrap_regressions/unresolved_name_diagnostic_contract_spec.spl`.
- Eager-resolution reproducers + prevention (passing): `test/01_unit/compiler/20.hir/bootstrap_regressions/unresolved_name_eager_resolution_spec.spl`.
- Gate: `scripts/check/check-hir-closure-resolves.shs` (not registered in must_check_gates.sdn).
  On the failing snapshot it reports `FAIL ... window_effects.spl: draw_text_shadow;
  aes128_gcm.spl: _inc32,_make_j0`; on the p4p2 tree after `2830694a792` it reports PASS for the
  same two entries.
