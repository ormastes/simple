# Stage 2 HIR enum-owner failure while qualifying Item 5 VHDL port

Status: OPEN. The selected Item 5/6 branch contains the compiler-owned VHDL
output port at commit `e68c66ffcae`; its focused behavior spec has not run.

## Reproduction

- Worktree: `work/targets-release-20261010` at `e68c66ffcae`.
- Compiler: admitted pure-Simple Stage 2 under
  `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
  SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`.
  Its adjacent `admission.env` says `status=admitted` and binds that hash.
- Command: `SIMPLE_LIB=src timeout 600s <admitted-stage2> compile test/01_unit/compiler/driver/driver_vhdl_output_port_spec.spl --format=smf --output build/item5-vhdl-port-long.smf`.
- Exit: 1 after 367.152 s in phase 3 HIR. Parse and surface build reached
  525/525; HIR reached 525/525, then reported one poisoned module and four
  errors. Observed RSS during HIR 456/525 was 2,208,788 KiB; this is a sampled
  value, not peak RSS.
- Poisoned module: `compiler.semantics.perf.collection_plan`.
  Two occurrences each of `qualified enum pattern owner differs from subject
  owner` and `E-HIR-MATCH-UNHANDLED-PATTERN` are reported for
  `src/compiler/35.semantics/perf/collection_plan.spl`.
  The port and its spec were lowered before this module without an explicit
  diagnostic. The log does not identify which match arms have the mismatched
  enum owners.

## Impact and next action

The compile never reaches monomorphization or executable behavior. Source
closure and Phase 5 checks are green for the VHDL port, but native behavior,
provider demand-load, and size/startup evidence remain unqualified.

Inspect the subject and qualified pattern owner identities in
`expression_components.spl:226` at the error site, then repair the
canonical owner resolution or the actual mismatched enum projection. Add a
focused regression with the real `CollectionPlanFacts` enum cases and an
unrelated enum negative case. Do not replace qualified patterns with a broad
catch-all that could accept an incompatible owner. Rebuild an admitted
self-hosted compiler and rerun this spec in a fresh bounded verification cycle.

## 2026-10-11 focused owner-binding candidate

Two smaller admitted Stage 2 probes compiled imported and local enum fields
without an owner error. In the real `collection_plan.spl`, the two
`match node.kind` sites match the two observed owner errors. Binding
`node.kind` to a local `CollectionPlanKind` before each match lets a
bounded direct compile reach HIR 90/90 and monomorphization, then MIR 90/90.
The command was `SIMPLE_LIB=src timeout 240s <admitted-stage2> compile
src/compiler/35.semantics/perf/collection_plan.spl --format=smf
--output build/item56-collection-plan-typed.smf`. It exited 1 after
99.896 s because MIR reported 58 errors across the 90-module closure,
including unsupported `HirExpr` struct equality at
`collection_plan.spl:95:16`, enum payload/identity errors in HIR/type
modules, and ambiguous bare enum variants. This direct compile is not an
executable test PASS and does not qualify the VHDL port.

The typed bindings preserve the declared enum owner and are kept as a
source-level repair candidate. The underlying field-projection owner bug
remains open; the MIR failures are a separate current-source qualification
blocker. The three-cycle limit for this focused diagnosis is exhausted.

## 2026-10-11 narrow MIR equality repair

The first direct MIR error was three whole-`HirExpr` comparisons in
`collection_plan.spl`. The loop is now taken from the one stored original
block, so its redundant `original_loop` copy is gone. Validation compares the
source binding by symbol and type and compares admitted variable/literal
mappings by their values and types. Two authored regression cases cover source
and induction binding mutation after extraction.

A bounded direct compile with the same admitted Stage 2 binary reached HIR
90/90 and MIR 90/90, then exited 1 after 100.321 s with 55 MIR errors, down
from 58. No diagnostic names `collection_plan.spl`; the first remaining error
is `DimExprKind.Named` payload mismatch at `hir_types.spl:797:51`.
Other errors include ambiguous bare variants in
`hir_lowering/type_equality.spl`, missing enum runtime identity, and
`PlatformLayoutDiagnostic` payload mismatch. This is stage-scoped compile
evidence, not a unit/spec PASS or Item 5 qualification. The focused VHDL port
spec and native size/startup cohort remain unrun.

## 2026-10-11 optional payload and tuple-owner follow-up

Three bounded 90-module direct compiles with the same admitted pure-Simple Stage 2 binary followed the previous 55-error baseline. Their full failing logs are retained at `build/mini_builds/item56_dimexpr_optional_binding_90module.log`, `item56_qualified_patterns_90module.log`, and `item56_symbol_span_90module.log`. An explicit `i64?` binding in `DimExpr.named_range` cleared the first direct-`Some` payload error (54 MIR errors, 94.175 s). Qualifying tuple-pattern variants in `hir_lowering/type_equality.spl` cleared 40 ambiguous bare-owner and missing-identity diagnostics (14 errors, 93.747 s). Early float returns, direct `SymbolId.id` access in `get_symbol`, and an explicit `Span` binding reduced the remaining set to six (89.899 s). The six were two pairs of `unknown variant SymbolId`/missing runtime identity plus two multiple-wildcard diagnostics. The other two direct `SymbolId` struct patterns in `symbol_display_name` and `rename_symbol` have since been replaced by field reads, but no fourth broad compile was run: the mandatory three-cycle cap is exhausted for this session.

The direct `Some(i64)` failure and typed-local control are retained as fixtures and detailed in [the optional payload bug](enum_optional_payload_context_lost_2026-10-11.md). The 90-module compile still has no terminal PASS, the current-source compiler is not admitted, and the VHDL/Item 5/Item 6 system tests and performance gates remain unqualified. The next session should first verify the final `SymbolId` edit once; if it passes, proceed to the actual target entrypoints, not another diagnostic-only count loop.
