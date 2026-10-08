# Enum match recovery read an obsolete local binding map

Status: source repair only; native qualification pending.

## Actual failure

Compiler ec7f0118a19e2703e3b092ac775237cd93491271cca26ca4724259a8aa082019, built from 8ccea67adf9cf01c4fe6eccf2ad852ddf4fafcf5, completes all three HIR stores for `test/fixtures/compiler/imported_enum_runtime_aliases/main.spl`, then reports two `B5b: match has multiple wildcard/binding default arms` errors. The independent two-owner enum fixture reports the same diagnostic once. No app or native regression PASS is claimed.

Retained evidence: `build/item5-trait-enum-layout-cycle2-20261008/qualification/llvm/enum-aliases/build.log`. The actual main HIR cache entry is `59b3736b1ad5da18d3e717b0682ef6de4e7ea28273d20b252974ac730ee4bbe2.hir` under `/root/.cache/simple/v1/projects/7dcf7beb22f33342151bfd60494ef3d85d51da9a92b6318d2576edd1a65e5941/native-build/v1/default/hir`. Its header binds frontend-exe ec7 and source identity `14d03fac80e6ace6n188`. A read-only copy is retained under root `build/review/item5-enum-alias-<entry-name>`.

The stored HIR proves the prior canonical alias repair ran: UnitMode/UnitModeAgain refer to symbols 0/1, both named SharedMode with the left module owner; PayloadMode refers to symbol 2 from the right module. HirEnum runtime names agree with those identities. Parameters retain Named(0)/Named(1). Match subjects are untyped NamedVar values and the unit-name patterns remain Binding, requiring MIR's declared-local recovery.

## Source defect and repair

`mir_lowering_types.spl` bind_local writes local_symbol_ids/local_symbol_values and their index. find_local is the authoritative reader and returns LocalId(-1) for a missing binding. It does not populate local_map; reset_function_local_tracking clears that legacy map.

The Var and NamedVar arms in both enum_match_expr_type and enum_match_receiver_local_type nevertheless probed local_map. Thus parameters bound by lower_function could not reach their separately retained local_hir_type metadata through these paths. They fell back to raw symbol recovery instead, a different path with existing aggregate-Option transport limitations.

Replace exactly these four reads with find_local and its nonnegative-ID admission check. Do not repopulate a redundant map, change SymbolIds, infer an owner from variant spelling, filter away ambiguous owners, or relax unit/payload metadata checks. Symbol-table fallback remains available for genuinely absent local metadata. Native trait call lowering itself has no direct local_map reads; its owner caller may benefit from the repaired shared receiver helper.

## Required qualification

Parent will integrate this source-only repair into the next coordinated compiler generation. Run the retained alias and distinct-owner fixtures with the admitted candidate, compile and execute their outputs on both requested backends, and retain negative ambiguous/mismatched-owner diagnostics. The actual RED fixtures are already present; no unchanged Hello or compiler build was run in this lane. Four-site diff inspection and git diff --check passed, which are source checks only. Runtime closure of the observed B5b failure remains unproven until that execution.