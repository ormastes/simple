# Stage 2 B5b duplicate-wildcard diagnostic in shared HIR closure

Status: OPEN. The selected Item 5/6 branch cannot produce an executable
current-source compiler from the admitted Stage 2 toolchain yet.

## Evidence

- Admitted compiler: `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple` (hash and admission in the Item 5 VHDL blocker report).
- `SIMPLE_LIB=src timeout 160s <stage2> compile src/compiler/20.hir/hir_types.spl --format=smf --output build/mini_builds/item56_hir_types_isolate.smf` reached MIR 87/87 and exited 1 after two `B5b: match has multiple wildcard arms` errors. Log: `build/mini_builds/item56_hir_types_isolate.log`.
- Direct `type_equality.spl` (88 modules) and `collection_plan.spl` (90 modules) compiles have the same two errors. This points to their shared 87-module closure, without identifying a particular module.
- Correction: the first source scan missed expression-form `val ... = match` blocks. A corrected indentation scan found ten blocks with a bare enum arm followed by `_` in the shared 87-module closure: one `MethodResolution.Unresolved` block and nine `SymbolKind.Method`/`Function` blocks. An eleventh block has three bare `VhdlResetSynchrony` arms but no wildcard, so it cannot directly produce this exact diagnostic.
- `lower_match_case` records a duplicate wildcard after `has_default_body` was set by an earlier Wildcard or Binding arm. The old diagnostic dropped its provided span in the summarized MIR error output.

## Next action

The wildcard diagnostic now prints the current function/module plus first and
duplicate spans. The ten bare-variant-plus-wildcard source blocks have been
changed to qualified `MethodResolution` and `SymbolKind` patterns; these
changes are not yet compiled. In a fresh bounded verification session, rerun
one focused 87-module closure. If B5b remains, use the location-rich diagnostic
to identify its HIR producer and repair that cause. Do not weaken the
duplicate-default check.

The three bounded direct compiles this session all failed, so no executable
test PASS or Item 5/6 qualification is claimed.
