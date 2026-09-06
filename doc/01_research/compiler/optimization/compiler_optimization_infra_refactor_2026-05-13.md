<!-- codex-research -->
# Compiler Optimization Infrastructure Refactor - Local Research

Date: 2026-05-13

## Findings

- Canonical MIR optimization wiring lives in `src/compiler/60.mir_opt/mir_opt/mod.spl`.
  It owns `OptLevel`, pass lists, target optimization context, and the string-keyed
  dispatcher used by `pipeline_optimize`.
- The current cipher/pattern hot path is:
  `pipeline_optimize` -> `run_pass_on_module("pattern_idiom")` ->
  `run_pattern_idiom_pass_*` -> function/block/instruction walk ->
  `lookup_rule_for_callee`.
- `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` previously rebuilt
  `cipher_rule_table()` for every `lookup_rule_for_callee` call and then returned
  `table[n]`. This adds avoidable allocation/work in the call-site matching path.
- Dynamic loading already exists for block/plugins and WFFI in `src/compiler/15.blocks/plugin_startup.spl`
  and the Rust interpreter extern layer, but docs repeatedly note whitelist and
  safety constraints. Optimizer hot-path rules should therefore be built in by
  default; dynamic providers should be reserved for rare, experimental, or
  out-of-tree optimizers.
- Existing docs point to a larger follow-up: a shared MIR visitor/transform API
  would reduce repeated pass walking and distinguish module/function/loop passes.

## Implemented First Slice

- Added common optimizer rule provider metadata in the MIR pattern rule layer.
- Marked cipher rules as a built-in hot-path provider.
- Changed `lookup_rule_for_callee` to return the matched rule directly instead
  of rebuilding the full table on each lookup.

## Next Safe Refactor Targets

1. Add a shared MIR function/block/instruction visitor for passes that only
   rewrite instructions.
2. Replace string pass dispatch with a small pass descriptor table while keeping
   stable CLI/display names.
3. Add a dynamic optimizer manifest format only after built-in pass boundaries
   and versioned ABI fields are stable.
