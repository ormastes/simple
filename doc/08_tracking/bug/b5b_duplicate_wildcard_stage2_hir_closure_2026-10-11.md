# Stage 2 B5b duplicate-wildcard diagnostic in shared HIR closure

Status: OPEN. The selected Item 5/6 branch cannot produce an executable
current-source compiler from the admitted Stage 2 toolchain yet.

## Evidence

- Admitted compiler: `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple` (hash and admission in the Item 5 VHDL blocker report).
- `SIMPLE_LIB=src timeout 160s <stage2> compile src/compiler/20.hir/hir_types.spl --format=smf --output build/mini_builds/item56_hir_types_isolate.smf` reached MIR 87/87 and exited 1 after two `B5b: match has multiple wildcard arms` errors. Log: `build/mini_builds/item56_hir_types_isolate.log`.
- Direct `type_equality.spl` (88 modules) and `collection_plan.spl` (90 modules) compiles have the same two errors. This points to their shared 87-module closure, without identifying a particular module.
- Source scan of the 87 parsed modules found no match block with two same-level wildcard or bare-binding defaults. That scan is only source-level evidence.
- `lower_match_case` records a duplicate wildcard after `has_default_body` was set by an earlier Wildcard or Binding arm. The old diagnostic dropped its provided span in the summarized MIR error output.

## Next action

The wildcard diagnostic now prints the current function/module plus first and
duplicate spans; this change is not yet compiled. Run one focused direct
compile in a fresh verification session and use the new context to locate the
HIR arm producer. Confirm whether source, HIR normalization, or array transport
duplicates the default; then add a focused behavior regression and repair the
actual cause. Do not weaken the duplicate-default check.

The three bounded direct compiles this session all failed, so no executable
test PASS or Item 5/6 qualification is claimed.
