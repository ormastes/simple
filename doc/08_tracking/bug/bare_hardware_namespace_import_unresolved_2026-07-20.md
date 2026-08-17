# Bare `hardware.*` namespace imports fail to resolve (needs `std.` prefix; ~64 specs affected)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** compiler module resolution / `src/lib/hardware/**`

## Symptom

`test/01_unit/hardware/riscv_common/.spipe_matchers_riscv_formal_contract_spec.spl`
fails immediately (0 examples executed) with:

```
error: semantic: Cannot resolve module: hardware.riscv_common.core.riscv_formal
error: test-runner: no examples executed
```

The spec's import is:

```
use hardware.riscv_common.core.riscv_formal.{
    RiscvFormalContract, RiscvRetireEvent, ...
}
```

Reproduced identically under BOTH evaluators (rules out the usual
run-vs-test-evaluator landmine as the root cause here):

```
bin/release/x86_64-unknown-linux-gnu/simple run <spec>       # same "Cannot resolve module" error
bin/release/x86_64-unknown-linux-gnu/simple test <spec> --no-session-daemon  # same error
```

## Root cause

The actual module lives at `src/lib/hardware/riscv_common/core/riscv_formal.spl`.
Per `.claude/rules/structure.md`, the supported import convention is
`use std.X` (resolves from `src/lib/`). The bare `use hardware.X...` form
(no `std.` prefix) is NOT resolved by the module resolver from either `run`
or `test` — it instead tries to resolve `hardware` relative to the current
working directory / project root, which fails.

**Confirmed empirically:** prefixing the import with `std.` (i.e.
`use std.hardware.riscv_common.core.riscv_formal.{...}`) makes the "Cannot
resolve module" error disappear and the spec proceeds to execute its
examples. However, doing so is NOT a safe drop-in fix for this campaign:

1. This bare `hardware.*` (no `std.` prefix) import style is used by **64
   files** under `test/01_unit/hardware/` (`grep -rl '^use hardware\.'
   test/01_unit/hardware/ | wc -l` = 64), so this is a systemic/repo-wide
   pattern, not a one-off typo in this single spec — fixing only this one
   spec would diverge from the established sibling convention and is out of
   this shard's scope (touching only 1 of 64 affected files).
2. Even after adding the `std.` prefix, the spec does NOT go green — it
   then hits a SEPARATE, already-tracked defect: imported free
   functions/structs (`RiscvFormalContract`, `riscv_mask_for_xlen`,
   `riscv_instruction_size`) report `semantic: function/variable ... not
   found` under the test evaluator, matching the known landmine documented
   in `generic_class_static_method_unresolved_under_test_2026-07-20.md` /
   `enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`
   (imported free symbols unresolved under `simple test`'s evaluator even
   though import resolution itself succeeds).

So this spec is blocked by two stacked, independent defects: (a) bare
`hardware.*` namespace resolution (this doc), and (b) the pre-existing
imported-free-symbol-under-test landmine (already tracked, not re-filed).
Neither is fixable via a spec-only edit without diverging from the 64-file
sibling convention or without a compiler-side fix.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/hardware/riscv_common/.spipe_matchers_riscv_formal_contract_spec.spl \
  --no-session-daemon
```

## Affected specs seen this shard

- `test/01_unit/hardware/riscv_common/.spipe_matchers_riscv_formal_contract_spec.spl`

(Broader sibling pattern: 64 files under `test/01_unit/hardware/` use the
same bare `use hardware.X` import style; likely all share this root cause,
not independently verified here — out of shard scope.)

## STILL_PRESENT — re-verified 2026-08-17 (P2 triage, compiler lane)

Recorded reproducer `test/01_unit/hardware/riscv_common/.spipe_matchers_riscv_formal_contract_spec.spl`
NO LONGER EXISTS. Source verification instead:
`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:156-300` tries
local dir, `$SIMPLE_LIB`, `src/<path>`, then a `lib/`-family search gated on
`if relative_path.starts_with("lib/")` (line 219). A bare `hardware.*` never gets
a `lib/` prefix, and `src/hardware/riscv_common/core/riscv_formal.spl` does not
exist (the module lives at `src/lib/hardware/...`). No namespace fallback list
exists. 32 files under `test/01_unit/hardware/` still use the bare form, e.g.
`test/01_unit/hardware/riscv_common/riscv_formal_contract_spec.spl:3`.
NOT FIXED by this lane (interpreter path owned by a concurrent P1 lane).

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STALE-REF

The cited `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`
(403 lines) contains no occurrence of `hardware`, and no `"hardware"` literal
appears in any `src/compiler/10.frontend/core/interpreter/*.spl`. The namespace
alias table is elsewhere; re-locate it before actioning.
