# VHDL backend emits block-level MIR temps as process VARIABLES (`:=`); the E2E spec expects concurrent SIGNAL assignments (`<=`)

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache test/02_integration/compiler/vhdl_backend_e2e_spec.spl
# Results: 33 total, 18 passed, 15 failed      (after the MirTerminator.Ret rename fix)
#   ✗ compiles simple adder to valid VHDL entity — expected false to equal true
#   ✗ compiles local copies to signal assignments
#   ✗ compiles branch-local computations inside combinational process
#   … 15 in total, all "expected false to equal true"
```

Dumping the generated VHDL for the first failing example (probe:
`build/tmp_gap/vhdl_probe.spl`, a copy of the spec with a `print` of
`compiled.vhdl` inserted before the structural checks) gives:

```vhdl
architecture rtl of adder is
begin
    comb: process(all)
        variable sum : signed(31 downto 0);
    begin
        sum := a + b;
        result_out <= sum;
    end process comb;
end architecture rtl;
```

Every structural check passes except
`vhdl_backend_e2e_spec.spl:207`:

```simple
check(vhdl.contains("sum <= a + b;"))
```

Actual: `sum := a + b;` (variable assignment).
Expected by the spec: `sum <= a + b;` (signal assignment).

## Root cause

The two sides model the same MIR differently and both are internally
consistent, so this is a **contract divergence**, not a one-sided bug:

* **Backend as it stands:** every MIR local, including block-level temps, is
  hoisted into a single `comb: process(all)` and declared `variable`. VHDL then
  *requires* `:=` — writing `sum <= a + b;` to a declared `variable` is a hard
  GHDL error. So the emitted code is valid on its own terms.
* **Spec as written:** block-level temps become architecture-level *signals*
  with concurrent assignments (`sum <= a + b;`), and only *branch-local* temps
  (the `v_`-prefixed ones) become process variables with `:=`. That split is
  visible in the assertion set: the 18 passing examples are exactly the ones
  asserting `v_… :=` or `result_out <=`; the 15 failing ones are exactly the
  ones asserting `<name> <= …` for a non-`v_` temp
  (`vhdl_backend_e2e_spec.spl:207, 283-284, 611-613, 690-694, 736-737,
  981`, …).

The two shapes cannot be reconciled by editing one assertion: the declaration
(`variable sum` vs a signal declared in the architecture) and the assignment
operator must change together.

## Why not fixed now

Deciding which side is authoritative is a VHDL-backend design call, not a test
repair. Flipping the spec to `:=` would silently bless a change of the
generated hardware structure (a process variable has no delta-cycle semantics
and no separate driver, so the synthesised result is not equivalent for
multi-driver or feedback paths); flipping the backend back to concurrent signal
assignments touches the emitter for every block-level temp and must be
re-validated through GHDL analysis for all 33 examples. Neither is safe to do
from a measurement lane without the backend owner's intent.

Related and already fixed in the same file: the spec referenced
`MirTerminator.Return(...)`, but the enum variant is `Ret`
(`src/compiler/50.mir/mir_instruction_support.spl:279`). That stale name made
the whole file fail to compile — 0 of 33 examples ran, reported as
"9 passed / 24 failed". Renaming the 35 call sites to `MirTerminator.Ret`
revived the file and took it to 18 passed / 15 failed. **The same stale
`MirTerminator.Return` appears in at least 8 further `.spipe_matchers_*` spec
files under `test/01_unit/compiler/` (backend/native, backend, native,
mir_opt/cipher) — those are outside this lane's scope and were not touched.**

## Fix 2026-09-13 (BUGFIX-6 lane) — swept the remaining stale `MirTerminator.Return` sites

The doc noted "at least 8 further `.spipe_matchers_*` spec files" still used
the stale `MirTerminator.Return(...)` name and were "outside this lane's
scope and were not touched". A repo-wide sweep found the real count was
**32 files** (across `test/01_unit`, `test/02_integration`, `test/03_system`,
`test/system`, `test/integration`, and the `test/unit` mirror tree)
constructing `MirTerminator.Return(` — a variant `MirTerminator` never
declared (it declares `Ret(value: MirOperand?)`).

The existing regression guards (`mir_terminator_variant_name_spec.spl`,
`mir_enum_variant_references_exist_spec.spl` — both written by a prior lane
specifically to pin this incident) confirmed the shape: all call sites use
the single-positional-arg form (`MirTerminator.Return(nil)` /
`MirTerminator.Return(Some(...))`), matching `Ret(value: MirOperand?)`
exactly, so a straight `MirTerminator.Return(` -> `MirTerminator.Ret(`
rename is value-identical everywhere. The two guard specs' own prose/fixture
uses of the literal string `"MirTerminator.Return"` were deliberately left
untouched (they exist to detect this exact stale name, not to construct it).

RED (base `a6450c9d6f5`, sample):
`test/01_unit/compiler/backend/llvm_matrix_lowering_spec.spl` ->
`Results: 2 total, 0 passed, 2 failed` (`semantic: unknown variant or
method 'Return' on enum MirTerminator`).

Fix: renamed `MirTerminator.Return(` to `MirTerminator.Ret(` in all 32
non-guard files.

GREEN:
- `mir_terminator_variant_name_spec.spl`: `2 total, 2 passed, 0 failed`.
- `mir_enum_variant_references_exist_spec.spl`: `2 total, 2 passed, 0 failed`
  (first run hit a stale test-runner cache and reported the old failure;
  `--no-cache` reproduced the true, current-content result).

**Not fully green everywhere, and that is expected, not a regression**: once
a file actually compiles and its examples execute instead of dying on the
unknown-variant error, some examples now surface *different*, genuinely
pre-existing defects that the stale name had been masking entirely (0
examples ever ran there before). Two confirmed instances, neither caused by
this rename and neither touched:
- `llvm_matrix_lowering_spec.spl`: LLVM backend now panics
  (`compile error: LLVM backend does not support MatMul lowering`) instead
  of returning the expected descriptive text — a genuine LLVM-backend
  behavior gap (`MirToLlvm.translate_module` needs to catch this case and
  return text rather than panic), out of scope for this rename.
- `mir_opt/cipher/pattern_dispatch_spec.spl`: 20/22 pass; the 2 failures
  ("rewritten instruction is Intrinsic not Call") are an unrelated
  pre-existing cipher-pattern-rewrite gap. **Correction (2026-09-13):** the
  file actually executed was `test/01_unit/compiler/mir_opt/cipher/
  pattern_dispatch_spec.spl`, which already used `Ret(` before this change —
  it was never one of the 32 renamed files, only its `test/unit/` twin was.
  The 20/22 result and the 2 pre-existing failures are real and unrelated to
  this rename, but the "renamed file surfacing a pre-existing defect" framing
  above does not apply to it. None of the 12 `test/unit`-only renamed files
  in this list (the `test/unit/compiler/mir/**` and `test/unit/compiler/
  mir_opt/**` entries below) were actually executed as part of this pass —
  only their `test/01_unit` twins were, where those twins existed and needed
  the rename. See the test-tree-divergence-delta note below for the
  after-effect this had on 6 of those pairs.

This mirrors exactly the precedent this doc's own MirTerminator.Return
`vhdl_backend_e2e_spec.spl` fix already set (0/33 -> 18 passed/15 genuinely
failed) — reviving a file from "never executes" to "executes and reports
real results" is the fix; the newly-visible real failures are separate,
pre-existing bugs left RED per `.claude/rules/testing.md`, not swept under
this rename.

Files changed (32, `MirTerminator.Return(` -> `MirTerminator.Ret(`):
`test/03_system/feature/compiler/{mir_native_spec.spl,mir_complex_spec.spl}`,
`test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl`,
`test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl`,
`test/02_integration/compiler/vhdl_backend_e2e_spec.spl`,
`test/integration/compiler/vhdl_backend_e2e_spec.spl`,
`test/01_unit/compiler/backend/{llvm_matrix_lowering_spec.spl,cranelift_gemm_fusion_spec.spl,vhdl_backend_spec.spl,vhdl_abi_spec.spl,native/isel_x86_64_spec.spl,native/isel_riscv64_spec.spl}`,
`test/01_unit/compiler/native/auto_vectorize_spec.spl`,
and their `test/unit/compiler/**` mirror-tree copies plus
`test/unit/compiler/mir/{aop_injection_spec.spl,mir_serialization_spec.spl,mir_pattern_idiom_benchmark_spec.spl,mir_opt_spec.spl}`,
`test/unit/compiler/mir_opt/{optimizer_manifest_backend_policy_spec.spl,fs_optimization_spec.spl,var_reassign_analysis_spec.spl}`,
`test/unit/compiler/mir_opt/cipher/{pattern_dispatch_spec.spl,cipher_parity_spec.spl,opt_remark_spec.spl,cipher_rewrite_integration_spec.spl,target_opt_context_spec.spl}`.

## Test-tree-divergence delta check (2026-09-13, BUGFIX-6 lane)

`sh scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD`
reports FAIL ("offender list SHRANK but guard still FAILs — offender state
changed") rather than a clean PASS. Investigated: this is a pure improvement,
not a regression or a stale-baseline problem.

Direct before/after run of the underlying guard
(`check-test-tree-divergence.shs --ref <rev>`):

- BASE (`origin/main`): `3947 diverged vs 965 baselined (3085 new, 103
  fixed-but-still-baselined)`
- NEW (`HEAD`): `3941 diverged vs 965 baselined (3079 new, 103
  fixed-but-still-baselined)`

The **baselined** counts (965 total, 103 fixed-but-still-baselined) are
unchanged — no baselined pair flipped status, so there is nothing to
`--generate-baseline` for. The removed 6 entries all came from the
**unbaselined "new"** bucket (3085 -> 3079):

```
unit:compiler/loader/jit_context_spec.spl
unit:compiler/mir/mir_opt_spec.spl
unit:compiler/mir/mir_serialization_spec.spl
unit:compiler/mir_opt/cipher/cipher_parity_spec.spl
unit:compiler/mir_opt/cipher/cipher_rewrite_integration_spec.spl
unit:compiler/mir_opt/cipher/pattern_dispatch_spec.spl
```

Verified directly (`cmp`) that each of these 6 `test/01_unit/**` /
`test/unit/**` pairs is now byte-identical — exactly the effect of applying
the same mechanical `MirTerminator.Return(` -> `Ret(` rename to both twins of
each pair. Zero new divergence was introduced; the delta script's FAIL is its
designed behavior for ANY change to the offender list (even a shrink),
requiring a human to confirm the shrink is benign rather than auto-passing —
which this note does. The remaining 3079 unbaselined + 965 baselined
offenders are pre-existing and untouched by this lane.
