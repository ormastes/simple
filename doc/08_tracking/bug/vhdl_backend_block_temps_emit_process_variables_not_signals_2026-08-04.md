# VHDL backend emits block-level MIR temps as process VARIABLES (`:=`); the E2E spec expects concurrent SIGNAL assignments (`<=`)

**Status:** OPEN (backend/spec contract divergence — needs the VHDL backend
owner's call, unchanged). **The stale-`MirTerminator.Return` half named at the
bottom of this doc is now FIXED, 2026-08-17** — see "Stale variant name: fixed"
below.
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

## Stale variant name: fixed (2026-08-17)

The "8 further spec files" note above was close but not exact. The real census
(`/usr/bin/grep -rln 'MirTerminator\.Return' test/`) was **5** files, 43 call
sites, and all 5 are now renamed to the real variant `MirTerminator.Ret`
(`src/compiler/50.mir/mir_instruction_support.spl:321`; there is no `Return`
variant and never was):

| file | sites |
|---|---|
| `test/03_system/feature/compiler/mir_complex_spec.spl` | 1 |
| `test/03_system/feature/compiler/mir_native_spec.spl` | 1 |
| `test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` | 3 |
| `test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` | 3 |
| `test/integration/compiler/vhdl_backend_e2e_spec.spl` | 35 |

`test/integration/compiler/vhdl_backend_e2e_spec.spl` is the legacy mirror of
the `test/02_integration/` copy this doc already repaired; only the mirror was
left stale. Measured on that file (the 5-file set's only substantial one):

```
# BEFORE (HEAD content, run from a copy)
Results: 41 total, 1 passed, 40 failed
    semantic: method `prepare_tuple_types_for_module` not found on class `VhdlBackend`

# AFTER
Results: 41 total, 20 passed, 21 failed
```

+19 examples genuinely unblocked. The `prepare_tuple_types_for_module`
"missing method" error was a cascade of the unknown-variant failure and is
gone. The remaining 21 REDs are **not** this defect: 15 are the backend/spec
`<=` vs `:=` contract divergence this doc is actually about (still open, still
an owner decision), and the rest are two other product gaps surfaced by the
now-running file — `VHDL combinational local 'arr_sig' must be a fixed scalar
or record`, and `unknown extern function: rt_process_run_capture`.

The mirror pair remains legitimately diverged on one line (`tag:
["only-compiled", "slow"]` vs `tag: ["slow"]`), so
`scripts/check/test_tree_divergence_baseline.txt:34` stays valid and was NOT
edited.

Coverage landed with the fix:
- Reproducer: `test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl`
- Class detection: `test/01_unit/compiler/mir/mir_enum_variant_references_exist_spec.spl`
  — extracts every `<MirEnum>.<Variant>` reference from the MIR-constructing
  specs across all five MIR enums and asserts each is declared in the product
  enum, so any future stale variant fails, not just `Return`.

Related defect found while doing this, filed separately:
`doc/08_tracking/bug/local_skip_on_interpreter_shadow_discards_block_false_green_2026-08-17.md`
— 19 spec files shadow the std `skip_on_interpreter` decorator with a local
helper that discards its block and still reports PASS. That false green is why
the stale variant survived in `mir_native_spec.spl`/`mir_complex_spec.spl`:
an unknown variant is only diagnosed when the constructing expression is
evaluated, and those bodies never ran.
