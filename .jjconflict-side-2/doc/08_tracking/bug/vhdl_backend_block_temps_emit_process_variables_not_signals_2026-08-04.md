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
