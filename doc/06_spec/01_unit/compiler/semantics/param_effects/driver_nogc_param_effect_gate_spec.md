# Typed no-GC policy admission

**Evidence status:** authored operator manual; generated docgen and execution verification pending an admitted full pure-Simple runtime. No PASS claimed.

Source: `test/01_unit/compiler/semantics/param_effects/driver_nogc_param_effect_gate_spec.spl`.

1. Parse source and construct physical module surfaces through the real frontend.
2. Admit strict synchronous reads and require the durable ownership policy bit.
3. Reject escaping contracts without publishing a new policy bit.
4. Preserve strict policy after HIR eviction, empty later admission and failed later admission.
5. Feed an actually admitted context into the real AOT driver, evict HIR, request the bypass and require NOGC-POLICY-002. Restore the go-to-end environment before asserting the result.
6. Require fresh and legacy-only contexts to remain false; a mixed legacy/strict batch becomes true.

Requirements: no-GC recovery §3.7 and AC-CYCLE-04/AC-GATE-02. This focused gate does not complete either broad acceptance row.
