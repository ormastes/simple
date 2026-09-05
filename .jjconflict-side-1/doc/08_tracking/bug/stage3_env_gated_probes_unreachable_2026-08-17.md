# Env-gated compiler probes are unreachable in the Stage 3 self-host

- **Filed:** 2026-08-17
- **Status:** FIXED (plumbing) — see "Fix" below. The underlying Stage 3
  defect this unblocks is still open.
- **Severity:** high (diagnostics infrastructure; blocks root-cause analysis)
- **Area:** bootstrap provenance / compiler diagnostics

## Summary

No env-gated diagnostic probe inside the compiler could be switched on for
bootstrap Stage 3 from outside. Stage 3 runs under `env -i` with an explicit
allowlist, so any variable not on that list is dropped and every probe gate
reads empty and stays silent. The instruments existed and could not be turned
on where it mattered.

## Measurement (not inference)

`SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE` was added by commit `a4f768af811` in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1371`.

- It **was** compiled into the admitted Stage 2 binary: `strings` on that
  binary finds the `HIR-PAYLOAD-LOOKUP` literal.
- It emitted **zero** lines during Stage 3.

Cause, read directly from the code rather than inferred from the symptom:
`bootstrap_stage3_run_transcribed`
(`scripts/check/lib/bootstrap-stage3/command-snapshot.shs:212-227`) execs
Stage 3 as

```
env -i "HOME=..." "PATH=..." "TMPDIR=..." "LC_ALL=C" "LANG=C" /bin/sh -c '...' sh "$@"
```

where `"$@"` is the explicit `NAME=VALUE` vector supplied by the caller, ending
at `--`. The Stage 3 call site
(`scripts/bootstrap/bootstrap-from-scratch.sh`) supplied a fixed vector of 12
`SIMPLE_*` variables plus `RUST_LOG`, `LIBRARY_PATH`, two `MALLOC_*`, and
`LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING`. Nothing else can survive
`env -i`.

## Scope: this was never about one probe

Every env-gated probe on the Stage 3 compile path was equally unreachable. A
census of `SIMPLE_*` trace/diag gates in `src/compiler`, `src/lib`, `src/app`
returned 37 names; the ones on the Stage 3 compile path and confirmed to be
pure `if env == "1": print ...` gates are:

| variable | site |
|---|---|
| `SIMPLE_BOOTSTRAP_DIAG` | `20.hir/hir_lowering/_Items/module_lowering.spl:48,57,918,1779,1827`; `declaration_lowering.spl:54` |
| `SIMPLE_COMPILER_TRACE` | `module_lowering.spl:47,56`; `declaration_lowering.spl:53`; `60.mir_opt/mir_opt/mod.spl:43`; `10.frontend/core/parser_expr.spl:78` |
| `SIMPLE_HIR_SIBLING_TRACE` | `module_lowering.spl:66` |
| `SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE` | `module_lowering.spl:1371` |
| `SIMPLE_HIR_EXPORT_ORIGIN_TRACE` | `20.hir/hir_lowering/module_surface.spl:1066` |
| `SIMPLE_MIRB_TRACE` | `50.mir/mir_data.spl:133,207,522` |
| `SIMPLE_MIR_FIELD_TRACE` | `50.mir/_MirLowering/function_lowering.spl:1164`; `_MirLoweringExpr/expr_dispatch.spl:1162` |
| `SIMPLE_MIR_RET_TRACE` | `20.hir/hir_lowering/statements.spl:420,582` |
| `SIMPLE_MIR_DEFAULT_PAD_TRACE` | `50.mir/_MirLoweringExpr/switch_operators_calls.spl:705` |

That is ~10 probes across HIR lowering, MIR lowering, and MIR opt — the exact
layers the Stage 3 blocker lives in.

**Plausible explanation for multiple dark cycles.** The Stage 3 defect stayed
dark across five cycles while these instruments were present in the tree and
silently inert. This is offered as a plausible contributing cause, not a
demonstrated one: no cycle transcript was re-run to prove a probe would have
localised the defect.

## Why this was not a one-line fix

The Stage 3 explicit-env vector is also hashed into
`bootstrap_stage3_args_sha256` -> `stage3_build_args_sha256`, which is part of
the Stage 3 admission/provenance gate — the machinery that proves the Rust seed
did not build Stage 3 and that the frozen runtime was not swapped. Appending a
variable naively touches exactly that gate. An investigating agent correctly
refused to patch it mid-investigation.

## Fix

`bootstrap_stage3_diagnostic_env` in
`scripts/check/lib/bootstrap-stage3/authority.shs`, wired into both Stage 3
call sites (`scripts/bootstrap/bootstrap-from-scratch.sh`,
`scripts/bootstrap/resume-stage3-from-admitted.sh`). At each site the value is
computed **once** and word-split into both the args-hash vector and the real
invocation, so the two cannot drift apart.

The gate is not weakened:

1. **Name allowlist**, fixed, no prefix rule and no wildcard — the 9 names
   tabled above. Each was read and confirmed print-only.
2. **Value constrained to the literal `1`.** Any other value — `0`, `2`, a
   path, empty — is dropped. A pass-through variable cannot carry a payload
   into the compiler; it can only flip a print gate on.
3. **Deliberately excluded** because they can change what Stage 3 *builds*
   rather than only what it *prints*: `SIMPLE_DIAG_FILE`,
   `SIMPLE_MEM_DUMP_PATH`, `SIMPLE_UI_DUMP_HTML_PATH` (write files to a
   caller-chosen path), `SIMPLE_OBJDUMP` (runs a tool),
   `SIMPLE_DEBUG_INFO_LEVEL` (changes debug info in the emitted object),
   `SIMPLE_KEEP_LLVM_IR` (emits artifacts).
4. **The pass-through is inside the hashed vector**, so the args hash keeps
   describing the real invocation. Enabling a probe **does** change
   `stage3_build_args_sha256` — intended: a hash that omitted part of the
   environment would be the weaker gate.
5. The seed-delegation gate
   (`bootstrap-from-scratch.sh`, greps the Stage 3 log for
   `^Build complete: [0-9]+ compiled` / `^Linked: .* via clang` and FAILS on
   presence) is unaffected in the safe direction: a probe can only ADD lines,
   so this can make that gate fail closed, never falsely pass.

## Ablation

`scripts/check/check-stage3-diagnostic-env-passthrough.shs` (fail-closed;
`ERROR — nothing was checked` exit 2 on a vacuous run). It sources the real
`authority.shs` + `command-snapshot.shs` and drives the real
`bootstrap_stage3_run_transcribed`, substituting only the final executable for
a stub that reports which `SIMPLE_*` variables its process actually received —
which is precisely the property under test (what survives `env -i`).

Verbatim, 2026-08-17:

```
=== arm 1: with fix, SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1 ===
diagnostic env emitted: [SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1]
trace-var-visible lines: 1
HIR-PAYLOAD-LOOKUP probe-visible SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1
=== arm 2: with fix, variable unset ===
diagnostic env emitted: []
trace-var-visible lines: 0
HIR-PAYLOAD-LOOKUP probe-visible SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=<unset>
=== arm 3: control -- without fix, SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1 ===
trace-var-visible lines: 0
HIR-PAYLOAD-LOOKUP probe-visible SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=<unset>
=== invariant 1: args hash unchanged by default ===
default-with-passthrough: 40d0ca29f8bc2258265164eff8e17e592d819ebd1b7c9f1602a1aa7667f393bd
pre-fix-baseline:         40d0ca29f8bc2258265164eff8e17e592d819ebd1b7c9f1602a1aa7667f393bd
=== invariant 2: an enabled probe changes the args hash ===
with-probe-enabled:       3813efbeeb892610610ec6a1d5c8d9879744a2b7b5b1974b52b49d7c5e588c8f
=== invariant 3: value and name scope ===
emitted with hostile values: []
PASS — 6 arm(s)/invariant(s) checked, 3 ablation arms behaved as specified, default args hash unchanged, enabled probe changes hash, non-allowlisted and non-1 values rejected
GATE_RC=0
```

Arm 3 is the control and it reproduces the defect: with the variable exported
but the pass-through words omitted from the invocation — exactly the pre-fix
call shape — the stub sees `<unset>`. A control that failed to fail would mean
the test was broken.

Invariant 1 is the byte-identity proof required by design constraint 4: with no
allowlisted variable set, the emitted vector is empty and the args hash is
character-for-character the pre-fix baseline.

## Impact to state plainly

- **Default runs are unchanged.** Empty pass-through, identical explicit-env
  vector, identical transcript bytes, identical args hash (invariant 1).
- **`stage3_build_args_sha256` changes whenever a probe is enabled.** That is
  the point. A run with a probe on is a different invocation and must hash
  differently.
- **`bootstrap_stage3_helper_bundle_fingerprint` changes** because
  `authority.shs` changed. It is computed live and compared against a live
  recomputation (`manifest-verify.shs:81`), not against a stored constant, so
  there is no hardcoded value to update — but any Stage 3 manifest written
  before this change will now mismatch and needs a re-run. No such manifest
  exists in this worktree (`find build -name '*stage3*manifest*'` → empty).
- **`--diagnostics` modes now reach Stage 3.** `bootstrap-from-scratch.sh:394`
  already exports `SIMPLE_BOOTSTRAP_DIAG=1` in those modes, so they will now
  pass it through and produce a different Stage 3 args hash than before. This
  is a real behaviour change for those non-default modes, and it is the
  intended one.

## Unverified

- No full bootstrap was run. The ablation exercises the real transcribed-exec
  plumbing with a stub in the compiler's place; it does not prove a probe
  produces useful output inside a real Stage 3 compile.
- `scripts/check/lib/bootstrap-stage3/self-test.shs` exits 0 after this change
  but prints nothing at all. A silent exit 0 is not evidence in this repo, so
  it is recorded as unverified rather than as a pass.

## Next

Use the pass-through in the next Stage 3 cycle rather than a hand-reconstructed
replay. If a needed probe is not on the allowlist, add the name to
`bootstrap_stage3_diagnostic_env` after confirming its gate is print-only, and
re-run the ablation gate.
