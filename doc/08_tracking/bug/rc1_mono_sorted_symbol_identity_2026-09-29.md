# RC1 monomorphization copies native dictionary keys

## Evidence

Admitted producer:
`build/phase_snapshots/phase1_1790651890_phase2_1790653273/simple`.
The schema-generator closure reaches HIR 62/62 but crashes after reporting four
generic functions and zero specializations.

`build/native_probe/config-layout/layout-cycle2-schema-crash.log` reproduces
the crash under LLDB at `PostMonoVerifier.verify_module + 8724`: projection of
`f.return_type.kind` dereferences zero. The ordinary native run's macOS report
`simple-2026-09-29-124226.ips` independently records the same PC and null address,
first-function cursor zero, and zero type-parameters carrier. A second debugger
attempt hits the previously recorded frontend lifetime fault instead; no more
diagnostic launches were made.

Earlier `layout-cycle1-key-debug.log` proved that two native SymbolId copies
with numeric ID zero do not compare equal as erased dictionary keys: lookup
with the original key returned a valid aggregate, while the copied key returned
NIL. The layout validator now avoids that lookup by consuming values directly.

## Monomorphization source defect

`monomorphize_modules` activates rewriting when generics exist. Its
`sorted_symbol_keys` helper explicitly copies SymbolId keys into an array and
copies them again while sorting. Step 2 uses those copied keys to look up
functions. This repeats the proven aggregate-key identity hazard: failed lookup
produces a zero-filled function that survives into verification. The post-mono
nil comparison checks tagged NIL (3), so raw zero can pass that comparison and
crash during field projection. No verifier checks were weakened.

## Repair and resource behavior

Sort scalar indices of a directly obtained function-value array, using
precomputed numeric symbol IDs. Rewrite those actual function values. Ascending
symbol order and stable insertion sorting remain unchanged. Sorting swaps only
integers, avoiding repeated copies of whole function bodies. Two scalar arrays
replace the copied-key array; there are no reconstructed-key dictionary reads.

The existing mono native-regression spec now asserts the retained template's
name, symbol ID, type-parameter count, and return kind, beyond its prior counters.

The connection from sorted-key copying to the schema failure is source-level
evidence combined with independently proven native key-identity behavior.
Rebuilt schema execution and the extended regression are still required.
General aggregate-key equality and the intermittent frontend lifetime crash
remain separate open problems.

**STATUS: WARN — scoped source repair; rebuilt verification pending.**
