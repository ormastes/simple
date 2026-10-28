# Native coverage has no executable probe producer

The 2026-10-28 runner coverage attempt used the `aa58...` runtime generation's
Rust seed as its compiler child. It timed out after 240,034 ms while building
the coverage wrapper; the outer process timed out at 302 seconds. The fixture
never ran. A first-line diagnostic was a source excerpt, not a usable cause.
Evidence: `/tmp/runner-source-routes-evidence-20261028/final-runner/coverage-attempt3`.

A separate direct probe with the existing pure-Simple phase-2 producer
`stage2-simple-aliasfix` compiled and ran a real branch in 15.085 seconds,
with peak tree RSS 354,080 KiB under a 2 GiB cap. `SIMPLE_COVERAGE=1` enabled
the runtime collector, but its decision and condition tables were empty.
This disproves that changing compiler selection alone repairs coverage.
Evidence: `/tmp/coverage-debug-evidence-20261028/probe*` and `producer.sha256`.
No phase-2 compiler was rebuilt.

At release source `ff74e6226c5`, `mir_instruction_kinds.spl` defines typed
`DecisionProbe` and `ConditionProbe`. `mir_coverage_probe_admission.spl`
explicitly rejects them with `MIRCOV-PROBE-E-UNLOWERED`. There is no production
insertion/lowering path. The parser's `ast_coverage_inventory.spl` can declare
zero-count obligations, but declarations do not prove executed outcomes.

## Required generic compiler work

1. Preserve each authored decision and condition identity from the flat AST
   through HIR into MIR, including generated wrapper source mapping.
2. Insert typed probes at evaluation points, preserving short circuiting and
   exactly-once evaluation. Associate conditions with their parent decision.
3. Lower admitted probes to the existing core runtime ABI (decision ID,
   result, authored path, line, column; conditions also carry condition ID).
   Keep backend rejection for unsupported or malformed probes.
4. Make optimizer and native caches retain probes and bind instrumentation
   mode, source inventory, and schema to cached artifacts.
5. Build and qualify a new producer separately. Require real branch outcomes,
   uncovered declarations, short-circuit controls, and failing test controls.
   Until this happens, generic automatic coverage remains unfinished.

## Explicit partial runner self-measurement

`SIMPLE_RUNNER_SELF_COVERAGE_OUTPUT=/absolute/output.sdn` on the test-runner
application enables six explicit production admission decision probes in
`native_test_request_error`. The application writes standard
`decision-condition-v1` rows with an immutable six-site denominator, including
zero-hit sites. It does not change child compiler settings. The metadata states
`whole_runner_coverage: false` and `automatic_source_coverage: false`.
The scope excludes every other runner function, condition coverage, and MC/DC.
An unexecuted site is reported with zero outcomes, never as covered.

The fixed collector avoids enabling `SIMPLE_COVERAGE` in the parent and all its
children. It measures the six declared branch results once at their real owner
call sites. This separate artifact cannot satisfy the ordinary `--coverage`
gate or substitute for full runner coverage.

Only the entry process contributes to this receipt. The entry consumes the
output environment variable before launching descendants, so a child runner
cannot overwrite the parent's evidence. Parallel workers are outside this
scope. Current native verification covers the production admission owner and
standard coverage parser; the whole application entry requires a separate
runner rebuild and end-to-end qualification when disk headroom permits.

The existing phase-2 producer formats an `i64` loaded from an array as a
tagged runtime value through both interpolation and `.to_text()`: line 65
became `<value:0x41>`. Typed scalar locals did not repair it. The renderer uses
the existing `std.sffi.host.raw_i64_to_string` scalar ABI, verified by native
green/red/empty controls. This remains a compiler formatting defect rather
than a reason to reinterpret corrupt rows as valid counts.

## Native coverage reader loses a count of three

The direct standard-reader integration then exposed a separate defect: six
correctly observed decisions became five covered decisions after
`parse_coverage_state_sdn`. Re-rendering the parsed state preserved false counts
6, 5, 4, 2, and 1, but changed the count 3 to 0. The reader uses
`decision_false[key] ?? 0` after decoding the dictionary value to a raw integer;
the existing producer treats raw 3 as the optional nil tag. A count must be
loaded only after dictionary membership is checked, without optional coalescing
on the decoded integer. Apply this to decision and condition reads and merges.
Evidence: `/tmp/coverage-debug-evidence-20261028/standard-parser-diagnostic.sdn`.
The native integration fixture deliberately remains red until that service
defect is fixed. The separate raw probe green/red/empty controls passed.

Build `test/fixtures/runner_self_coverage/main.spl` with an existing producer,
then run `python3 scripts/check/check-runner-self-coverage.py /path/to/binary
--output /path/to/evidence`. The controls exercise all six true/false outcomes,
retain all six declarations with no execution, and ensure an intentionally
incorrect expectation still exits nonzero with a coverage artifact.
