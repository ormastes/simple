# Staged closure selection authentication

Executable: `test/01_unit/app/compiler_entrypoint/entry_closure_staged_selection_spec.spl`.

Three examples compare split preparation/admission with the existing complete selection, reject generation-byte corruption after preparation, and reject snapshot-manifest corruption after preparation. All use actual SCV publication and admission functions. The pinned P1 interpreter executed all three successfully.

Native lifetime fixtures:

- `test/fixtures/bootstrap/parse_closure_staged_scratch.spl`: actual scratch helper, four-stage peak comparison, nested struct/array survival, borrowed/refused owners, failed adoption, OS publication copy and post-session cache replacement.
- `test/fixtures/bootstrap/parse_closure_staged_coordinator.spl`: deterministic domain services for the production coordinator owner. Assemble with `python3 scripts/check/assemble-parse-closure-native-probe.py --output build/probe.spl`; `--owner PATH` supplies the original owner for the red control.

Compile the generated source using pinned P1 `compile --native --backend=llvm` with `SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap` and `SIMPLE_RUNTIME_PATH` pointing at the diagnostic current-C archive. Guard compilation at 1 GiB/90 seconds and execution at 256 MiB/15 seconds. The fixture contains explicit diagnostic initialization and a fail-closed unused thread hook; neither substitutes for a production compiler/runtime qualification.

Detailed limits, paths, hashes and outcomes are recorded in `doc/08_tracking/bug/scv_staged_closure_scratch_2026_10_29.sdn`.
