# Cold-HIR diagnostic fixture omits its production helper

- Bug ID: `cold_hir_diagnostic_helper_closure_2026_10_11`
- GitHub: https://github.com/ormastes/simple/issues/3112
- Severity: P1
- Status: OPEN; source/template controls PASS, native compilation and output verification UNRUN.
- Source-reviewed base tree: `9a95f2ae00ec3080ef9bbfaf9508e8a8d4fc2c56`.

The exact driver mismatch branch now calls `cold_hir_source_mismatch_evidence_v1`, while `scripts/check/lib/check-cold-hir-path-diagnostic.py` extracted only that branch into an isolated source fixture. Its template neither defined nor imported the helper, and its `ProbeHir` carried only `path` although the helper also reads `name`. The expected-output oracle separately retained the older root/source/hir format and omitted empty-source evidence. These are source-composition findings; no native run is claimed for the broken merged fixture.

The repair extracts the helper verbatim from `src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl`, supplies a minimal fixture `HirModule` with path/name fields, and updates the five-case oracle for index/module fields and the empty-source line. The diagnostic receipt binds the helper source, exact extracted helper and template hashes. PASS also requires unchanged helper and template bytes after real execution, alongside the existing driver/producer checks. Compiler production logic remains unchanged.

`python3 -B -I scripts/check/tests/cold_hir_path_diagnostic_contract_test.py -v` passed six bounded controls: complete fixture/type closure, exact source propagation, missing/duplicate helper rejection, missing/duplicate insertion-slot rejection, changed caller-boundary rejection and exact current oracle lines. These are source/template checks, not compiled Simple execution. Existing five real diagnostic scenarios remain in the native harness.

Closure requires running `scripts/check/check-cold-hir-path-diagnostic.shs` with an admitted producer/runtime and verifying the real fixture compilation/output, helper/driver/template stability, and producer identity. Current compiled/native/Stage 3/release qualification remains pending. Keep the issue OPEN.
