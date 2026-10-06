# Managed bootstrap test graph: implementation contract

Status: **candidate plan; automatic graph wiring is not implemented**.
The Phase1 callback is implemented separately. Native helper fixes remain unqualified.

Use the existing compiled `managed-tasks` owner and `BuildRunV1` codec. Never launch
another shell background scheduler. One host budget is 80 jobs; each admitted
build/test task requests 20, so at most four tasks hold capacity. Waiting tasks
hold no capacity. Resource release requires the existing owned-tree collection.

The already admitted Phase2 producer and Hello proof are prerequisites for this
downstream graph. Its producer and source digests must remain separate identities.

| Task | Prerequisites | Required retained output |
|---|---|---|
| `phase1_tests_completed` | admitted seed and configured source | terminal receipt containing the actual test verdict, categories, logs, seed/config hashes |
| `managed-phase3` | admitted Phase2 + Hello | existing Phase3 completion |
| `managed-phase4` | admitted Phase2 + Hello | existing early-P4 completion, explicitly distinguished from P3→P4 |
| `phase2_{backend}_product_{suite}_prepare` ×6 | admitted Phase2 + Hello | native build, authenticated generated source, enumeration, one real first-case smoke |
| `phase2_{backend}_product_{suite}_full` ×6 | corresponding prepare and Phase1 terminal | canonical full-suite execution in a fresh process |
| `phase2_product_matrix` | all six terminal product receipts | canonical six-product verifier and full inventory coverage |

Backends are LLVM and Cranelift; suites are compiler, interpreter and loader.
Preparation, native build, enumeration and first-case smoke do not depend on
Phase1 tests. Only full-suite execution waits for Phase1 terminal completion.
Phase1 assertion failure does not block authorized later execution. This needs
an explicitly named *completion* task: its control success means its child tree
was collected and its actual failed/PASS/infra verdict was retained, never that
tests passed. The final gate must inspect the test verdict separately.

Similarly, a failed first-case assertion must remain a failed result while
allowing remaining cases. Failed native compilation blocks only that product's
runtime dependents; independent products continue. Infrastructure uncertainty
retains ownership and cannot be converted to a successful completion receipt.

Required implementation gaps before automatic wiring:

1. Split the canonical product callback into prepare and remaining operations.
   Existing `--resume` only admits an entirely successful previous backend; it
   cannot authenticate a partially prepared product and must not be weakened.
2. Bind the prepare output transport to the successor task through the existing
   manager's artifact/producer factory, including binary, source, compiler,
   runtime, options, build/enumeration and smoke receipt hashes. A path alone
   is insufficient. Reuse only idle compatible cache directories under leases.
3. Reuse the renderer's --case-id selector for the first registered executable
   case. Keep smoke counts separate. After Phase1 terminal, start a fresh full
   suite process using the existing canonical verifier. The first case is
   intentionally repeated to preserve fixture/global state; its smoke result
   contributes zero to full-suite counts. No complement-ID or synthetic union
   transport is required for this policy.
4. Compose phase tasks and product tasks into one N-task inventory and resource
   policy, with all task contexts admitted. The current two-task `managed-phases`
   entrypoint cannot enforce this whole graph by adding shell background jobs.
5. Publish the generated-source SCV authority after rendering and before native
   product compilation. The helper's earlier source snapshot cannot cover bytes
   that did not yet exist.

Remote fix `163e0afaac2` already supplies explicit Phase2 matrix provenance and
resume validation; it is reused as `0f9bc06b552`, not reimplemented.
The inventory of 4079 canonical authored files remains separate from legacy
out-of-root files. Neither six diagnostic mains nor a selected-case smoke proves
that full coverage. Commented blocked test bodies must remain registered with
bug-linked failing assertions; no exclusions may silently become PASS.
