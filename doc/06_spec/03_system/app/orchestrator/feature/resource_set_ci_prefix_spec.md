# ResourceSet CI value and prefix preservation

Status: **NOT_RUN — awaiting verification**. Authored from executable assertions;
not SPipe-generated evidence and not a passing CI execution record.

- Spec: `test/03_system/app/orchestrator/feature/resource_set_ci_prefix_spec.spl`
- Oracle: `test/fixtures/orchestration/resource_set_ci_prefix_native_probe.spl`,
  `resource_set_ci_prefix_checks()`
- Existing fixtures: `test/fixtures/orchestration/ci_job_process.sdn` and
  `test/fixtures/orchestration/ci_pipeline.sdn`
- Authored labels: CFG-01, CFG-02, from
  `doc/02_requirements/feature/caret_distributed_orchestrator.md`; the table below
  maps partial assertion intent only.

## Setup

Run from the repository root. The oracle loads both fixtures using bounded
regular-file reads. Its local `ci_list(source)` helper indents the original
source as one child of an ordinary ResourceList. It preserves the parsed child
and its position; it does not fabricate a successful decoder or execute jobs.

## Scenario: preserve values through legacy and unified decoding

1. Decode the Job fixture with `decode_job` and with `decode_resource_set`.
   Check that the unified result contains exactly one Job.
2. Compare that Job's name, backoff limit and first container command with the
   legacy decoded values. An unexpected resource kind fails the assertion.
3. Decode the Pipeline fixture directly with `decode_pipeline` and as the
   single nested child of a ResourceList through `decode_resource_set`.
4. Check the nested kind is Pipeline and compare its name, job count and
   fourth job's run_after list to the directly decoded Pipeline.

These comparisons protect the shared strict-envelope/value-decoder refactor;
they do not infer semantic equality from successful parsing alone.

## Scenario continuation: retain source paths after nesting

| Mutation | Direct-path assertion | Nested assertion |
|---|---|---|
| Job backoffLimit becomes -1 | `spec.backoffLimit` | Kind `range`, path `spec.items.0.spec.backoffLimit`, positive line and column |
| Pipeline fourth job runPolicy becomes sometimes | `spec.jobs.3.runPolicy` | Kind `unsupported_run_policy`, path `spec.items.0.spec.jobs.3.runPolicy`, positive line |
| Add unexpected:true to Job spec | Not checked by this oracle | Kind `unknown_field`, path `spec.items.0.spec.unexpected` |
| Repeat Job backoffLimit | Not checked by this oracle | Rejection kind `duplicate_key` |

The nested errors must refer to the original child within the ResourceList.
The oracle does not rebuild a span map or replace nested errors with root-only
paths. Duplicate-key detection must remain at the strict parse boundary.

## Assertion mapping and limits

| Authored labels | Concrete assertions |
|---|---|
| CFG-01 | Checked Job and Pipeline typed values agree through direct and unified decoding |
| CFG-02 | Invalid amounts/policies and unknown/duplicate fields fail with the asserted nested paths and coordinates |

Unreadable fixtures, unexpected kinds, missing jobs or changed values cause
real assertion failures. No build task, scheduler acceptance, controller host
mutation or provider launch occurs in this test. No runtime, admitted SSpec,
SPipe/manual maintenance or coverage result has been produced here. Full signed
dispatch and provider nonce/inspection acceptance remain separate and NOT_RUN.
