<!-- codex-research -->
# Existing Simple test-binary workflow, 2026-10-03

Scope: clarify and repair Simple's existing native test facility, not introduce
a C++ testing framework. User requests compiler/interpreter/loader test binaries
for LLVM and Cranelift, querying their case counts before execution.

Source inspected: release/1.0 at
`d865e086eae9a0a9d92e51691b86f30721d39c9e`. The older Windows working checkout
does not contain all recently landed runner/backend/thread fixes; inspect the
actual release revision rather than infer current behavior from that checkout.

| Evidence owner | Confirmed behavior |
|---|---|
| `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` | Native/binary and compile/SMF modes; explicit LLVM/Cranelift backend parsing |
| `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` | `run_test_file_native` selects explicit AOT from `native_backend`; pins producer SHA, uses native build, directly runs output |
| Same owner, `native_test_compile_args_with_threads` | Existing `native-build --backend ... --entry-closure --runtime-bundle core-c-bootstrap --threads ... --cache-dir ... --output ...` invocation |
| `src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl` | Existing generated result-bearing spec entry and zero-executed-example rejection |
| `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` | `list_tests_static` reads source; not compiled registry enumeration |
| `scripts/bootstrap/run-native-aot-suite.shs` | Existing suite wrapper pins producer/runtime, requests explicit AOT, keeps artifacts and validates native evidence |

The inspected execution path builds per-spec executables. Existing direct
subsystem entries and any aggregate generator still need full trace and live
verification before claiming the requested six aggregate products. In
particular, no binary-owned listing flag has been verified by this research.
Neither a source search miss nor this per-spec implementation proves there is
no other aggregate/list feature. Research that feature before changing its
architecture.

No new native test was run for this documentation update. Current compiler
repairs proceed independently. A separately explored GoogleTest bridge was a
misinterpretation of the request; it is excluded from the implementation and
from these commits. Its probe outcomes are not Simple subsystem test evidence.

Knowledge lookup: canonical SPipe resolved through the reviewed compatibility
checkout `.spipe/spipe` and its `scripts/find-spipe.mjs --agent-guide`; common
wiki/skill indexes were read. This is project implementation knowledge; common
SPipe guidance should route users here and explain research-before-replacement.
No external framework comparison or feature-option selection is needed for
this correction to the already selected existing-feature workflow.

Follow the [maintained native test guide](../../07_guide/infra/testing/native_test_binary_workflow.md).
