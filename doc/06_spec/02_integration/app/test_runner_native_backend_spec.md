# Native backend executable assertion outcomes

Executable specification: `test/02_integration/app/test_runner_native_backend_spec.spl`.

Requirement: REQ-NATIVE-004. Prerequisites: admitted self-hosted producer selected through `SIMPLE_BINARY`, its frozen runtime authority selected through `SIMPLE_RUNTIME_PATH` when required, and an admitted Windows native toolchain.

For LLVM, create a temporary Simple BDD fixture asserting that six times seven equals forty-two. Build it with the explicit LLVM native backend and execute the emitted artifact directly. Expect one passing assertion and no failures or execution error. Rewrite the fixture to assert forty-three; build and execute again. Expect zero passing assertions and one failure.

Next rewrite the fixture as a main function printing text without executing assertions. Build and execute it with the same backend. Expect a failed runner result reporting no assertions, with execution resource evidence retained.

Repeat all three outcomes using Cranelift. Both scenarios remove their source fixture after collecting results. Private executable caches are removed on completion unless `--keep-artifacts` requests retention.

Status: executable spec authored; runtime evidence pending admitted producer. This manual does not claim a passing integration run or full compiler/interpreter/loader inventory coverage.
