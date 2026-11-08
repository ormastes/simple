# Pinned workspace preparation native components

**Status:** authored manual, not generated docgen. The one Simple SSpec scenario
is **AUTHORED_UNRUN**. Separately, its actual Core-C fixture completed 163 dynamic
checks; that is native component evidence, not execution of the SSpec wrapper.

**Source:** `test/02_integration/lib/storage_roots/workspace_executable_preparation_v1_spec.spl`.
**Helper:** `test/fixtures/orchestration/workspace_executable_preparation_checks_v1.spl`.

## Should execute real component checks without claiming chmod success

1. Supply the exact source-bound native artifact identified in
   [attempt 3](workspace_executable_preparation_v1_native/attempt3/evidence.sdn).
   The helper verifies its SHA-256 before execution.
2. Run the actual executable with a 20-second timeout and 64 KiB output bound.
   Require exit 0, empty stderr and the exact two-line result: the 163-check
   component PASS and the explicit full-positive-preparation BLOCKED statement.
3. Verify the artifact hash again. Missing/changed executables, a signal, a
   timeout, exit 77 or different output fail this scenario rather than skip it.

The native fixture checks independent SHA vectors across block/chunk boundaries,
the sparse file size limit, actual clock deadlines, invalid native owners,
unchanged original file bytes/mode, directory traversal and real mount namespace,
mountinfo and statx identity. Unrelated opaque nsfs roots are accepted as metadata;
selected filesystem security roots still require canonical absolute paths.

The first run was [blocked by valid nsfs metadata](workspace_executable_preparation_v1_native/attempt1/evidence.sdn).
The corrected-source binary then hit an additional harness logical-file limit
([SIGXFSZ](workspace_executable_preparation_v1_native/attempt2/evidence.sdn)).
Attempt 3 executed that same binary with the exact sparse logical limit allowed,
while retaining the allocated-byte monitoring bound. Neither failure is erased.

Actual admitted XFS quota, a signed keeper/preparation stage, enforced guest
read-only inputs/writable outputs, successful owner-execute mode effects,
Windows access and full Host/common execution remain separate pending gates.
Registry fork-child isolation also requires its separate repair and regression;
this component evidence does not cover that boundary.

<details><summary>Executable SSpec</summary>

```simple
describe "Pinned workspace preparation native components":
    it "should execute real hash, deadline, mount and refusal checks without claiming chmod success":
        step("Verify the exact native fixture and execute its real production-owner component checks")
        workspace_preparation_native_checks_v1("build/workspace-executable-prep-v1/native-preparation-r2",
            "557686f94830b947542c6674f89d3a137830398cdea6c3385bfb76c59eeab346")
```

</details>
