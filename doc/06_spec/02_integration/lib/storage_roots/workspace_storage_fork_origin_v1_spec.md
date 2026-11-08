# Workspace owner process-origin isolation

**Status:** authored manual, not generated docgen. The one Simple SSpec wrapper
is **AUTHORED_UNRUN**. Its exact Core-C fixture separately passed 182 parent and
49 child checks, once, on source `257e6f8fc28254efbd96ea9f34ed62685721fd17`.

**Source:** `test/02_integration/lib/storage_roots/workspace_storage_fork_origin_v1_spec.spl`.
**Helper:** `test/fixtures/orchestration/workspace_storage_fork_origin_checks_v1.spl`.
**Native fixture:** `src/runtime/test/workspace_storage_fork_origin_v1_selfcheck.c`.

## Should refuse inherited owners and retain quarantine after recovery

1. Supply the source-bound native artifact from the
   [native receipt](workspace_storage_fork_origin_v1_native/evidence.sdn).
   The helper verifies its exact SHA-256 before launching it.
2. Execute it with a 20-second timeout and 64 KiB output bound. Require exit 0,
   empty stderr, the complete native PASS statement and the explicit
   NOT_QUALIFIED statement. Missing artifacts, signals, timeouts, exit 77 and
   altered output fail; no successful skip exists.
3. Verify the artifact identity again. The reported parent count may increase
   when the actual poll is interrupted; the native executable itself enforces
   every assertion and the full child response protocol.

The native executable includes the actual owner source under symbol aliases
so it can hold the real private registry mutex across `fork`. The child must
refuse every public entry before inherited lock/token access, preserve sentinel
descriptors and perform no string-cache allocation. The parent independently
receives the child's completed check count, reaps its own child and verifies
its registry, mutex and subsequent native calls remain intact.

The initial origin observation verifies an actual PID-namespace object. Native
device/inode mismatch prevention is checked against that real identity; no
privileged namespace clone is performed. A separately labelled one-shot syscall
fault injects `stat` EIO during guarded release. After the real syscall succeeds
again, the registry must stay quarantined and refuse before the retained mutex.
This injected failure is not reported as an actual host `/proc` outage.

The loan mechanism case uses local metadata with no native handles, roles or
quota admission. It verifies the real pair-release helper can finish while a
competing thread holds the registry gate, and that a changed generation or busy
state refuses both releases. It does not prove positive XFS preparation.

**Pending gates:** admitted Simple execution/docgen and core/MCP checks; actual
namespace clone transitions; configured quota/keeper preparation; Windows native
handles and selected-user access. Earlier storage 73, observer 61 and preparation
163 component results are separate historical evidence, not rerun here.

<details><summary>Executable SSpec</summary>

```simple
describe "Workspace owner process-origin isolation":
    it "should refuse inherited owners before locks and retain quarantine after namespace-query recovery":
        step("Verify the exact native artifact and execute actual fork, quarantine and loan-contention checks")
        workspace_storage_fork_native_checks_v1("build/workspace-storage-fork-origin-v1/native-fork-origin",
            "b1536e280b58b93323183eef33cf619211b34c8819e799340e97ed13f785ab0c")
```

</details>
