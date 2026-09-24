<!-- codex-research -->
# Windows Server native Simple Container: local research

Checked 2026-09-27. This is a design input, not a claim of working Windows support.

The selected requirement is `doc/02_requirements/feature/windows_server_process_container.md`: run Windows programs in process-isolated Windows Server containers, sharing the host kernel, with no VM fallback. The common value layer already provides `ContainerHostRequirementV1`, `ContainerHostCapabilityV1`, `RuntimeIdentityV1`, `RuntimeOperationV1`, and the lifecycle transition oracle in `src/lib/common/contracts/container/`. It can reject `windows/linux`, `virtual-machine`, and mismatched capability claims, but it cannot prove actual HCS mode or image compatibility.

Only a Linux host provider exists under `src/lib/nogc_async_mut/container/providers/`. There is no Windows HCS/containerd adapter, scoped Windows broker, executable native Windows system spec, or live Windows Server fixture in this worktree. The existing Windows TODO and test plan therefore remain open. SimpleOS owns a separate kernel scheduler provider; macOS uses a separate native sandbox design. Shared code should carry copied identity/lifecycle values, not Windows handles or a common subprocess implementation.

The current plan names `containerd → runhcs → HCS`. More precisely, containerd and its Windows shim own HCS handles and native lifetime; a Simple adapter would own the client connection, request policy, identity-bound journal, and validation of observed IDs. A direct HCS binding would be a later, separately designed alternative. An SDN capability receipt is an observation, not permission to call the runtime.

The common `native-container` token is too broad to prove process isolation. The Windows leaf needs typed host build, image OS build/digest, requested/observed isolation mode, runtime identity, compute identity, and authorization evidence before setting `launch_capable=true`. The user has selected process isolation but has not selected the ordinary-client privilege policy. Do not claim rootless Windows execution from `ContainerUser` or a daemon pipe.

Related local artifacts: [cross-host architecture](../../04_architecture/simple_container_cross_host.md), [Windows requirements](../../02_requirements/feature/windows_server_process_container.md), [Windows test plan](../../03_plan/sys_test/windows_server_process_container.md), and [Windows TODO](../../08_tracking/todo/simple_container_windows_server_qualification_2026-09-27.md).
