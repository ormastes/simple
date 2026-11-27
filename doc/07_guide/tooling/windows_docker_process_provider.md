# Windows Docker process-provider integration

Status: AWAITING_VERIFICATION. One live lifecycle probe passed (below). That is
evidence, not deployment qualification: the controller launch schema, SPipe and
manual gates are still NOT_RUN.

## Live probe evidence (2026-11-22)

Host: Windows 11 Pro build 26300.10075 (DESKTOP-VMF96U6). Engine: Docker CE 29.10.0
(`dockerd` service `docker-ce`, `C:\Program Files\DockerCE\docker.exe`) listening on
`npipe:////./pipe/docker_engine`, which is the only endpoint the provider admits.
Docker Desktop and its WSL Linux engine were stopped, because Desktop's Linux engine
owns `docker_engine` while it runs. Engine ID `844f2a31-da1d-40b2-8e4d-7a8daf2e56cf`,
kernel `10.0 26300 (26100.1.amd64fre.ge_release.240331-1435)`. Image:
`mcr.microsoft.com/windows/servercore@sha256:a43c2d41a3d6e940dec865731e2f5db5c3e03f705f5300ef0b5817d3e01ecfb1`
(tag `ltsc2025`), image ID `sha256:793f7bf4733a1846f4c7f31c14dff835a8ad348613e979c943cd804c54a3ba16`,
OsVersion `10.0.26100.33828`. Before this run no image pin existed anywhere: specs use
placeholder digests. The 26100 image runs process-isolated on the 26300 host.

Entry: `src/app/test/windows_docker_live_probe.spl`, run by
`sh scripts/check/check-windows-docker-live-probe.shs <probe.exe> <image-ref>`. The
wrapper reads the pins from the engine and the image and passes them in.

| check | Phase 1 (seed `ac2e90625c2a`, interpreter) | Phase 2 (admitted Stage 2, native-build) |
|---|---|---|
| live prepare/create/start/wait/logs/destroy, `cmd.exe /c echo` | N/A by design: refused before any Docker effect (`child environment capture requires the matching native C provider`, `process_ops.spl:1959`) | PASS: logs `simple-wdp-ok`, wait exit 0, exact-ID absence confirmed |
| non-zero exit propagation (`WDP_EXIT=3`) | N/A (same refusal) | PASS: wait exit 3 |
| inside an smux pane (`--serve`, `new`, `send`, `capture`, `stop-server`) | PASS: smux served by Phase 1; the pane ran `docker run --rm --isolation=process ... cmd /c echo` and printed `smux-container-ok` | PASS: the pane ran the wrapper + Phase 2 probe, verdict PASS |
| Windows provider scripted specs (10 files) | 121 passed, 0 failed, 1 NOT_RUN, after realigning 3 stale V6 expectations (`doc/08_tracking/bug/windows_docker_specs_stale_after_v6_network_2026-11-22.md`). NOT_RUN is the cooperative-progress case in `docker_server_network_v6_spec.spl`, which is native-lane only by owner decision; see `doc/08_tracking/bug/windows_scripted_docker_progress_needs_native_thread_on_seed_2026-11-22.md` | N/A (bootstrap CLI has no `test`) |

Use the Windows provider's typed request and explicit policy. Its host kernel and
image OS-version strings must exactly match the selected observed pair; choosing
a compatible pair remains the deployment owner's responsibility. Pin Docker's
absolute executable, local named pipe, engine identity, immutable image reference
and image ID. The provider invokes native bounded capture with a minimal child
environment and never invokes a command shell.

The caller owns a durable per-attempt journal. Persist the original request and
prepared intent before create and retain the exact returned native ID before
start. A response lost after create leaves an uncertain attempt; do not recreate
it, search by name, or prune. Recovery needs the exact native ID and validates all
ownership labels against the original request. Failure to inspect is not absence.

Run the provider only under the trusted controller authority. This implementation
does not make direct Docker-pipe access safe for independent untrusted clients.
No Windows variant has yet been admitted in the controller's Linux launch schema.
Mounts, broad network policies and automatic runtime installation are outside this
slice. A failure never selects Hyper-V, WSL or another engine.

Before enabling deployment, complete the Windows live test plan and the admitted
compiler/SPipe/manual gates. The historical Windows 11 23H2 / Server Core 2022
fixture is not a replacement for source-matched current evidence. Report explicit
NOT_RUN for absent fixture/compiler evidence rather than skipping into PASS.
