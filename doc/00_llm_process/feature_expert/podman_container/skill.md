# Feature Expert — Podman-backed Simple container sessions

## Role

Own the small, grant-free podman path of the Simple container layer and its
consumers: caret-suite agents launched in a container from `cs`, and the legacy
test-runner container backend. The signed/journalled orchestration path
(`LinuxOciRuntimeProviderV1`) belongs to `simple_orchestrator`; this entry only
records what it shares with that path.

## Feature Links

- Layer: `src/lib/nogc_sync_mut/container_session/podman_session_v1.spl`
- cs consumer: `src/app/llm_caret/cs_container.spl`, wired in `cs_dashboard.spl`
  (`launch:` / `pane:kill`) and `cs_main.spl` (`/quit`)
- Test-runner consumer: `src/lib/nogc_sync_mut/test_runner/test_runner_container.spl`
- Specs: `test/01_unit/lib/nogc_sync_mut/container_session/podman_session_v1_spec.spl`,
  `test/01_unit/app/llm_caret/cs_container_spec.spl`,
  `test/01_unit/lib/nogc_sync_mut/test_runner/container_bounded_run_spec.spl`,
  live (opt-in): `test/03_system/app/container/feature/podman_session_live_spec.spl`

## Contract

- One workload = one `podman run --rm --name <n> --label
  io.simpleorch.session.owner=<o> --label io.simpleorch.session.name=<n>`.
- The layer writes no file (no cidfile, no journal). The container is the only
  artifact, so cleanup is provable with `podman ps -a`.
- Every effect goes through an injected runner `fn([text], i64) -> (text, text, i64)`.

## Traps (each one was hit)

- **`--rm` does not survive a killed client.** SIGKILL, a closed pty or a
  timeout of the `podman run` client leaves the container (seen in `Created`
  and `Up` states on podman 4.9.3). Always reap by exact name
  (`rm --force --volumes --time 0 --ignore`) and prove absence with
  `container exists` (exit 1). `podman_session_run_v1` does this after every
  outcome; a killed supervisor is recovered with `podman_session_reap_owner_v1`.
- **`{{` / `}}` collapse to one brace in every double-quoted literal.** A Go
  template must be written `{{{{.Names}}}}`. Three inspect formats and the
  health probe reached podman as single-brace text while their scripted specs,
  comparing against the same collapsed literal, stayed green. A JSON literal
  ending in `}}` loses a brace the same way; write the tail as `}" + "}"`.
  Assert on the rendered length or bytes, not on another literal.
- **`engine-info-json-limit` also means "unbalanced".** The depth scan returns
  the same reason for a document one brace short. It was correct; the fixtures
  were malformed.
- **Bare `use a.b.name` is not a selective import for the JIT.** With several
  co-compiled `process_run_timeout` definitions the HIR lowering reported the
  call as ambiguous and cs fell back to the interpreter. Use
  `use std.io_runtime.{process_run_timeout}`.
- **Seed binary in a minimal image.** `busybox:1.36` (glibc 2.41) lacks
  `libgcc_s.so.1`; mount the host copy read-only:
  `--container-mount /lib/aarch64-linux-gnu/libgcc_s.so.1:/lib/libgcc_s.so.1`.
- **Durable tombstones are intentional.** The OCI provider's
  `runtime-intent-<pod>-<attempt>-<generation>` record in phase `destroyed`
  fences re-create and makes destroy idempotent after restart
  (`oci_runtime_v1_spec`, "reads a durable destroyed tombstone ..."). Do not
  delete it on destroy. Compaction, if wanted, must be an explicit prune of
  older generations after the owner's cleanup receipt.
- **Fixture roots.** `host_execution_fixture_v2` tracks its `/tmp` roots;
  consumer specs sweep them from `after_each`. Never glob-delete
  `/tmp/host-execution-fixture-*`: other sessions run the same specs.

## cs usage

```
/launch caret:slang/<model> --container busybox:1.36 \
    --container-mount /lib/aarch64-linux-gnu/libgcc_s.so.1:/lib/libgcc_s.so.1 \
    --workspace /abs/worktree
```

Repo root is mounted read-only, `--workspace` read-write, the resolved Simple
binary read-only, all at the same paths; network defaults to `host` so the
agent reaches the slang server on `localhost:8721`. The container is named
`cs-<session>-<agent>` under owner `cs-<session>`. `/kill` and `/quit` reap it
and delete the client's stderr spool.

## Measurements (2026-11-12, aarch64, podman 4.9.3 rootless, runc)

- Live spec: normal exit 0, failing exit 7, timeout kill (exit -1), orphan
  recovery by label — `podman ps -a` empty after each.
- cs `caret:dummy` and `caret:slang` in `busybox:1.36`: container `Up` ~100 s,
  agent TUI rendered in the pane, chat text delivered to the container tty,
  `/kill a1` -> "killed pane id3, removed container cs-<session>-a1",
  0 owned / 0 total containers, 0 `cs-<session>-*.stderr` files afterwards.
- Not observed: a model reply from the slang server inside the container
  within 90 s of sending the prompt.

## Open

- `host_cleanup_spec` is red on the interpreter: `retained_file_abi` declares
  raw libc `openat`, a native-only boundary the seed interpreter cannot call.
- `oci_engine_policy_spec` "executes an exact scripted absolute route" and
  `oci_execution_user_v2_spec:34` (`with` not found) fail for unrelated reasons.
- Provider journal compaction and a provider-level label sweep are not built.
