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
- **`rm --force --time 0` can answer 125 while succeeding.** With a tty
  client still attached, podman reports "could not be stopped: given PID did
  not die within timeout" although SIGKILL was delivered; the container is
  gone moments later. `podman_session_reap_v1` repeats removal (5 attempts)
  until `container exists` says absent. Found by `/quit` with a live agent —
  a smoke that always `/kill`s first never reaches it.
- **Default detach keys.** An attached tty reserves ctrl-p,ctrl-q, swallowing
  the agent's own Ctrl-P and leaving a running container behind a detached
  client. The layer passes `--detach-keys=`.
- **A name is not ownership.** Agent ids restart at `a1` in every cs, so two
  cs on one session derive the same container name. The first version reaped
  by name whenever the roster spec said `--container`; a cs whose launch was
  REFUSED then force-removed the other cs's live container on `/quit` or
  `/kill`. Removal now needs both: the process recorded a successful spawn
  (`cs_container_mark_launched`), and the engine reports this process's
  `io.simpleorch.session.instance` label (`podman_session_reap_instance_v1`,
  which then removes by the inspected container ID). `/reap` is the one
  deliberate exception and says so in the help text.
- **Session names are hashed into the owner label**: `cs-<readable>-<10 hex
  of sha256(session)>`; "a b" and "a-b" used to share an owner.
- **Read-write mounts are policed on the normalised path**: `..` is refused,
  and `/`, `$HOME`, `/home`, `/var`, `/tmp`, ... (exact) and `/etc`, `/usr`,
  `/lib*`, `/dev`, `/proc`, `/sys`, ... (whole tree) cannot be mounted rw.
- **`container inspect` on a missing container exits 125 on podman, 1 on
  docker.** The test-runner backend calls a container gone only for that exit
  plus "no such container"; a dead daemon or timeout is "unknown" and fails
  the run.
- **Names are per session, not per cs process.** A launch refuses when
  `cs-<session>-<agent>` already exists instead of removing it (it may belong
  to a second cs). `/reap` is the explicit recovery after a killed cs.
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
`cs-<session>-<agent>` under owner `cs-<session>`. `/kill` reaps it; the end
of either cs loop (`/quit`, EOF, Ctrl-C/D) reaps every containerized agent;
both delete the client's stderr spool. A cs killed by SIGKILL cannot clean up:
the next cs on that session refuses to reuse the name and `/reap` removes
everything under the owner label.

## Real bug-fixing agent in a container (2026-11-12)

- Image: `config/container/caret_agent.Containerfile` (debian trixie-slim +
  git + libgcc-s1 + procps, 213 MB, no compiler). busybox lacks git.
- A git **worktree** workspace needs the main repo's `.git` mounted rw
  (`--container-mount <main>/.git:<main>/.git:rw`); otherwise git inside says
  "not a git repository". The repo-local identity then applies.
  `--container-env KEY=VALUE` covers an identity that lives in `~/.gitconfig`.
- The `--config` file is outside the repo: mount it ro explicitly.
- Push stays host-side: no credential is mounted, on purpose.
- Proof: session `ctr-proof-1`, agent a1 fixed a one-line expectation, ran the
  spec inside (1 passed) and committed 60 s after the prompt; `/kill`, `/reap`
  and `/quit` left 0 containers and 0 spools. Exact launch line:
  `doc/07_guide/app/llm/local_llm_slang_caret_setup.md` section 8.

## Measurements (2026-11-12, aarch64, podman 4.9.3 rootless, runc)

- Live spec: normal exit 0, failing exit 7, timeout kill (exit -1), orphan
  recovery by label — `podman ps -a` empty after each.
- cs `caret:dummy` and `caret:slang` in `busybox:1.36`: container `Up` ~100 s,
  agent TUI rendered in the pane, chat text delivered to the container tty,
  `/kill a1` -> "killed pane id3, removed container cs-<session>-a1",
  0 owned / 0 total containers, 0 `cs-<session>-*.stderr` files afterwards.
- `/quit` and stdin EOF with the agent still running: container removed,
  spool removed. cs killed with SIGKILL: container left in `stopping` (its
  tty vanished), relaunch on that session refused while it existed, and it
  had removed itself (`--rm`) before `/reap` ran ~20 s later. `/reap` against
  a real leftover is covered by the live spec's orphan example.
- Model round trip from inside the container (same flags, one-shot):
  `--provider slang --model Qwen3-Coder-30B-A3B-Q4_K_M --prompt "Reply with
  exactly: container-pong"` printed `container-pong`, exit 0. The default
  model name `slang-local` is rejected by the server; pass the served model.
- Not observed: a reply rendered in the cs pane. The piped (non-tty) cs loop
  only repaints on input, and the dummy agent shows the same, so this is a
  capture limit of the smoke, not a container problem.

## host_cleanup_spec: five stacked causes (0/10 -> 10/10)

Each one hid the next; none was the first visible error's fault.

1. Fixture JSON one brace short (`}}` collapse) -> `engine-info-json-limit`.
2. Three `distributed_authority_snapshot_v2` functions imported but not `pub`.
3. `openat` / `geteuid` declared in `retained_file_abi.spl`'s Linux branch but
   absent from the interpreter's POSIX table
   (`src/compiler_rust/compiler/src/interpreter_extern/posix_abi.rs`). A libc
   name needs no runtime twin; it needs an entry there plus the drift pin in
   `extern_drift_tests.rs`.
4. **Private directories made with `dir_create`.** That is 0777 & ~umask —
   0775 under the usual desktop umask 0002 — and
   `retained_directory_open_trusted_v1` then refuses the directory
   (`SCVDB_DIR_FINAL_UNTRUSTED`). The journal root, terminal-wait, cleanup
   store and exec-publication directories now use
   `directory_create_private` (`std.nogc_sync_mut.io.dir_entry_ops`, 0700 for
   every missing component; a umask can only clear bits). A spec that
   pre-creates such a directory must do the same. Setting `umask 022` in the
   shell did not change the outcome here; do not rely on it.
5. The cleanup fixture supplied two scripted clock samples; the path reads
   three (destroy admission, destroy pre-exec check, absence observation) ->
   `absence-observation-clock-unavailable`.

Also: an inline `std.a.b.fn(...)` expression is not resolved by the
interpreter (`variable std not found`); import the name. `opt.?` on a nil
option evaluates to nil, so `assert(x.?)` reports "condition evaluated to
nil" rather than the real upstream error — print the error field first.

## Open

- `oci_engine_policy_spec` "executes an exact scripted absolute route" and
  `oci_execution_user_v2_spec:34` (`with` not found) fail for unrelated reasons.
- Provider journal compaction and a provider-level label sweep are not built.
