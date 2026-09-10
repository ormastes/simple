# Lane SIMPLEORCH — Simple Orchestrator, Simple Container, Simple CI orchestration

Goal (user, 2026-09-07): "with spipe skill, imple container orchestration, simple
container for hosts imple. apply to simple ci orchestration."

Research (authoritative design):
`doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md`
— requirements ORCH-001..016, acceptance catalog §14, milestones M0..M10 §15.2.

## Binary identity (M0)

Measured 2026-09-07, unchanged across the whole session (bracketed before/after):

```
readlink -f bin/simple -> bin/release/aarch64-unknown-linux-gnu/simple
50093192 bytes, mtime 2026-09-06 09:59:11
bin/simple --version -> "WARNING: this Rust-built Simple binary is a bootstrap seed only"
```

**Every verdict in this lane so far is RUST SEED evidence, not self-hosted.**
A self-hosted re-run is required before any release-bound claim.

## Ownership boundary — do not collide with these lanes

This lane does **NOT** edit `src/os/services/container/**`. Research §8.4 requires
parity fixtures before any extraction, and four lanes already own that tree:

| Lane | Owns |
|---|---|
| `container_live_wiring` | `VfsManager.container_view` live lookup enforcement |
| `simpleos_harden_t3ctr_manager` | `container_manager.spl` |
| `simpleos_harden_t4oci_import` | `oci_import.spl` |
| `process-isolation` | scheduler/process isolation |

Existing CI surface to extend later, not replace: `src/app/ci/`,
`src/app/container_packaging/`.

## runtime_need

```
runtime_need:      none
facade_checked:    std.common.sdn.parser (parse_with_spans_and_issues), std.io_runtime.file_read
chosen_path:       reuse-facade
rejected_shortcuts: none
```

M1 needs zero `rt_*`: the canonical SDN parser already emits duplicate-key
`SdnIssue` records with 1-based line/col, so the strict profile is "any issue
rejects" rather than a new detector.

## Milestones

| M | Deliverable | Status |
|---|---|---|
| M0 | Snapshot + runnable toolchain inventory | **PARTIAL** — binary identity recorded above; `src/lib/nogc_async_mut/kernel_plugin/` re-checked 2026-09-07 and is **still absent**, so M2 stays blocked |
| M1 | Strict SDN resource schemas + canonical resource model | **IMPLEMENTED, extended in slice 2** — spec green on SEED only; self-hosted verdict NOT_RUN. Pod + Deployment; slice 2 added `command` and class-aware artifact rules, so the slice-2 blob hash for `resource_v1.spl` supersedes the slice-1 one |
| M2 | Shared runtime interfaces, static composition, local journal, controller model | **PARTIAL** — see the SUPERSEDED note below. The synchronous half (runtime provider shape, CI runner, receipts) landed 2026-09-07; the no-GC async hot-path substrate (ORCH-015) is still absent |
| M3 | Linux real local vertical slice | **PARTIAL** — the `native-process` lane executes real host processes end to end; the `native-container` lane is BLOCKED on host privilege (TODO DB rows 275-277) |
| M4 | Windows native process provider | NOT_RUN |
| M5 | macOS native workload/sandbox lane | NOT_RUN |
| M6 | Deployment/Job/Service controllers + first-cohort mixed network | **PARTIAL** — the Job/Pipeline CI controller landed (expansion + ordered execution + receipts). `Service`, `Deployment` reconciliation and the cross-host network matrix are NOT_RUN |
| M7 | Replicated-state production profile, failure/security suite | NOT_RUN |
| M8 | FreeBSD jail/ocijail | NOT_RUN |
| M9 | SimpleOS integration, real booted-network tests | NOT_RUN |
| M10 | Optional profiles (pod networking, storage, VM adapters) | NOT_RUN |

## M1 — what landed

`src/lib/common/contracts/orchestration/resource_v1.spl` (596 lines): canonical
typed `ResourceV1` (Pod, Deployment) plus `decode_resource(source) ->
Result<ResourceV1, RejectionV1>`, the strict SDN decode profile. Rejects, each
with a dotted schema path and 1-based source line/col:

duplicate key · unknown field · wrong type · missing required field · empty
name/containers · unsupported apiVersion/kind/os/runtimeClass/networkProfile ·
`native-container` on macos · both `image` and `artifactSetRef` · neither ·
duplicate container name · non-integer CPU/memory quantity · request above limit ·
containerPort out of 1..65535 · negative replicas · empty `matchLabels` ·
selector/template label disagreement.

Quantities canonicalize to integers at decode time (CPU millicores, memory
bytes); no float reaches the resource model. `digits_to_int` deliberately avoids
`text.to_int()`, which fails open to 0 on garbage.

Fixtures: `test/fixtures/orchestration/{echo_deployment,duplicate_key,
unknown_field,selector_mismatch,macos_native_container}.sdn`.

Spec: `test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl`
covers LANG-002/003/007 and MAC-003.

### Verdict (seed, `--no-session-daemon`)

```
green   -> Results: 7 total, 7 passed, 0 failed
sabotage-> Results: 7 total, 5 passed, 2 failed
reverted-> Results: 7 total, 7 passed, 0 failed
```

Sabotage disabled the duplicate-key issue gate and both selector/template
mismatch branches (`if false:`); exactly the two matching examples went red and
no others, so neither arm is vacuous. Both were restored from a pre-sabotage copy
and re-verified byte-identical (`if false:` count 0).

## Findings worth keeping

- **`namespace` is a hard-rejected identifier.** `struct ObjectMetaV1: namespace:
  text` is refused by the compiler's common-mistake check ("Use 'mod' for modules
  instead of 'namespace'"), so the field is named `ns` while the SDN key stays
  `namespace`. Filed:
  `doc/08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md`.
- **SDN needs quotes around a value containing a colon.** `image:
  registry.example/probe@sha256:aa` parses as a nested mapping, so `as_text`
  rejects it on type. Correct parser behaviour; fixtures quote such values.
- `parse_with_spans_and_issues` gives spans keyed by the same dotted path the
  schema uses, so rejections get real line/col for free.

## Next slice (not started)

1. `Job` + `Service` + `Node` + `ArtifactSet` in the same contract.
2. Local journal + `PodBinding` (M2 model half — the parts that do not need the
   async kernel-plugin layer).
3. Simple manifest-builder API (§5.4) — deferred: a second authoring path with
   one consumer. LANG-005 stays NOT_RUN until a second manifest exists.
4. CI application (`Pipeline`/`PipelineRun` expanding to `Job`s) needs `Job` and
   a node agent first; it is not reachable from M1.

## Gate verdicts (seed, 2026-09-07)

```
spec        Results: 7 total, 7 passed, 0 failed   (--no-session-daemon)
spipe-docgen 0 stubs, 1 warning (length recommendation only)
lint        PASS — 1 file(s) checked (0 cached, 1 linted), Lint passed: all files clean
root-guard  FAILED with 211 violation(s) — PRE-EXISTING RED (all tools/* and var/lib);
            0 of the 211 name any path this lane created. Not caused here, not fixed here.
```

## Blob insurance (shared working tree can silently wipe in-progress files)

Recorded with `git hash-object -w`; restore with `git cat-file -p <sha> > <path>`.

```
17b357a1779ec9e72dac94e8b3ab6acc67870060  src/lib/common/contracts/orchestration/resource_v1.spl
f05b9354a47a4acbfa3b20452c2b2a84fecd2d2f  test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl
05c1ca1646242774908447cce438a82a7967ad3b  test/fixtures/orchestration/echo_deployment.sdn
22b9b487db0ae53bd875b67e86af9a00a1cfbe3d  test/fixtures/orchestration/duplicate_key.sdn
b96742ea1aba9487f5ef1880f78887fb0d31ceaa  test/fixtures/orchestration/unknown_field.sdn
7b29f3e50147f9680aadf3251d897def51e51ed4  test/fixtures/orchestration/selector_mismatch.sdn
29cdcdc69d9af636ae15e10fc20a9460691b7b23  test/fixtures/orchestration/macos_native_container.sdn
05f8555e2c13e0f9ce16cfeacd087231ca2dfc65  doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md
92c0d7d9e927bff1caa03668e95d7386be745370  doc/00_llm_process/feature_expert/simple_orchestrator/skill.md
6bccd128f0e3431cd44e5e7355506e236a48fb84  doc/08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md
baf6115afdbe307635e869c5002a276283af1c36  doc/06_spec/01_unit/lib/common/contracts/orchestration/resource_v1_spec.md
```

---

## SUPERSEDED claim (2026-09-07) — "M2+ is blocked on the async kernel-plugin layer"

An earlier revision of this file, of the lane memory, and of the feature wiki
said M2 and everything after it were blocked because
`src/lib/nogc_async_mut/kernel_plugin/` is absent.

**The absence is still true. The conclusion drawn from it was too broad.**
What is missing is the no-GC async / bounded-hot-path substrate (ORCH-015,
research §7.6). Disproving evidence: a SYNCHRONOUS Job and CI runner —
Pipeline decode, dependency ordering, real process launch, receipts — was built
and executed on 2026-09-07 using only `app.io.mod`'s process facade and the
existing SDN parser. It touches none of that substrate. The claim is kept, not
deleted, so the next reader can see what the reasoning error was: an absent
dependency was treated as blocking work that does not depend on it.

Still genuinely blocked on the async substrate: bounded operation pools,
backpressure, generational provider pinning, cancellation/retirement — i.e. the
parts of M2 that ORCH-015 actually names.

## Slice 2 (2026-09-07) — Job, Pipeline, and the CI application

### What landed

| Path | What |
|---|---|
| `src/lib/common/contracts/orchestration/ci_v1.spl` | `Job`, `Pipeline`, strict decode, and `expand_pipeline` — a Pipeline expands into ordinary Jobs in deterministic dependency order (Kahn, declaration-order tie-break). Refuses unresolved `jobTemplateRef`, unknown `runAfter`, self-edge, cycle, unsupported `runPolicy`, wrong `kind`. |
| `src/app/ci/pipeline_runner.spl` | The CI application: walks the expanded order, launches each Job through a runtime lane, writes one `JobReceiptV1` per job and one `RunReceiptV1` per run. Verdicts PASS/FAIL/NOT_RUN/BLOCKED. |
| `resource_v1.spl` (extended) | `command: [text]` with Kubernetes semantics; the strict toolkit (`as_dict`/`require`/`only_known`/`decode_pod_spec`/…) is now `pub` and reused, not copied. Artifact rules are now class-aware: a `native-container` needs exactly one of `image`/`artifactSetRef`; a `native-sandbox`/`native-process` needs `command` and must NOT name an image. |
| `src/lib/common/sdn/parser.spl` | Fixed: block-sequence entries were reported as duplicate keys, which made every strict consumer refuse any multi-entry sequence. Record: `doc/08_tracking/bug/sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md`. |

### Execution policy actually implemented

- An upstream failure stops its dependents (`NOT_RUN`, naming the upstream) and
  does NOT stop independent jobs — research §12.2.
- `runPolicy: always` runs after an upstream failure for diagnostics and never
  turns the run verdict green.
- A `native-container` job is refused as `BLOCKED` with the host probe's reason.
  **It is never downgraded to a host process** — asserted as `verdict == BLOCKED`,
  `attempt == 0`, empty stdout, and proved non-vacuous by the sabotage arm below
  (ORCH-006 negative, research §4.1). The spec also checks the receipt reason
  equals the probe reason; that is a copy check inside one process, not
  independent corroboration — do not cite it as evidence.
- `probe_linux_oci()` is a POSITIVE probe: it nests a mount namespace inside a
  user namespace — the exact operation runc's nsexec performs — instead of
  reading `runc --version` and inferring.

### Verdicts (seed, `--no-session-daemon`)

```
resource_v1_spec.spl                 Results:  7 total,  7 passed, 0 failed
ci_v1_spec.spl                       Results: 11 total, 11 passed, 0 failed
pipeline_runner_spec.spl             Results:  3 total,  3 passed, 0 failed   <- REAL process execution
sdn_sequence_duplicate_key_spec.spl  Results:  3 total,  3 passed, 0 failed
```

Neighbouring SDN suites after the parser fix, no regressions:
`sdn_spans_spec.spl` 16/16, `sdn/sdn_block_sequence_spec.spl` 7/7.

### Sabotage (three independent arms, one pass)

Disabled dependency edges in `expand_pipeline`, the upstream-failure gate in the
runner, and the `native-container` refusal branch:

```
green    -> ci_v1 11/0   runner 3/0
sabotaged-> ci_v1  9/2   runner 1/2
reverted -> ci_v1 11/0   runner 3/0     (both files restored byte-identical, `if false:` count 0)
```

Red examples were exactly: cycle detection, out-of-declaration-order ordering,
upstream-failure propagation, and the container refusal. No unrelated example
moved. The ordering oracle was strengthened first — the original diamond had
declaration order equal to topological order, so it could not have detected a
pass-through; a pipeline that declares its dependent FIRST was added.

The nonce oracle: each run mints `SIMPLEORCH-<ms>` and every job echoes it. The
receipt must contain that run's nonce, so a receipt cannot be satisfied by
fabricated or stale text (research §13.4). Both `stdout` and `exit_code` are
asserted, never `.0` alone.

### Container lane — BLOCKED on this host, with privilege this lane must not take

`docker` socket is group-denied; `runc --rootless` dies at
`nsexec: failed to unshare remaining namespaces: Operation not permitted`
because `kernel.apparmor_restrict_unprivileged_userns=1` and `newuidmap` is
absent. Filed with the measured evidence, the two possible unblocks, and the
exact resume command:
`doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md`
→ TODO DB rows **275, 276, 277**.

### Gate verdicts for this slice

```
spipe-docgen  0 stubs on all three new specs
lint          ci_v1.spl                PASS, clean
              pipeline_runner.spl      BLOCKED BY LINTER — not a finding
              sdn/parser.spl           BLOCKED BY LINTER — not a finding
```

The linter aborts with `error: semantic: class CodeLine has no field named code`
depending on the linted file's import closure. Proven not to be this lane's
code: the same abort happens on `parser.spl` with this lane's 4-line change
reverted, and on a 4-line file whose only import is `ci_v1` — content that
itself lints clean. Filed:
`doc/08_tracking/bug/lint_codeline_has_no_field_code_closure_dependent_2026-09-07.md`.

### Next slice

1. Unblock or hand off the container lane (TODO 275-277) — needs the machine
   owner's decision, not more code.
2. `Service` + `EndpointSlice`, then `Deployment` reconciliation (M6 proper).
3. A local intent journal so a runner crash is recoverable (M2's synchronous
   remainder); the async substrate stays a dependency for ORCH-015 only.
4. Re-run every verdict here on a self-hosted binary — all of it is seed
   evidence.

## Blob insurance, slice 2

```
904fc2d9253c3cfc67835824137dd1fc4accf7dd  src/lib/common/contracts/orchestration/ci_v1.spl
ca59c18bef8d4bc1cb84a220f8459f3a7847ea0d  src/lib/common/contracts/orchestration/resource_v1.spl
386bdd5a102fa0bb9868e4936d075b2cedeec623  src/app/ci/pipeline_runner.spl
38b22244b9883b264e9235493d6ba0480c24bc78  src/lib/common/sdn/parser.spl
c47a9f33b4e56cf937ae5844a2d16d15ed991c91  test/01_unit/lib/common/contracts/orchestration/ci_v1_spec.spl
68ea6730002bb850acd694f4e397a695136dbe93  test/02_integration/app/ci/pipeline_runner_spec.spl
534086401ae8bdd2e94ef44b36e88755273bcab0  test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl
46d7bc90e02f8d5e24fe4df55d92916ce1d3a3ac  test/fixtures/orchestration/ci_pipeline.sdn
77d1f83fda75819daf156e0fb3d52aa7de229bc2  test/fixtures/orchestration/ci_pipeline_cycle.sdn
bb5356e0054e6db0c4dc47c86150dcf736ddf88a  test/fixtures/orchestration/ci_job_process.sdn
68c4d2ea9a7b1fa125ad934dfe2e5957490b2e12  test/fixtures/orchestration/ci_job_container.sdn
bb94269fcb3338a3fb21955a83992c5d3bb54104  doc/08_tracking/bug/sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md
e57ecefaecc3c95bd075a0c11d1713f97f3f2d00  doc/08_tracking/bug/lint_codeline_has_no_field_code_closure_dependent_2026-09-07.md
834a31c8704942cf7f57b1bc0ee8abca5b3199a3  doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md
```

## Known side effect of this slice: TODO DB ids shifted

`bin/simple todo-scan` assigns ids positionally, so inserting three rows
renumbered the row after them: the rendering lane's row moved 275 -> 278
(`doc/03_plan/sys_test/render_lane_mission_showcase.md:53`). That row's own text
says "see TODO DB row 277", which now names this lane's
`simpleorch container-evidence` row.

The reference was ALREADY dangling before this slice — the DB held 276 rows
(ids 0..275), so id 277 did not exist. It is now wrong rather than absent. Left
for the rendering lane's owner rather than edited from here; a numeric
cross-reference into a positionally-numbered generated table is the underlying
fragility. `doc/TODO.md` and `todo_db.sdn` are auto-generated (+13/-7 lines
total) and land only if the user wants them.

### Blob hashes refreshed after the final edits

```
35b7f8a1386017ea2b3e344223395f10b50970f9  test/02_integration/app/ci/pipeline_runner_spec.spl
baf6115afdbe307635e869c5002a276283af1c36  doc/06_spec/01_unit/lib/common/contracts/orchestration/resource_v1_spec.md
85e96352f86eb7cfa97387493adb6c5b5e048bcc  doc/06_spec/01_unit/lib/common/contracts/orchestration/ci_v1_spec.md
62f541b1e594c1d76afd7b44a52f0de0d93b6d49  doc/06_spec/02_integration/app/ci/pipeline_runner_spec.md
d5ab13ee9f7e3fd4e24af6f7af02dcb17ccc9059  doc/06_spec/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.md
6a92e2ae0b1fa9f560e26503bafbce8926a1d5a8  doc/00_llm_process/feature_expert/simple_orchestrator/skill.md
```

## Slice 2b (2026-09-07) — Podman is the default engine

`probe_linux_oci` became `probe_container_lane()`: it tries **podman**, then
docker, then bare runc, and reports `engine` and `privilege` as SEPARATE fields
from `available`. Podman is the default because rootless is its normal mode — a
CI node should not have to hand a daemon root to run a build.

Two platform facts encoded in the probe rather than left to a reader:

- **Podman on Windows is refused outright** for `native-container`. `podman
  machine` runs a Linux guest (WSL2/Hyper-V) and has no Windows-container
  backend, so it cannot produce a process-isolated Windows container. Windows
  candidates are containerd+runhcs or Docker's Windows-containers backend. This
  corrects the research §4.2 row that listed Podman beside containerd for
  Windows.
- **Root is per host, not per container.** Linux rootless needs userns +
  subuid/subgid + `newuidmap`/`newgidmap` (+ cgroup v2 delegation for enforced
  limits). Windows process isolation needs Administrator; a FreeBSD jail needs
  root; neither has a rootless equivalent. `privilege` is `unknown` whenever the
  lane is unavailable and is never inferred from the engine name — rootless
  podman and a root docker daemon both merely "answered `--version`".

New host-independent oracle (5th example in the runner spec): an unavailable
lane claims no engine and no privilege; an available lane names one of the three
engines and states root or rootless, never unknown; docker never claims
rootless. It asserts invariants rather than this host's answer, so it stays
meaningful on a host where the lane works.

Measured receipt after the change — the probe now names the binding constraint
of the first candidate it reaches, which with podman absent is docker:

```
boxed | native-container | BLOCKED | exit=0 | stdout=[] |
  docker-daemon-unreachable: permission denied while trying to connect to the
  docker API at unix:///var/run/docker.sock
```

Verdicts after the change: resource_v1 7/7, ci_v1 11/11, **pipeline_runner 5/5**,
sdn_sequence_duplicate_key 3/3.

**Source caveat:** HTTPS fetching is unavailable in this session
(`native HTTP supports http:// only; HTTPS requires the TLS runtime`), so the
podman-on-Windows and per-host-root claims are working knowledge plus the host
probes quoted above — NOT re-verified against vendor docs. Research addendum
carries the same caveat. Re-verify before any release claim.

Research addendum: `doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md`
§ "Addendum 2026-09-07". TODO rows 275-277 updated: podman+uidmap+userns lift is
now the preferred unblock, docker group membership the root fallback.

### Blob hashes, slice 2b

```
51715e22768c1494656da793cfa8e4aa88cf73e6  src/app/ci/pipeline_runner.spl
66b3cc994bbda2563c1c3db97873156f408660e8  test/02_integration/app/ci/pipeline_runner_spec.spl
a4dc1c73fdfb415cb92028c3c571346c3c5c1b40  doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md
13a46fbb26ec6688da0d34b61ff73462c7865c01  doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md
```
