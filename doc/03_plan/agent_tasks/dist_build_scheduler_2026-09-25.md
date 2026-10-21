<!-- codex-design -->
# Parallel agent plan — distributed build and fast feedback

**Status:** Full functional scope requested; N2 numerical NFR selected; benchmark evidence pending. Read-only Astra, scheduler and hook/CI research completed. Two disjoint P0 contract lanes drafted source and focused specs; runtime verification is blocked by the self-hosted test-runner crash.

**Merge owner:** Codex build-platform integrator.

**Final reviewer:** Astra or the highest-capability available reviewer, independent of each source lane.
**Manual reviewer:** Same final reviewer, reading generated `doc/06_spec` pages as operator manuals.

**Local handoff:** [2026-09-26 host evidence and parallel owner lanes](dist_build_local_handoff_2026-09-26.md). TODO DB rows 338–341 track the fixture, Linux two-node, N2 benchmark and signed-CI acceptance work; each lane must claim its files before editing.

## Contract frozen by primary design owner before implementation fan-out

Shared type/interface names: `SnapshotManifest`, `ToolchainManifest`, `InputManifest`, `ActionSpec`, `AttemptSpec`, `NodeCapabilities`, `ActionResultCandidate`, `AcceptedResult`, `GateReceipt`, `ResourceStore`, `ResourceState`, `CompilerProvider`, `ExecutionContext`. Preserve semantic action identity separately from attempt/fence and test-validation identity. Confirm actual module placement against the compiler/app/lib layer routes and freeze versioned SDN/binary schemas before editing producers/consumers in parallel.

Shared manual flow helper text: `step("Select exact source and policy snapshot")`, `step("Plan affected build and checks")`, `step("Dispatch admitted actions")`, `step("Validate and publish results")`, `step("Verify current integration candidate")`. Proposed setup/checker helper names: `given_pinned_snapshot`, `given_two_node_fixture`, `given_outgoing_refs`, `given_submodule_pin`, `expect_complete_action_manifest`, `expect_current_fence`, `expect_required_gate_receipt`, `expect_pin_reachable`. A scaffold without a real action/checker must use `assert(false)` or `fail(...)`; never a passing placeholder. The design owner may refine names once, before SSpec sidecars begin, and then all lanes use the frozen set.

## Lanes and ownership

| Lane | Depends on | Owned area and deliverable | Acceptance responsibility |
|---|---|---|---|
| C — Contract/identity (primary) | User selection | Canonical action/input/attempt/result and gate-receipt schemas, knowledge route, baseline fixtures; owner of shared interface changes. | Golden vectors, incomplete-input rejection and baseline receipt. |
| A — Action/native build | C | `src/app/build/targets/`, native-build input-manifest consumer, verified warm receipt/CAS integration, attempt-private output paths; coordinate `src/compiler` identity edits only through C. | Imports, generated inputs, dependencies and same-mtime mutations; clean/cached parity. |
| S — Scheduler/transport | C, then A's admitted action contract | Local DAG, resource tokens, durable attempt ledger, fenced broker; later node-agent transport and exact toolchain matching. | Dependent ordering, bounded resource use, crash/retry/stale-result and real two-node fixtures. |
| O — Container/Orchestrator worker | C and S admission contract | App-owned composition of build actions with `PodSpecV1`/`JobV1` and `RuntimeProviderV1`; truthful physical/execution/target compatibility; Linux OCI execution first, individually qualified OS providers later. | No sandbox/process downgrade, no cross-OS false PASS, immutable inputs/private output, real Linux container worker and per-host BLOCKED/UNSUPPORTED rows. |
| F — Local hook/receipt speed | C | Existing hook dispatcher, `run-gate-tier.shs`, must-check registry, `land.shs`, signed receipt path. **`check-push-must-pass.shs` is dirty in another lane now; wait for ownership or work in an isolated branch without folding that diff.** | Staged bytes, all outgoing refs, JJ/Git seams, complete wall time, preserved mandatory destination and no hidden timeout PASS. |
| G — GitHub admission | C and F receipt contract | Base-owned controller, unprivileged PR/fork execution, exact merge-candidate check mapping, current ruleset audit; preserve existing required contexts. Add scoped signed local build admission with exact artifact evidence and full-build fallback. | Fork, policy self-edit, missing/skipped child, base drift, stale/revoked receipt, artifact mismatch, signer/job/platform mismatch and changed-check-code fixtures. |
| R — Repository dependencies | C | `.gitmodules`/gitlink inventory, selected clean-fetch canaries, pinned exception scope, branch policy and worktree isolation; no immediate directory migration. | Pin mismatch, unreachable child, optional over-fetch, changed-pin invalidation and protected-ref paths. |
| H — Clang/native adapter | C and A | Strict header-policy evaluator, exact invocation capture, CMake launcher, native policy stamps and complete native PCH/PCM/BMI context. | Archive HC catalogue, including policy-only Ninja no-op, no-cache ancestor and ABI domains. |
| V — Independent verification/performance | C through H as applicable | SPipe SSpec scenarios/manuals, differential clean builds, target-specific speed benchmarks, docs and release evidence. | Every selected `REQ-NNN`, selected NFRs, zero stubs, exact fixture/host and unsupported rows visible. |

Read-only research sidecars have completed local source scans, including Astra's existing container/Orchestrator contract review. Draft common action, scheduler-transition, native-manifest, signed-admission and container-admission files remain unverified. The O lane's pure admission adapter is not a real worker/provider. Lower-model implementation sidecars own bounded disjoint files and require highest-capability review. Parallel lane writes use isolated worktrees or explicit disjoint ownership and distinct `build/` outputs. No lane may add its own action hash, CAS, ledger, hook policy engine or unreviewed required status name.

## Merge order and conflict rules

1. Integrate C schemas and tests. Record exact owners of existing dirty files and do not absorb unrelated changes.
2. Run A, F and R concurrently on disjoint source areas; G starts from F's receipt contract. H can build policy fixtures after C and native execution wiring after A.
3. Integrate A before S local executor; S remote transport follows local fault tests. F's feedback changes can land independently once its obligations and GitHub admission remain sound.
4. Merge G, R and H into an exact integration-candidate test. V reviews each lane, the generated manuals and the merged behavior before any new required check or release admission.
5. Astra reviews cross-lane assumptions and final architecture/evidence. Resolve conflicts in shared contracts at C, then rerun only affected criteria once. Do not repeat unchanged green checks.

The [build-platform plan](../compiler/build_system/dist_build_scheduler_2026-09-25.md) owns phase dependencies. The source paths above are planning ownership, not authority to edit another active session's dirty files or change remote policy settings.

## Current S-to-A consumer handoff

The S lane now retains regular `.a`/`.lib` and object bytes under accepted
manifest digests. `retained_binary_cas.spl` verifies the appropriate format
before dependency admission or SFTP; `parent_artifact_export.spl` installs one
digest-pinned policy row into a protected caller directory. These APIs are
source drafts until pure-Simple verification resumes.

The primary owner added a sequential whole-graph source runner and a separate
entrypoint over the existing parent journal/remote service. The entrypoint
requires a graph-manifest digest from protected administrator policy, checks
the exact manifest bytes before loading requests, and keeps request-byte pins
inside the manifest. Its planner spec
was authored in a disjoint sidecar lane and is unrun under the current runtime
cap. Astra reviewed the runner; shared CAS, multi-active resume and global
priority findings were fixed by the primary owner. The merge owner must next
qualify a cached compiled entrypoint, journal restart and real two-worker
producer/consumer execution before calling lane S integrated. The final
reviewer must examine the entrypoint and spec after these fixes.

Astra's cold-link review found that a complete consumer request cannot exist
before producer output bytes do. The owner added protected ordered link
templates and retained-output resolution in new scheduler files. The S lane
now has source for a versioned, digest-pinned link template and staged
controller entrypoint. It validates template producer membership, declared
outputs, link worker/profile and capacity before
producer execution; replay the accepted owner; derive a second graph from the
original exact producer wires plus the resolved link request; resume the same
link action/fence after restart. The C lane reviews identity encoding, the A
lane supplies a real archive-to-executable fixture, and V reviews generated
manual and live two-node evidence. An unresolved template is never executable.
The next S/C handoff is administrator plan issuance: snapshot exact input wires,
publish one bounded record atomically under an administrator-owned directory,
and permit execution by restricted record ID without caller overrides. The
current staged CLI digest flag relies on a trusted launcher and is not itself
authorization. The merge owner is the primary Codex agent; Astra is final
architecture reviewer before native qualification.
The canonical bounded record parser and content-addressed no-replace store
exist in source, but the S/C handoff still owns independent trusted-root
selection, administrator-only approval of issuance, revocation semantics and a
restricted production entrypoint. An arbitrary path or digest supplied by a
caller cannot grant authorization.
The issuer source now shares CLI preflight loading, checks the independently
approved digest against the complete staged input set, and publishes the record
only on a valid preparation. The protected approval and installed root remain
external inputs; no user-facing issuance command or production admission is
claimed.
The installed root still needs descriptor-based owner, mode, and no-follow
verification on every launch. Its [P1 authority bug](../../08_tracking/bug/dist_build_issued_root_authority_2026-09-27.md)
records the exact acceptance cases; a fixed path and digest check are not
sufficient authority for a privileged issued entrypoint.
The S lane added a dedicated issued-record source entrypoint, and the wrapper
now names only its distinct native basename. The merge owner must build and
qualify that exact native artifact, install the administrator root with
protected ancestors, and keep the raw diagnostic controller outside privileged
credential/state access. Record deletion revokes only future launches; an
already loaded record can continue unless its active attempt is reconciled.

The A lane currently owns dirty `target_executor.spl`. Its local executable
link path hashes a library at `target_output_path` and builds a dependency
manifest from that mutable path. The merge owner must add an explicit accepted
producer route that materializes the exact accepted archive into an attempt
private input directory, validates its digest after copying, and passes that
private path to the linker. It must not turn `target_action_reusable` on until
the complete native closure receipt is proven. Keep the local source-building
route for targets with no accepted distributed producer. The S lane must not
edit or overwrite A's live dirty executor file.

Acceptance requires a real library v1 → executable link, a library-only v2
change that changes the linked result, and refusal of a stale fence, corrupt
archive CAS, missing accepted manifest or changed private copy. Run that
fixture on the deployed pure-Simple runtime and a real Linux OCI worker before
calling the end-to-end consumer path complete.

## G-lane signed-build controller handoff

`src/app/build/signed_build_controller.spl` now composes protected bootstrap
gate validation, pinned OpenSSH V2 signature verification, and a copied private
artifact decision. Its caller must supply base-owned manifest bytes/digest,
current candidate expectation, independently collected `GateReceipt`, pinned
signer/KRL configuration and an already downloaded artifact. `FULL_BUILD`
returns no artifact path; `REUSE` returns only the copied private path. The
currently dirty `.github/workflows/build-binaries.yml` belongs to another
session and is not modified by this lane. The G-lane merge owner must place a
base-owned controller before unprivileged PR build execution, retain a
reporting required context in both decisions, consume only the returned
private artifact path, and exercise invalid signer/gate/artifact plus full
build fallback. Existing MinGW seed fallback has a distinct artifact name and
must never be accepted as Stage 2 evidence. Source composition and focused
rejection tests have no production-runtime PASS or live GitHub admission.

Astra's read-only workflow review selected the existing Linux Stage 2 job as
the first reuse target. Its seed build, smoke, upload, job name and ordinary
build fallback stay active; MinGW remains separate. The verifier must be built
from approved base-owned source, derive repository/PR/base/head and the exact
integration-candidate tree independently, obtain protected signer/revocation
policy and observed mandatory gates, and isolate untrusted receipt/signature/
artifact inputs. Only a `REUSE` result with a private artifact path may
replace Stage 2 build work. Any verifier absence, error, identity drift or
artifact mismatch runs the ordinary build; no privileged PR trigger may
execute candidate code. The current workflow and push hook are dirty in other
active lanes, so their owners must wire and qualify this handoff before a
GitHub required context can claim signed reuse.

## Astra production-critical replan (2026-09-26)

The critical path is a qualified self-hosted runtime, then installed issued
controllers and worker, a real Linux two-node graph, cold staged compile/link
and export, and recovery qualification. N2 targets are selected but unverified; timing measurements alone do not admit a threshold.

| Lane | Exclusive owner files | Dependency and acceptance |
|---|---|---|
| A — native qualification | New `scripts/check/check-dist-issued-native.shs` and installation evidence | Consume the runtime from its current owner; build exact issued graph/staged and worker entrypoints, record hashes/provenance, reject raw or stale binaries. No bootstrap retry in this capped session. |
| B — whole graph | `two_node_qualification*.spl` and matching system spec/manual | After A and two provisioned workers, prove proposed/accepted attempt identity, CAS/dependency bytes, cleanup acknowledgements, and attempt-free repeat; reject mixed versions and faults. |
| C — staged link | New `two_node_staged_qualification.spl` and dedicated spec/manual | After A, prove producer acceptance, dynamic link identity, mounted operand, second-worker link, protected export and executable result. |
| D — Clang | `src/app/build/clang_policy/`, `cmake/SimpleClangPolicy.cmake`, dedicated specs | Compose top-level observation/lock/Ninja/acceptance; prove unchanged policy no-op, changed policy rebuild despite timestamp collision, and unrelated-object preservation. Strict parent admission is open. |
| E — signed CI observation | New `src/app/build/signed_build_ci_observation.spl` and focused specs | Bind independently observed exact candidate, protected policy/checker/submodule identities and current mandatory gates to the existing signed controller. Workflow wiring waits for its live file owner. |

The merge owner is the primary Codex agent. Astra reviews cross-lane
assumptions and the final architecture. The workflow/push scripts,
`target_executor.spl`, compiler, OCI provider, runtime and MCP configuration
are dirty under other live sessions; those owners retain their files. The
crash matrix, protected installation, base-owned submodule authority and
separate OS provider qualification remain acceptance gates.

The signed-hook lane now requires a sealed execution snapshot before any
receipt may shorten GitHub work: exact Git blob materialization, copied native
binary, enforced read-only sandbox, cleared ambient source/cache paths, and
receipt binding for the snapshot policy. Astra found that ordinary detached
worktrees and final rehashing do not satisfy this requirement; cold full-tree
materialization already exceeds the hook's default budget. The existing live
hook owner must integrate a measured signed operation separately from fast
unsigned checks. The staged-executable lane has a pure Docker attach frame
decoder as a fixture-specific transport prerequisite, while the general
worker still requires V4 descendant control and result-writer separation.

Lane E now has a pure-Simple current-observation precheck and focused source
spec. It returns ordinary-build fallback before signature or artifact access
on changed PR, merge tree, policy, checker, selected submodules, manifest or
gate digest. The base-owned event/Git observation collector and required-job
wiring remain with the workflow owner; source composition is not live CI
evidence. Its focused spec is unrun under this session's verification cap.

Lane A now has `scripts/check/check-dist-issued-native.shs` as a Linux-only
candidate builder. It requires adjacent verified Stage 4 provenance and a
clean checkout, archives the exact committed tree into a private source root,
copies the verified compiler, builds five restricted entrypoints (graph parent,
staged parent, build worker, fail-closed verifier parent and verifier worker), and
retains binary/log hashes. It clears ambient compiler/runtime overrides,
selects the C runtime bundle explicitly and records the selected host C
compiler and an installed linker hint. Actual linker/toolchain closure is
still unproven. Its receipt is explicitly unqualified; it does
not install into `bin/release` or provision a worker. The macOS host returned
`BLOCKED reason=linux-qualification-host-required`, and shell syntax passed.
The remaining lane A proof needs a prepared Linux host and a current admitted
Stage 4 compiler; do not use the current stale seed or retry bootstrap under
this session's verification cap.

Lane D now has a source-only Clang Ninja controller that holds the build lock
through native execution and captures exact output bytes. It pins the installed
Ninja digest and a restricted `build.ninja` plus `CMakeFiles/rules.ninja` graph.
Astra found that graph admission followed object invalidation; the barrier now
checks the approved graph under its lock before writing the stamp or removing
objects. Astra's follow-up caught a symlink fixture needing an approved graph;
that fixture was corrected. A host Ninja syntax probe executed the synthetic
three-step graph and produced `object-aobject-b`; this is fixture evidence,
not a Simple controller PASS. Focused rejection, no-op and synthetic Ninja
rebuild specs are authored but unrun under this
session's verify cap. The protected caller, complete compiler/header closure,
strict no-follow ancestor admission, successful real Ninja rebuild and
multi-output publication remain open; no production Clang admission is claimed.

The Clang barrier now preflights every mapped object, stamp and output path
under the owner lock before changing existing artifacts. It removes the prior
accepted output on a required rebuild, so future-dated output cannot suppress
Ninja work and a retained hardlink cannot become the next output. A restricted
graph validator now checks one CMake static-library edge's direct object inputs
against the complete protected map and requires one producer per mapped object.
Astra identified a false-coverage risk from Ninja continuation and variable
output syntax; the validator now rejects these forms before edge selection.
Focused omission, lexical-deception and redirected-path regressions are
authored but not Simple-runtime PASS evidence. Full command/header closure and
broader Ninja grammar remain open.

Lane C now has a source-level cold staged qualification driver and a dedicated
SPipe scenario/manual. Astra's review caught and prompted fixes for a partial
live fixture being counted as a successful test and a non-compile producer
being eligible for PASS. The driver requires two fresh nonce-bound OCI reports,
worker-matched compile/link profiles, resolved retained producer bytes,
durable accepted attempts and cleanup, protected executable export, a pinned
verifier receipt, and an attempt-free repeat. The verifier's actual isolation
is independently provisioned and still needs qualification. The live scenario
and docgen remain unrun under the current three-cycle runtime cap; no Linux
native candidate or provisioned two-worker fixture exists here.

A disjoint SimpleOS container provider adapter and focused kernel fixture spec
now exist. It launches through the managed scheduler and reports only
scheduler-observed exit, with logs and restart recovery explicitly unavailable.
This local SimpleOS seam does not advertise a distributed worker capability;
materialization, logs, recovery and live kernel evidence remain separate.

Lane C export follow-up now supports a conservative dynamic PIE profile in
pure Simple. Protected executable rows gained an explicit target field; the
qualifier compares it with the resolved link action's target before export.
Re-pin every executable policy file, then verify a real target-matching PIE
on Linux. The structural unit fixtures are authored but unrun. The execution
verifier remains a separate source gap: an exact native engine pin, a pinned
in-container Simple worker, complete V4 child-output capture into a private
mounted result, parent result validation and observed cleanup are required
before it can produce a trustworthy receipt. OCI engine logs are diagnostics.
See `doc/08_tracking/bug/dist_exec_verifier_byte_capture_2026-09-26.md`.

One external-format probe copied Debian bookworm arm64 `/bin/true` from the
local container image and inspected its ELF metadata without executing Simple:
ET_DYN, AArch64 machine 183, `/lib/ld-linux-aarch64.so.1`, one mapped
PT_DYNAMIC, `DF_1_PIE=0x08000000`, and non-overlapping PT_LOAD ranges all match
the admitted profile. This is compatibility evidence for the parser design,
not a Simple parser PASS or a live distributed link/export run. Astra's
independent static review found no P0/P1 and identified overlapping PT_LOAD
acceptance; the classifier now rejects those ranges and has a focused
regression fixture, still unrun under the verification cap.

Astra's fast-push review also identified a signed-receipt execution-input
race, and its workflow review found that Windows Stage 2 fallback plus skipped
Linux execution can leave a green job without the requested native evidence.
The owner must integrate an immutable hook-input snapshot and a protected
distribution acceptance checker before claiming fast signed reuse or a full
target-matrix PASS. The hook/workflow files are currently owned by external
sessions, so this plan records the gaps in the two dated tracking bugs without
folding their live edits into this lane.

Astra found that the operator two-node live qualifier previously assigned
producer and consumer roles from the order of issued worker configs, while
the graph runner admits those configs by worker ID. The qualifier now resolves
both roles by ID before querying capabilities or auditing owner state. This
allows an otherwise valid consumer-first config order without changing the
approved plan digest. Astra's read-only source review found no issue; the focused live qualifier
cannot be executed in this Mac session without the provisioned two-worker
fixture and a source-matched runtime.

The serial graph runner now invokes the existing startup-only missing-spool
reconciliation before taking its ledger snapshot. Before any revocation it
re-derives each graph action from its paired request and rejects duplicate or
mismatched action identities. It filters active attempts by the validated
action and worker, revokes only an attempt with a
matching durable intent and no request spool, and plans from the owner's
updated state. Spooled or otherwise unproven attempts remain active for
worker-status recovery. This closes the admission-to-spool replay loop in
source; a provisioned crash fixture and source-matched Simple run remain
required to qualify it, and orphaned private upload snapshots need a separate
durable cleanup mechanism.
The graph-runner focused spec now stages an intent and admitted attempt without
a request spool, restarts the serial runner with a clock that prevents remote
dispatch, and inspects the durable revoked attempt and advanced fence. It is
authored but unrun under this session's Simple verification cap. A second
scenario substitutes an unrelated request in the copied graph and requires
the original active attempt and fence to remain unchanged.
