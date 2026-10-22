# Distributed build controller (V1–V4 source)

`simple dist-build --config /absolute/path/parent.conf` is the source-level
entrypoint for one authenticated Linux OCI worker attempt. Install a compiled
self-hosted `simple` containing this command before using it. The current
diagnostic seed cannot execute the positive file-read path.

After an uncertain attempt, use
`simple dist-build --config /absolute/path/parent.conf --status <attempt-id>`
to read a completed result without relaunching the worker. A result already
committed to the parent ledger is returned locally. Use
`simple dist-build --config /absolute/path/parent.conf --cancel <attempt-id>`
only when the worker has not started; capacity is released after its durable
request-bound cancellation acknowledgement. An active or uncertain worker
continues to reserve its fence. Both commands use the same protected config.

The administrator owns `parent.conf`, its parent directory, the SSH identity,
known-hosts file and worker policy. The config uses exactly these rows in this
order, ends with one newline, and has no comments or extra rows:

```text
simple-dist-build-parent-v1
request=/absolute/path/request.wire
owner=/absolute/path/owner
source=/absolute/path/source
state=/absolute/path/state
cas=/absolute/path/cas
ssh-executable=/usr/bin/ssh
ssh-digest=<lowercase SHA-256>
sftp-executable=/usr/bin/sftp
sftp-digest=<lowercase SHA-256>
known-hosts=/absolute/path/known_hosts
known-hosts-digest=<lowercase SHA-256>
identity=/absolute/path/identity
identity-digest=<lowercase SHA-256>
worker-id=worker-1
host=build.example
user=builder
port=22
remote-executable=/usr/local/bin/simple-build-worker
inbox=/srv/simple-build-inbox
trust-domain=trusted-build
target-triple=x86_64-unknown-linux-gnu
provider-abi=<lowercase SHA-256>
worker-memory=8589934592
scheduler-cpu=4
scheduler-memory=8589934592
scheduler-memory-reserve=0
scheduler-fd=128
timeout-ms=30000
```

The request file must be a canonical `simple-build-worker-request-v1` wire.
Its worker ID must match the protected worker. Its fence field is a required
canonical placeholder for this CLI; the controller allocates the actual fence
under the exclusive owner lock and creates a fresh worker request. The
controller checks action identity and resource values,
queries the worker with a fresh nonce over pinned SSH, and requires an exact
fenced Simple Orchestrator Job plan before journal admission. The controller
admits Linux, macOS, Windows, FreeBSD, OpenBSD, NetBSD or SimpleOS controller
identities with a qualified Linux worker; that list does not establish a live
controller on every host. The plan is admission metadata; the
current worker route still launches its pinned OCI container directly.
The controller snapshots and verifies
input bytes, journals admission, transfers through pinned SFTP, then accepts
only independently verified output bytes. A known nonzero container exit
publishes bounded diagnostics, an empty output manifest and a versioned
failure proof bound to its request, permanent launch binding, fence, known
exit and exact result wire after the worker persists its terminal observation.
The parent requires that proof and confirms the failed wire through the
worker's status path, retains the exact diagnostics, and journals
`action-failure-unclassified`. It frees scheduler capacity for a bounded retry,
without claiming that the source code caused the failure. A versioned
diagnostic evidence contract is needed before a remote failure may be labeled
deterministic `compiler-failure`. An uncertain transport or provider result
keeps its fence reserved for reconciliation.

The graph-action CLI source releases the journal owner after the complete
request spool is durable, so a second worker may be admitted while the first
transfers and executes. It reopens and revalidates the active request before
retaining or publishing a result. This overlap still needs a live two-worker
qualification on a current self-hosted runtime.

The status and cancellation source routes release the owner before contacting
the worker, then reopen and revalidate the exact active request before
publication or revocation. A completed status also retries cleanup when its
exact committed result has a pending worker acknowledgement. The parent
releases its owner lock across SSH, accepts only the pinned worker's exact
request/fence/result-digest ACK, then records the acknowledgement durably.
Cleanup failure keeps the committed build outcome and prints
`cleanup=pending` on a successful build; repeat `--status` to retry it. The
worker accepts an ACK only for its durable result and retained
container binding, confirms a stopped or exited native OCI identity, and
records terminal, absent and cleaned states before deleting staged and inbox
bytes. An identical completed ACK can be replayed after reboot. These paths
have source and review evidence only; their live crash and race behavior is
unqualified on the current runtime.

If a worker stops after OCI `wait` but before writing `result.wire`, it now
persists the exact exit code and full launch-binding digest first. A later
`--status` verifies that observation, recovers the same terminal native
container, rebuilds any partial result directory, and publishes the canonical
result last. A complete existing `result.wire` can be replayed read-only after
worker reboot or an image/provider-generation change under the same worker and
state root; current provider identity is required
only when publication remains incomplete. Recovery never launches the
container again. If a crash occurred before the exit observation, the
provider requests the exit code and identity in one native inspect response.
Only an exact `exited` container with a canonical exit code can create the
missing durable observation; `running`, `created`, `dead`, unknown codes and
conflicting observations leave the attempt active. This restart path is
source-level only until a qualified Linux worker exercises the crash points.

For a protected multi-action graph, use a V2 config with the same rows as V1
but replace the header with `simple-dist-build-parent-v2` and the first row
with `graph=/absolute/path/graph.manifest`. Select one action at a time:

```text
simple dist-build --config /absolute/path/parent-v2.conf --action <action-SHA-256>
```

The graph manifest ends with a newline and contains one to 256 exact request
file references. Each digest pins the bytes read from its path:

```text
simple-dist-build-graph-v1
request=<request-file-SHA-256>|/absolute/path/producer.request
request=<request-file-SHA-256>|/absolute/path/consumer.request
```

Use `--next` with a V2 config to select the highest-priority ready action
assigned to that worker that matches its protected target/provider policy and
fits the current **global** scheduler capacity. The current Linux worker holds
one `worker.lock` during execution, so selection refuses another attempt for
that worker while any of its attempts remains active. Final admission repeats
this check under the parent owner lock before request staging or journaling.
It reads a locked ledger snapshot, then the final owner rechecks readiness,
capacity and retry number under its lock before dispatch. Run two worker
configs concurrently to permit distinct ready actions to overlap; a lost
selection race reports incomplete and can be retried from a fresh snapshot.
The CLI prints a proposed random attempt ID before remote contact so status
and cancellation can recover an uncertain admission. `--next` allows at most
three admitted attempts per action, counting revocations, and skips actions
with deterministic compiler diagnostics. Further retries require explicit
`--action` with a new request template and the current retry number.

Use the same complete graph, scheduler capacity and dedicated owner root for
producer and consumer invocations; each selected request must name the worker
in that invocation's protected config. The durable ledger may retain accepted
actions from earlier graphs; readiness planning filters that history to the
current graph, while all active attempts continue to consume global capacity.

Keep every dependency action needed by a current consumer in its graph. A changed target name or
action digest needs an explicit owner/graph lifecycle decision; never delete
an owner with active attempts to make a changed graph fit. The CLI reads the
manifest once, checks each file digest, validates the complete acyclic graph
and then lets the owner
recheck dependency publication and allocate the current fence. A consumer
cannot dispatch until its producer's accepted output is retained. The
administrator must protect all parent directories from replacement; the
no-follow reads protect only final file components. This source route has
not passed self-hosted file I/O or a two-node run.

The source-level whole-graph runner in
`src/app/build/scheduler/parent_graph_runner_main.spl` accepts one to 16
protected worker configs and drives the graph until all actions have durable
accepted results. It resumes an active attempt before dispatching new work,
selects ready actions by global priority, and requires the configs to share
one owner, capacity, trust domain and retained CAS root. An uncertain remote
result reports incomplete and retains its active fence. Its diagnostic source
entrypoint accepts `--graph-digest <64-lowercase-hex-SHA-256>` followed by one
to 16 `--config /absolute/path/worker.conf` pairs. The digest must come from
the protected administrator policy, independently of the graph manifest and
its request files. The entrypoint checks the exact manifest bytes against it
before parsing the graph or dispatching any action; each manifest row then
pins its request bytes. Supplying a digest computed from an untrusted graph
at launch does not establish that protection. This entrypoint has
no qualified cached production binary yet; its planner spec and real two-node
compile/link scenario remain unrun under the current runtime blocker. Its
administrator config and graph path grammar currently admit POSIX absolute
paths only; Windows parent-controller support needs a separately qualified
path policy and native entrypoint.

For a cold compile-to-link build, a protected link template can name ordered
producer action/output pairs without claiming output digests that do not yet
exist. `parent_link_template.spl` validates the operand positions and rejects
ambiguous output names. After producer publication,
`parent_link_resolution.spl` reads the accepted ledger, exact retained output
manifests and CAS bytes, then constructs a complete link action and canonical
worker request. It replaces only the bound link operands with their
`/simple-build/inputs/<name>` paths, preserving linker order. Repeated
resolution of unchanged accepted bytes has the same
action identity; changed output bytes change it. The owner-backed entrypoint
replays and closes the durable parent journal before resolving retained bytes.
`parent_staged_link.spl` now binds the producer manifest, ordered template,
link intent and exact worker config bytes into one expected staged-plan digest.
It checks the producer request bytes, template closure and declared producer
outputs before dispatch,
runs the producer graph, then derives and runs a second graph containing the
original producer requests and resolved link request. Restart replays accepted
producers and can resume the link fence. The staged CLI source now loads a
bounded, no-follow template file and its
digest-pinned canonical base request. The template's version 1 wire is:

```text
simple-parent-link-template-v1
base-request=<base-request-SHA-256>|/absolute/path/base.request
input=<producer-action-SHA-256>|liba.o|1
```

The base request is a canonical link intent with no dependency outputs and a
placeholder fence of `1`; the staged controller never dispatches it. Each
`input` row gives an ordered linker argument index. The raw source CLI grammar is:

```text
--staged-plan-digest <protected-plan-SHA-256> --template /absolute/path/link.template --template-digest <protected-template-SHA-256> --config /absolute/path/worker.conf
```

The expected plan digest must be established independently by administrator
policy. The CLI calculates the candidate plan identity from exact producer
manifest, template and worker-config bytes and refuses a mismatch before
producer dispatch; calculating and trusting that expected value from the same
mutable candidate files at launch gives no authorization. The staged CLI is
source-only until its native controller passes the self-hosted build and
system tests. `parent_issued_plan_issuer.spl` checks an independently approved
digest before publishing a content-addressed record in an administrator-owned
store. It does not authenticate that approval or install the store. The
restricted source entrypoint accepts only `--issued-plan <record-SHA-256>`,
loads the exact record under compiled `/etc/simple/dist-build/staged-plans`,
then repeats staged preflight before execution. It admits Linux and macOS
controllers only. Current-runtime tests and real producer/link execution
remain required.

`bin/simple_dist_build_parent` is the production launch boundary for this
controller. It accepts only a host-compatible native executable under
`bin/release/<triple>/simple_dist_build_issued_parent` with an exact SHA-256
sidecar; the raw graph entrypoint is outside this wrapper's allowlist. The
installed controller and root must be administrator-owned; callers authorized
to select an issued record can rerun it while it remains present.

For a complete graph with no staged link, `parent_graph_plan.spl` defines a
separate execution identity over the exact graph-manifest digest and ordered
worker-config wire digests. The manifest itself pins every request wire. The
administrator-side `issue_approved_parent_graph_v1` requires an independently
approved execution-plan digest, rereads the bounded protected inputs, admits
the graph and shared worker policy, and writes a canonical record under
`/etc/simple/dist-build/graph-plans`. The record has a distinct header and
namespace from staged plans. The installed graph entrypoint accepts only
`--issued-plan <record-SHA-256>`; it rereads and rechecks the pinned inputs
before opening the parent owner. `bin/simple_dist_build_graph_parent` admits
only a matching native `simple_dist_build_issued_graph_parent` and SHA-256
sidecar. The raw graph source entrypoint remains diagnostic and must not be
installed with privileged credentials. Graph preflight does not prove that
each action can run on its assigned worker; the scheduler checks static
capability and resource eligibility during dispatch and fails closed.

The issuer caller must authenticate approval independently, protect the
installed root and every referenced file ancestor, and isolate SSH credentials
from raw diagnostic binaries. The graph source and its new specs have no
self-hosted runtime PASS or installed native candidate yet.

Missing, changed or wrong-format artifacts fail closed. No native candidate
has passed the required self-hosted build and whole-graph tests yet, so the
wrappers currently report that no admitted controller is available. On
OpenBSD, NetBSD, DragonFly and SimpleOS the wrapper requires an explicit
`SIMPLE_PLATFORM_TRIPLE` because the shared host resolver has no reliable
default release directory; the issued entrypoint rejects those hosts in V1.

On a Linux qualification host, `sh scripts/check/check-dist-issued-native.shs
<Stage-4-binary> <adjacent-Stage-4-provenance>` prepares three isolated
candidate binaries: issued graph parent, issued staged parent and worker. The
checker verifies Stage 4 provenance and a clean source checkout, compiles a
private committed-source archive with a copied compiler, and retains hashes,
build logs and an explicit `CANDIDATE_BUILT_UNQUALIFIED` receipt under
`build/dist-issued-native.*`. It does not install binaries or grant worker
credentials. The candidate build clears ambient environment overrides, pins
the C runtime bundle to `core-c-bootstrap`, and records the selected host C
compiler plus an installed linker hint. The actual linker and host headers,
libraries and compiler support files still need qualified observation; this
does not establish an independently approved host toolchain
image. A live two-node run, cold link, fault suite and protected
installation must still qualify those candidates before publication.

To export one accepted object, use a V3 administrator config. Keep the V2
graph header and rows, change the header to
`simple-dist-build-parent-v3`, and append
`export-root=/absolute/protected/build/objects` after `timeout-ms`. The
administrator creates and owns this directory. Then run:

```text
simple dist-build --config /absolute/path/parent-v3.conf --export <action-SHA-256> <declared-object.o> <destination-object.o>
```

The command replays the owner ledger, requires that action and exact object
row to be accepted, reads the retained manifest and binary CAS, verifies the
bytes including non-text bytes, stages a private object in `export-root`,
and replaces the destination by rename. It reports `EXPORTED` only after the
destination directory is synced and the export lock is released. A stage
cleanup warning preserves success and prints `cleanup=pending`. A failure after rename is reported as
`INCOMPLETE` with `published=true durable=false`; inspect/retry that exact
export. A lock-release failure also reports `INCOMPLETE`, even if the object is
already durable. This path accepts only `.o` or `.obj` leaves. V1/V2 configs have
no export root and refuse `--export`. The source and focused fixture have no
current self-hosted runtime PASS, so this is not yet a qualified deployment
command.

V4 adds a protected, digest-pinned export policy. Change the V3 header to
`simple-dist-build-parent-v4`, then append these rows after `export-root`:

```text
export-policy=/absolute/protected/export-policy.wire
export-policy-digest=<SHA-256 of exact policy bytes>
```

The policy is canonical UTF-8 text ending in a newline. Rows are sorted by
unique ID and name one accepted action, its declared output, a kind, a local
destination leaf and a fixed installation mode:

```text
simple-build-export-policy-v1
count=1
row=program|<action-SHA-256>|simple|executable|simple|0755|x86_64-unknown-linux-gnu
```

Run `simple dist-build --config /absolute/path/parent-v4.conf --export-policy
program`. The CLI accepts only the policy ID. The policy may describe `object`
(`.o`/`.obj`, `0644`), `archive` (`.a`/`.lib`, `0644`), or `executable`
(`0755`, with a required target triple). The source exporter handles objects,
a bounded ELF `ET_EXEC`/dynamic-PIE profile, and
Mach-O `MH_EXECUTE` images on Unix hosts. It checks bounded load headers,
then applies and verifies the trusted mode on a private
staged file before sync and rename. Regular `.a`/`.lib` archives use a
Simple-side bounded archive CAS adapter; thin archives and malformed member
lengths fail closed. Windows executable mode is unsupported because
its current chmod provider is a no-op. Static PIE is unsupported.
V4 disables the legacy
`--export` route so callers cannot bypass the pinned policy. The source has
no current pure-Simple runtime PASS, and the target executor does not consume
the exported file yet.

The V1 request-wire command still admits one dependency-free action.
Remote ActionSpecs require an authoritative complete compiler closure or a
complete immutable source namespace; a handwritten source list is insufficient.
The only hosted worker provider currently implemented is Linux OCI. A macOS
controller may use a remote Linux worker, subject to live qualification.

## CMake/Ninja policy dependency

For a C-family CMake target whose sources are fully declared, include
`cmake/SimpleClangPolicy.cmake` and call
`simple_clang_policy_attach(target "/absolute/path/policy.stamp")` after its
last `target_sources` call. The Simple policy gate must evaluate the current
request and atomically replace that stamp with its required dependency digest
before every `cmake --build`. The stamp is a native dependency, but a changed
timestamp alone does not prove Ninja rebuilt an object: an existing object can
have a future or equal timestamp. The current
module requires Ninja and refuses missing stamps, generator-expression
sources, unknown source languages and targets with no C-family object. The
Simple `native_rebuild_barrier.spl` accepts a digest-pinned, sorted mapping of
one target's complete object outputs, policy stamp and approved two-file Ninja
graph under a protected build root. It checks the graph and preflights every
stamp, output and mapped-object path under the owner lock before changing
existing artifacts. `REBUILD_REQUIRED` writes the stamp, removes the prior
accepted output and only mapped regular objects, and verifies their absence
before Ninja runs; `ADMIT_NOOP` verifies the stamp and every mapped object
without changing them. Policy, graph and path rejection preserves existing
artifacts; a later filesystem failure can leave invalidated paths and must
fail the build. Its returned owner lease must remain held through Ninja
execution and result acceptance, and every permitted builder must honor that
lock. The map wire is canonical and SHA-256 pinned by administrator policy:

```text
simple-clang-native-object-map-v1
target=libcore
stamp=policy.stamp
accepted-output=libcore.a
object-count=2
object=CMakeFiles/libcore.dir/a.c.o
object=CMakeFiles/libcore.dir/b.c.o
```

The build root and every path ancestor must be trusted and isolated from
unlocked writers. The barrier detects ordinary POSIX ancestor symlinks, but
the current `path_absolute` ABI can return its input when `realpath` fails;
this check is not a hostile-filesystem proof. A strict no-follow directory
admission primitive is required before this barrier can protect a build tree
that untrusted writers can mutate. Under the lease, no-op admission rehashes the
accepted output against the independently protected prior digest. The caller
must separately prove required compiler actions ran and that
rebuilt outputs are current before publication. The
native no-op decision also requires a current observed output digest equal to
the prior accepted output digest; an absent or changed output requires native
work. `observe_and_decide_clang_native_noop_v1` can capture one binary output
up to 128 MiB with a no-follow read and returns those same bytes only on no-op
admission. The trusted controller must bind the output path and prior digest to
the accepted action, then publish the returned bytes without reopening the
original file. Multi-output and larger native artifacts need a manifest and
streaming snapshot path. The revised CMake/Ninja fixture passed for C and
explicitly tagged C++ objects;
the Simple writer and barrier specs and full gate-to-launcher flow remain
unqualified. `native_ninja_controller.spl` now composes the lease, native
invocation, mapped-object reappearance and locked byte snapshot. It requires
an independently approved digest of the exact `build.ninja` and
`CMakeFiles/rules.ninja` bytes, checked before barrier mutation and rechecked
under the lease after the run;
additional `include`, `subninja` and `dyndep` graph forms fail closed in this
first adapter. The preflight also checks that the unique static-library edge
consumes exactly the protected map's direct objects, in their original archive
order, and that every mapped object has one producer edge. Variable-derived,
continued, implicit or multiple-output forms block this V1 route. This check
does not authenticate the compiler and archiver commands or complete header
closure. The Ninja executable must be installed under immutable trusted
ancestors. This source route neither authenticates the policy/map approval nor
proves full compiler/header/side-output capture. No production launcher yet
supplies the protected map and graph pins or publishes its returned bytes.

## Signed local-build reuse in GitHub

`app.build.signed_build_controller.verify_protected_signed_build_candidate_v2`
is a Simple source entrypoint for a future base-owned required build job. It
checks a gate receipt against independently pinned bootstrap-policy bytes and
the exact candidate, then verifies the V2 receipt through a pinned OpenSSH
signer policy, copies the downloaded artifact into a private directory, and
checks those copied bytes before returning a consumer path. Any failed step
returns `FULL_BUILD` with no artifact path. The caller must run the ordinary
build on that result and report the required GitHub context either way.

`app.build.signed_build_ci_observation.verify_observed_signed_build_ci_candidate_v1`
adds a current-candidate precheck. It requires the GitHub-observed merge tree,
the tree of the locally pinned integration candidate, the protected policy,
checker, selected submodules, manifest and current gate receipt to match the
expected build identity before signed verification. The pure check cannot
authenticate its caller's observations; the base-owned workflow must collect
them independently and preserve that provenance.

No current GitHub build workflow invokes this source entrypoint, and it has no
production self-hosted runtime PASS. Existing local CI receipts target the
separate extended code-idiom workflow; they do not admit a GitHub build job.

## Staged two-worker qualification

`app.build.scheduler.two_node_staged_qualification` is an operator-only source
driver for a cold issued compile/link plan. The matching SPipe scenario and
operator manual are `dist_build_staged_two_node_spec`. It requires a fresh
dedicated owner, distinct nonce-bound Linux OCI workers, compile and link
profiles matching those workers, exact proposed and accepted attempts,
retained dependency bytes, cleanup acknowledgements, protected executable
export, a pinned verifier receipt, and an attempt-free repeat. A partially
configured live fixture fails the live scenario. A missing complete fixture
may skip that scenario but does not count as live evidence.

The controller pins verifier bytes and checks its reported executable digest,
exit code, stdout digest and isolation field. Its receipt does not by itself
establish that the verifier actually enforced Linux OCI isolation; qualify and
install that verifier independently. No live two-worker run, current
pure-Simple PASS, or generated SPipe manual exists yet.

The SimpleOS managed container provider adapter in
`os.services.container.runtime_provider_v1` uses the kernel scheduler's real
task binding and exit reconciliation. It explicitly reports logs and restart
recovery unavailable. It is not admitted as a distributed build worker;
macOS, Windows and FreeBSD may coordinate authenticated Linux workers while
native isolation providers are qualified per operating system.

On a macOS host, run `sh scripts/check/check-macos-simpleos-container-host.shs
--sdn` to record the host, QEMU binary digest and HVF availability. Supply
`--image /absolute/path/to/simpleos.img --image-sha256 <lowercase-sha256>`
when an admitted SimpleOS guest image is available. The receipt's
`PREFLIGHT_ONLY` status covers host and image prerequisites only; it is not a
guest boot or container task-exit result. `BLOCKED` identifies missing
prerequisites. A real guest task-exit check and the Linux two-worker parallel
wave remain tracked in
`doc/08_tracking/todo/macos_simpleos_guest_container_live_route_2026-09-26.md`
and `doc/08_tracking/todo/dist_build_linux_parallel_wave_qualification_2026-09-27.md`.

### Executable export target admission

Executable policy rows require a seventh field containing an administrator-pinned
target: `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
`x86_64-apple-darwin`, or `aarch64-apple-darwin`. Object/archive rows retain six
fields. Missing or unknown executable targets fail closed; re-pin the policy
file digest after changing a row.

Linux admission supports a bounded ELF64 little-endian ET_EXEC/dynamic-PIE
profile. PIE requires an executable file-backed entry, one mapped PT_DYNAMIC,
terminated dynamic entries with DF_1_PIE, and the exact GNU interpreter for the
selected architecture. Static PIE and musl targets are unsupported. Addresses
and file offsets must fit 32 bits; dynamic tables are limited to 64 KiB, and
overlapping PT_LOAD virtual ranges are rejected.
Mach-O retains its existing segment validation with explicit CPU/target binding.
Format admission is not a complete ELF loader or code-safety proof: dynamic
relocations, dependencies, and instructions still require isolated verification.
The segment checks follow the [ELF program-header rules](https://refspecs.linuxfoundation.org/elf/gabi4%2B/ch5.pheader.html);
the GNU `DF_1_PIE` bit is [defined by glibc/binutils](https://sourceware.org/pipermail/libc-alpha/2018-January/090567.html).
