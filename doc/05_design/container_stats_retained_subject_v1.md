# Typed stats from the retained original container subject

Status: source-authored, **NOT_RUN**, awaiting scoped review and final workspace
dependency refresh. This implements the retained-FD boundary accepted in
`/tmp/container-stats-retained-subject-proposal-20261115-r1`, manifest
`158ec98e86a891599206acd3db3517403d776f268e0b2e5663ac24fd1fa5b352`.

`simple_container_stats_observe_v1` is exported through the existing Container
facade. It returns `ContainerExecutionStatsTurnV1` with the retained owner, an
optional typed observation, and an error. Windows Docker returns explicit
`optional-capability-unavailable:stats:windows-docker`. A legacy Linux owner
without the genuine fresh subject refuses rather than executing host commands.
The existing textual read/apply action whitelists and lifecycle wire remain
unchanged.

The Linux path is API → adapter → fresh workload owner → sealed transfer's
original record/containment → same successor custody → existing native subject.
CPU and workspace records take distinct typed branches. Workspace dispatch uses
the retained genuine native binding and `LinuxFreshWorkspaceCommandV3`; it never
strips workspace identity into the CPU subject path. Statistics do not invoke
association, the Running latch, a Stats action, a helper, a new writer, a journal
commit or an admission/release transition.

The subject must already be confirmed and ready. Its private fixed-child reader
uses the exact retained original container-root FD and only `cpu.stat`,
`memory.current`, `pids.current`, `io.stat`. New FDs enter the existing canonical
subject handle table before fallible metadata checks, and existing children are
reused. Immediate native ENOENT alone supplies optional file absence. Permission,
metadata, filesystem, parse, clock and other errors produce no snapshot. All
partial handles remain reachable through the existing owner's close path. No raw
FD, path capability, caller PID or second registry is exposed.

Before and after the read, the CPU branch invokes the actual readonly subject
observation with the exact CPU request key; workspace invokes the active typed
workspace key/binding bracket. Both require prior confirmation without creating
it. The native/custody layers recheck installed epoch/provider context; the sealed
transfer rechecks original admitted record/native ID; the fresh owner rechecks
its borrowed actual principal. Changed, closing or removed subjects refuse.

The snapshot includes full scope/runtime/request attribution, a digest of the
original subject identity, and a positive actual monotonic start/finish bracket.
The API extends the nested native bracket around its complete validation call.
Several kernel files are read sequentially: this is an observation interval,
never a simultaneous atomic snapshot. CPU usage is cumulative microseconds;
memory is kernel `memory.current`, PID count is `pids.current`. Scope is the
original container root and descendants, not a Podman CLI working-set or CPU
percentage display. The values confer no admission, resource-limit enforcement,
workload readiness or accounting-release authority.

The pure parser bounds CPU input to 8,192 bytes/64 fields, scalar files to 64
bytes, I/O input to 32,768 bytes/128 devices. Unsigned decimal accumulation and
all aggregate sums are checked against signed i64 storage. Duplicate, malformed,
negative, noncanonical, truncated and overflow records fail. Unknown bounded
numeric fields do not become supported metrics. Genuine numeric zero and an
actual empty I/O device collection remain observed data; missing metrics are
explicit Unsupported states, never zeros or swallowed permission errors.

Each sample performs fixed bounded reads plus the existing current-owner identity
checks; no autonomous background polling is introduced. Canonical counter FD
count stays at four per subject. Runtime cost/latency/RSS are unmeasured; no
performance claim is made from source inspection.

Coverage consists of 20 actual production-parser/shape cases and a genuine
CPU-only public-API fixture with normal admission/create/start, 13 repeated
observations, changed-request refusal, destroy/settlement and closed-alias
refusal. All are authored NOT_RUN. Native permission/substitution/cleanup-error
procedures remain unexecuted. The workspace public factory/session producer is
an explicit unfinished dependency of the unreviewed producer checkpoint; this
slice does not invent it or claim a genuine workspace fixture has run.

The exact checkpoint dependencies are recorded in the handoff manifest. Lower
workspace code still owns the evolving native/subject/custody files and upper
workspace code owns the record/factory wiring. This isolated stats delta must be
three-way refreshed over their final producer freezes and reviewed independently
before landing. The upper checkpoint already exceeded the 800-line authority-file
limit before this minimal same-owner stats addition; its planned mechanical split
must preserve the stats method and private binding semantics. No old snapshot
overlay is an acceptable integration method.
