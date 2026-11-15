# Installed Linux supervisor producer exclusion component

Status: AUTHORED_NOT_RUN; source component only. This does not open machine
genesis, replace the existing genesis refusal, adopt resources, or implement a
successor consumer. Existing Host, machine authority and storage code are not
changed by this component.

REQ-LINUX-SUPERVISOR-FENCE-001 binds exclusion to genuine installed root-owned
policy, the actual dedicated service account/process incarnation, and the
actual system manager. REQ-LINUX-SUPERVISOR-FENCE-002 requires whole installed
activation-closure inhibition, exact completed stop jobs, actual process/group
emptiness observations, and refusal of unknown service-UID processes.
REQ-LINUX-SUPERVISOR-FENCE-003 retains inhibition and cleanup ownership after
possible mutation, through the still-missing durable charge/successor handoff.

`linux_installed_supervisor_open_v1()` takes no roots, producer lists, PIDs,
expected hashes, completeness flags or caller bytes. Its private canonical
slot/generation owns an opaque profile reader, authenticated bus, generation
lock, exact native descriptors, prior unit states, actual mutation receipts
and actual stop-job observations. Diagnostic snapshots cannot construct it.

The four new IO files divide ABI declarations, protected profile provenance,
system-bus lifecycle and exclusion ownership. The profile capsule obtains its
reader from `linux_machine_policy_open_v1()` and consumes only the lazy fixed
`read_supervisor_profile_v1()` port added by the Linux storage lane. That port
retains the root-owned child descriptor, pins its bytes, and rechecks the
genuine process/namespace/machine-policy context. Closing or transferring that
reader invalidates later profile use.

The fixed profile `/etc/simple/container/supervisor-profile.sdn` has exactly:
`kind` (`linux-installed-supervisor`), `version` (1), `machinePolicyDigest`,
`serviceUid`, `supervisorUnit`, `providerUnit`, `activationUnits`,
`providerPolicy` (embedded installed provider-policy SDN), and
`closedActivationModel`
(`dedicated-uid-system-units-no-login-user-manager-cron-v1`), plus
`closedProviderModel` (`single-rootless-uid-all-stores-pinned-v1`). The service UID
must equal the actual unambiguous nonroot real/effective UID. Supervisor and
provider are distinct services; neither may appear in activation units. The
activation closure must explicitly include `user@<uid>.service`. Duplicate,
alias, malformed, unknown-state or self-stop routes refuse.

The closed model is an **external administrator installation obligation**.
Its enum names a supported installation contract; reading it is not an
observation of absence or a positive migration fence. The administrator must
install a dedicated account with no login, user-manager, cron, at, external
container clients or alternate activation paths, and ensure every cooperative
legacy creator runs under the enumerated system-manager routes. Root or
arbitrary same-UID host compromise is outside this model; guests must have no
host engine endpoint, delegated parent, policy, lock or state access. Machines
with arbitrary unowned legacy producers do not satisfy this supported model.
Absent policy, authorization or any required observation causes refusal.

The provider model is likewise an external closed-installation obligation,
not observed absence of alternate stores. Initial support is exactly one
rootless service UID/store. It binds the one canonical installed-v3 provider
policy's UID, graph root, run root, storage driver/options and service endpoint
to the same genuine machine-policy digest. The separate actual inventory owner
must decode the protected machine policy and require exactly one provider,
backend `linux-podman`, and byte-exact canonical CLI-policy agreement with the
installed-v3 policy. Additional providers/backends/stores must refuse as
unsupported/incomplete; a profile model token cannot silently exclude them.

The fixed `/run/dbus/system_bus_socket` is reached through root-owned,
non-writable, nofollow ancestry. The socket's root owner, native type and
device/inode/mount identity are checked before connection and during manager
authentication. The implementation creates its own bus with `sd_bus_new`,
fixed `sd_bus_set_address`, explicit client mode, disabled interactive
authorization and bounded method timeout. It never calls environment-sensitive
default/open-system helpers. The actual broker must supply root credentials;
the actual manager unique name must supply EUID 0 and PID 1. All manager
operations target that exact unique name and refuse replacement.

The supervisor profile is additionally bound through `GetUnitByPID`, the exact
unit `Id`, and `Service.MainPID` to the genuine current process context. The
live provider unit/main process is pinned independently. A producer alias
resolving to either of these units refuses. The bus support factory itself
requires the opaque installed profile; its mask/stop/reference methods reject
units outside the installed closure.

The provider's native proc directory identity and start-time ticks are pinned
and rechecked as well as its PID/unit; PID reuse cannot satisfy incarnation.
All four provider UID values must equal the installed dedicated UID. The
retained exclusion diagnostic exposes provider PID/incarnation, canonical
owner generation and current process identity for actual-peer correlation.
`installed_snapshot_v1()` first revalidates the actual supervisor and then
reads its retained installed profile; neither diagnostic can mint authority.

Before mutations, the owner acquires the fixed generation lock under
`/var/lib/simple/container/supervisor.fence.lock`; its ancestors through
`/var/lib/simple` are root-protected. The predelegated fixed `container`
directory itself must be service-UID-owned 0700, matching the actual machine
storage installation. There is no per-UID alternate state root. The final
directory and fixed lock file are retained; revalidation reopens their actual
fixed names beneath root-protected ancestry and compares exact native identity
and service ownership, as well as the live canonical lock generation.
This lock serializes cooperating new owners. It cannot exclude old writers by
itself. Actual masks and stops provide the legacy-route exclusion component.
No second journal is added.

Every installed unit must already be known to the manager. `RefUnit` ties its
continued visibility to the retained bus connection. Initial exact file states
are recorded. Service producers must use `KillMode=control-group`; their actual
manager-reported prior cgroups and event files are pinned on genuine cgroup v2
through nofollow descriptors before stopping. Runtime masks use `force=false`;
each new mask must return exactly the expected `/run/systemd/system/<unit>`
symlink to `/dev/null`. All routes are masked before any stop, followed by
actual manager `Reload`. Units installed in higher-priority local locations
that prevent an effective runtime mask refuse; installation must choose a
supported vendor-unit layout. The administrator must grant actual
noninteractive manage-unit-files, manage-units and reload-daemon authority.

The broker receives `AddMatch` and the manager receives `Subscribe` before
stopping. `StopUnit` uses `sd_bus_send` with an actual cookie and a bounded
`sd_bus_process` pump, not synchronous call dispatch. The pump retains
authenticated `JobRemoved` tuples even when completion precedes the exact
cookie-matched method reply. Success requires the returned job object, exact
unit, `done` result and unchanged manager. Inactive state alone never
manufactures completion.

Afterward every unit must remain masked, inactive, jobless, and bound to the
same manager unit object. Services require zero `MainPID` and `ControlPID`,
plus actual `populated 0` from the pinned cgroup event file or kernel removal
of the exact pinned cgroup directory. A missing old pathname is never treated
as removal proof. A complete genuine-procfs scan rejects any process retaining
the dedicated real/effective/saved/filesystem UID except the actual supervisor
and pinned provider main process, each re-correlated through the manager.
Races, inaccessible entries, malformed status, mount changes and incomplete
enumerations refuse. No PID/name-based killing or label-based adoption occurs.

All native outputs enter canonical cleanup ownership before subsequent
validation. Descriptor close consumes the slot first; uncertain close cannot
retry an integer that might have been reused. Transient proc descriptors are
closed per process and bounded slots are reused. Failed revalidation quarantines
the capsule instead of allowing repeated growing scans. Native owner state is
main-thread/process-bound. The startup acceptance budget is 30 seconds, each
method call is bounded to one second, each stop reply/completion pump to five
seconds/8192 turns, completion storage to 256 records, proc enumeration to
65536 entries, native descriptors to 4096, cgroup depth to 32 and profile
activation closure to 128. These are source bounds, not measured targets or
hard kernel-preemptive deadlines.

Every profile, bus and supervisor registry entry, including cleanup and
reopening after previous owners close, first invokes the shared permanent
`linux_machine_process_origin_check_v1()` guard. Numeric PID/TID equality
alone is insufficient across fork or PID-namespace collisions. The accepted
guard retains genuine procfs lifetime provenance even after capsules close.

Full scans occur only at initial exclusion or explicit retained-component
revalidation. They must not be placed in hot request handlers. No latency/RSS
measurements are available; target qualification must measure realistic setup
and revalidation fixtures before integration into admission.

After any possible mask or stop, `close_v1()` returns retained inhibition; it
does not unmask, restore prior state, restart units, drop the lock or silently
claim handoff. Actual change receipts remain available in the private owner
state. There is no automatic rollback API because partial or unknown prior
state cannot safely justify restoration. Before mutation, cleanup may release
only its actual descriptors, bus, lock and reader. Every component records
positive consumption separately from its first close diagnostic. `released`
and `consumed-error` retire the exact partner once; `retained` keeps a live
retryable owner, while unknown/stale outcomes preserve the exact owner in
quarantine without retrying a native descriptor. Already-consumed profile/bus
capsules return their own recorded result idempotently. The supervisor persists
each partner's progress and first diagnostic before another partner can retain
cleanup; a later retry cannot clear that diagnostic or reclose a consumed
partner. There is no early return that forgets an already-consumed close error.
The read-only `close_diagnostic_v1()` accessors retain the first diagnostic even
after consumption. Native fault injection and retained-partner/error sequences
remain NOT_COVERED until an actual qualified fixture runs. A future successor must
join this exact exclusion ownership and same machine writer before any
ownership transfer; a data snapshot or a closed bus is not that handoff.

`Ready` means only this exclusion component. It exposes no machine-genesis
flag or admission capability. Before a first grant, the actual inventory owner
must query **all** native resource IDs in **every** delegated endpoint/store,
without provider/service labels. Unknown resources must quarantine or retain
their actual capacity charges. Initial support may refuse every nonempty
inventory; adoption requires actual owner-validated retained requests and exact
charges. A same-machine-WAL consumer must retain the supervisor through the
durable charge and actual successor exclusion handoff. Neither source seam is
implemented by these four files; no positive inventory result is exposed.

The unique actual-fixture spec/manual is authored but not run. Source review
cannot qualify bus linking, callback-free message ordering, manager behavior,
OS layouts, teardown, process enumeration or native resource cleanup. Linking
requires the actual platform libsystemd ABI; no new runtime export/allowlist or
C shim is introduced. Native campaigns remain exhausted in this session.

Primary references: [fixed versus environment-selected bus opening](https://freedesktop.org/software/systemd/man/latest/sd_bus_open.html),
[manager unit files, jobs and subscription](https://freedesktop.org/software/systemd/man/latest/org.freedesktop.systemd1.html),
[nonvariadic append](https://www.freedesktop.org/software/systemd/man/latest/sd_bus_message_append_basic.html),
[actual peer credentials](https://www.freedesktop.org/software/systemd/man/261/sd_bus_get_owner_creds.html),
[send cookies](https://www.freedesktop.org/software/systemd/man/250/sd_bus_send.html),
and [unhandled message ownership](https://www.freedesktop.org/software/systemd/man/261/sd_bus_process.html).
