# Experimental Darwin launch and peer observation transport

`runtime_sosix_darwin_broker_transport_private.h` supplies bound launch attempts
and current kernel peer observations. It grants **no original-job admission or
owned-coalition authority** and is not wired into BuildRunner V4 capability.

GetJob omits EnvironmentVariables and SpawnConstraint. A same-UID actor can
remove/recreate the label before the first peer observation with identical code
and arguments but different launch configuration. The native test demonstrates
this actual takeover: the helper receives injected environment, GetJob hides it,
and code/PID observation succeeds. Consequently no admission-authorized state
or API is exposed. A future trusted broker needs an independent original-job
bootstrap channel before it can authorize workloads or own the coalition.

The controller owns zero-initialized `SosixDarwinBrokerTransport` state, a caller-
trusted CDHash, and the executable image lifetime. Submit constructs the job in
memory, generates a random label, and requests RunAtLoad, LaunchOnlyOnce, no
KeepAlive, and a CDHash SpawnConstraint. It requires the AMFI third-party
constraint enforcement gate. The fixed arguments are:

    executable --sosix-darwin-broker endpoint controller-pid controller-pid-version

The helper checks its connected controller using `sosix_darwin_broker_peer_identity`
before protocol data. The controller's `sosix_darwin_broker_observe_peer` compares
GetJob program/arguments/PID, LOCAL_PEERTOKEN, kernel PID version and unique ID,
and `csops_audittoken` CDHash. It pins the first observed incarnation; subsequent
same-label recreation is rejected. `peer_observed` describes an observation and
must never be interpreted as trusted launch provenance. Repeated checks can
catch stale tokens but cannot upgrade this observation into admission authority.

Callers must retain the bound image through launch and establish helper hardening
and dependency policy independently; CDHash alone does not prove debugger
resistance. They must keep the control descriptor private, including closing
inherited copies before fork children execute untrusted code. FD_CLOEXEC alone
does not close the pre-exec fork interval. The trusted helper must neither transfer
the connection nor exec between identity checking and use. Higher-level framing,
deadlines and operation state are separate. Calls on one state must be serialized.

RemoveJob is explicitly label-based registration housekeeping. EINPROGRESS is
returned unchanged; the submitted flag clears only on ESRCH. A possibly lost
SubmitJob reply retains the label for housekeeping. Observed identity stays
pinned. Removal grants no owned stop, kill, empty-tree, or reap receipt.

Native evidence covers wrong PID/version/hash, actual same-image impostors,
changed expected GetJob argv, pinned incarnation substitution, actual same-label
recreation, post-exec socket tokens, socket-path substitution with zero protocol
bytes, the pre-first-observation environment takeover, asynchronous removal,
wrong launch hash and renamed executable before constructors, plus an unbound
replacement execution control. It builds disposable native fixtures only.
