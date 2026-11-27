# Windows Container stream ownership

Applications use the shared Simple Container stream API. Its V3 backend union
selects a Windows Docker leaf and a real Windows native owned session, separately
from the existing Linux broker/cgroup variant. Identity, policy and helper budget
are signed and correlated before the leaf performs an engine operation.

The Windows managed raw owner reuses the existing PTY module's slot registry,
but creates ordinary bounded pipes without a pseudoconsole. It pins the exact
helper executable, builds typed argv and an explicit environment block, checks
actual CPU topology and parent-Job state, configures CPU/memory limits with
readback, creates suspended, assigns the retained Job and checks expiry before
resume. The lifetime timeout remains independent of launch-grant expiry.

Started and cleanup-required results carry the exact retained owner. The host
transfers that complete bundle to its sole stream reader; no naked HANDLE/PID
crosses RPC or becomes cleanup authority. End-of-output and leader exit alone
do not prove Job emptiness or completed native resource release.

Primary attach follows an existing container; exec creates a distinct native
Engine exec instance. Helper completion cannot prove either workload's absence.
A terminal capability cannot be advertised from a raw pipe or an unbudgeted
ConPTY server. The selected terminal path is a private Docker Engine named-pipe
broker launched inside the helper Job. It relays the actual container TTY;
there is no second host ConPTY. The broker owns the engine connection and its
bounded framing. Applications receive typed stream operations, never engine
credentials or a pipe handle.

Exec planning binds an immutable two-stage create/start intent. The broker
claims its existing private root, records create reservation before submitting
the request, persists the actual returned exec ID as a birth receipt, then
records start reservation before submitting start. Unknown create/start outcomes
are retained and never automatically retried. A refreshed start authorization
must name the same retained birth; it cannot create a replacement exec. Input
and resize require separately admitted ongoing control authority; signed intent
booleans do not supply that authority.

The raw owner, typed primary TTY creation, nonblocking broker stdio, Engine
exchange, private exec claims and read-only control observer are separate source
checkpoints. The observer's installed wrapper preserves the parent CLI baseline
and derives a distinct control identity from the actual Engine and installed
profile. A completed observation requires exact parent binding and both native
connections collected. Pending or cleanup-required owners remain retained.
The V3 broker, tagged facade and authenticated ongoing control consumer remain
required integration work; these checkpoints do not advertise interactive
support on an unqualified host.

Source and Windows qualification are separate: native Windows execution remains
NOT_RUN until an admitted fixture supplies actual evidence.
