# Windows owned exec-control observation

Status: source checkpoint, **NOT_RUN**. No Windows or compiler execution is
claimed. The shared session facade and signed Host delegation must consume these
owners before broker effects are enabled.

`WindowsInstalledExecControlProfileV3` canonically wraps the original installed
Docker policy and stream policy with exact component hashes. Its derived wrapper
hash is policy integrity, not an Engine observation. The retained adapter compares
the Docker policy bytes with its original installed bytes, checks existing exact
runtime authority and refreshes native host continuity before beginning a probe.
Scripted adapters are explicitly rejected at both native-probe and
control-observation planning entries; synthetic fixture provenance cannot be
combined with a real Engine response to manufacture an observed control pin.
The existing internal scope-fence transformation applies only to the effective
Docker policy used for inspection; it does not rewrite the installed wrapper.

The probe owns bounded nonblocking exchanges for API1.48 `info` and exact
container inspection. It retains each actual connected pipe observation before
writing, requires the same observed server PID across the two queries, and uses
the strict Engine binder to check Windows OS/kernel/engine identity, pinned
image, process isolation, selected user, CPU/memory, network, argv/cwd, terminal
flags, mounts and all managed scope labels. It cannot create or start an exec.
The actual probe calls `WindowsDockerEngineExchangeV3.begin_read_only_v3`.
Both that entry and the compatibility `begin_v3` reject every operation except
canonical info and exact container-inspect GETs before any native acquisition.
The exchange module still contains pure mutation codecs and transport state
types; these are not an admitted mutating session. Correct create/start data
with a matching deadline is rejected until an actual Host-verified effect owner
and stable installed scope/child-operation claim are implemented.

Each poll opens one connection, advances one exchange, or collects one exchange.
The overall monotonic window is checked before operations and after collection.
Complete requires actual joined evidence and both connections closed. Failed
collection invalidates the observation and retains the exact owner for cleanup.
Explicit collect returns Closed and invalidates observation; it is never an
exec/workload absence receipt.

The control identity hashes a separate domain containing the parent baseline,
installed wrapper hash, actual Engine identity and fixed pipe/API profile. The
observation separately carries full parent runtime identity, semantic request
digest, scope, query digests, actual response/endpoint evidence digest and native
clock sample. A policy hash or copied parent baseline cannot fill this field.

`stream_plan_with_control_v3` returns its supplied probe on every path, including
pending or invalid requests. The common API must retain that native owner in an
explicit session union. No native handle or mutable provider/WAL crosses into a
worker, and no wire decoder constructs the nonserialized exec admission carrier.

Pre-native negative specs exercise the real factory with invalid binding and
installed-profile inputs. Their baseline values are synthetic validation data,
not native observations. Positive Windows/CID and cleanup-fault qualification
requires the actual shared API fixture and remains outstanding.
