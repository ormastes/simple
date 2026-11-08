# Shared Container API owned output stream

Status: source implementation, runtime acceptance pending. This is output-follow,
not an interactive AgentSession. No input, TTY allocation or geometry capability
is advertised. Windows transport is explicitly unsupported by this slice.

`simple_container_output_plan_v2` resolves the existing retained workload through
the actual Linux adapter and derives a helper launch under protected local policy.
The provider alone constructs the absolute Podman route and ordered arguments:
`attach`, `--no-stdin`, `--sig-proxy=false`, followed by the complete native ID.
No shell, packet argv, PATH fallback, global cleanup or extra output reader exists.
The [Podman 5.4.2 attach reference](https://docs.podman.io/en/v5.4.2/markdown/podman-attach.1.html)
documents output following, disabling stdin, and signal proxying (enabled by
default). The explicit false value prevents helper termination from intentionally
forwarding a signal to the workload. This documentation check is not live teardown
evidence; the independent workload-alive oracle remains required.

The common outer template digest binds the complete workload plan, runtime
identity, observed provider identity, policy, exact helper CPU/memory, parent
operation/assignment/budget and immutable Caret target binding. It includes the
daemon's canonical V3 inner launch-template digest. Only the internally allocated
transport generation and not-yet-issued grant deadline are normalized out of that
inner template. The final native owner retains both generated values in its actual
request/claim. The outer digest and inner digest are distinct and must not be
substituted for one another during Host cleanup settlement.

The helper root is derived from the protected policy root and canonical helper
identity digest. The helper operation is the worker identity; the enrolled provider
generation is the launch generation. Reusing the exact helper operation/template
hits the existing exclusive daemon claim and cannot spawn another helper. The
Host journal independently refuses another begin lease for executing/unknown work.
A copied Simple value is never treated as a noncopyable launch capability.

The Host constructs `ContainerHelperAdmissionV2` only from a verified, committed
`HostHelperLeaseV1`; there is no wire decoder. Structural matching here does not
verify signatures or replace Host admission. The parent is the original Host
workload operation. Helper reservation and broker overhead are separate from the
container budget. V3 enforces exact helper CPU and memory plus the enrolled broker
pool identity. Provider policy selects `trusted-local-admin-image-fd-v1` explicitly:
the approved original image FD is executed, but trusted admin writes and dynamic
loader/library dependencies are not claimed immutable. No sealed-mode downgrade
occurs. Live Podman re-exec compatibility still requires evidence.

`simple_container_open_output_v2` rederives the plan, compares the trusted helper
admission, observes current engine identity, and independently reconciles the
exact retained running container before owned spawn. Native checks enforce the
verified deadline at launch; that deadline does not cap an admitted stream's
lifetime or authorize stopping the container. Scripted engine observations cannot
cross the native helper-spawn boundary.

Every return preserves the common provider owner. `Ready` transfers an opening
helper owner/reference bundle to the persistent smux composition; it does not
prove exec or attach success. `CleanupRequired` transfers cleanup authority even
when no reference was published. The provider retains no duplicate native handle.
Smux is the sole byte reader, adopts the full bundle only on successful fenced
publication, and otherwise keeps cleanup authority. Broker PID is diagnostic
registry metadata, never container identity or a signal target. Only durable
terminal/reap evidence and Host acknowledgement release helper accounting.
The native group stream maps both child stdout and stderr to the same output
pipe. Output is therefore merged, without channel labels or a stronger ordering
guarantee across writers. Broker control/diagnostics use protected receipts,
not that output pipe. EOF alone proves neither workload exit nor helper reap.

Pending acceptance: run the authored common planning/refusal specs; verify actual
signed helper begin and repeated/corrupted claim refusal; launch a real approved
rootless Podman workload with a fresh nonce; observe it through the sole smux pane
poll owner and independently inspect the exact container ID; close the helper and
prove the workload remains alive; retain cleanup authority across failed adoption,
EOF and broker failure; collect the real helper reap receipt before Host release.
Missing Podman, approved image, delegated cgroup, broker budget or native producer
is BLOCKED, never a passing skip. No runtime test was executed for this slice.

`simple_container_output_capabilities_v2(owner, plan)` is the common configured
discovery port after actual planning. It verifies the plan digest, owning scope,
current engine identity and exact engine route, then calls the canonical native
`linux_process_stream_template_admit_v3` preflight. That port observes the current
kernel/broker/delegation prerequisites without a helper claim, reservation or fork.
No expiry is fabricated for planning. Scripted providers and the V2 Windows
transport return unsupported. A positive result is a current observation for the
provided plan, not target authorization, reserved resources or attach readiness;
open still rederives the plan and verifies the actual admitted helper. Startup
without a plan advertises planning support only, with bind availability false.
