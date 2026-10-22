# Native macOS Simple Container qualification

Status: open, P1. The user selected macOS programs running directly on the
Mac host, with shared Simple Container logic and no VM. SimpleOS programs run
through the SimpleOS kernel provider on SimpleOS.

Implement the [native Mac plan](../../03_plan/agent_tasks/native_macos_simple_container.md)
and meet [REQ-NMC-001–005](../../02_requirements/feature/native_macos_simple_container.md).
The shared host admission and SDN source now recognizes `native-sandbox`, but
the Mac signed helper/provider and live sandbox/exit/cleanup evidence are
missing. The earlier QEMU/HVF preflight is not evidence for this TODO.

2026-09-28 Simple implementation: the Mac leaf now has a bounded Mach-O
format preflight and a request gate in
`src/lib/nogc_async_mut/container/providers/macos/`. It reuses
`RuntimeIdentityV1` and `RuntimeOperationV1`, rejects cross-OS/VM requests and
forged lifecycle state, and keeps even a valid-format request blocked until a
signed independent sandbox owner exists. The focused `.spl` unit specs are
written but unrun under this session's verification cap. This is admission
work, not a native container launch or completed Mac provider.

Mac host check (2026-09-27): macOS 26.5 has `/usr/bin/clang`, `codesign`, and
`security`; `security find-identity -v -p codesigning` reports zero valid
identities. An ad-hoc signature can support a local App Sandbox prototype,
but this host has no distribution identity for a signed release helper.
No native lifecycle provider, helper entitlements, or live App Sandbox
qualification exists in this checkout. Complete those pieces on this Mac
before calling the Mac implementation done.

2026-09-28 probe: an ad-hoc signed App Sandbox CLI and a signed `.app` fixture
both verified their signatures but exited with SIGABRT before `main` in this
restricted Codex host session. An unsandboxed control reached `main` and read
its test files. The probe establishes an environment/launch blocker here; it
does not prove that App Sandbox denied a file or that the Mac route works.
Repeat on an unrestricted Mac login, record actual sandbox state and the
host-sentinel/workspace checks, then test nonzero exit and cleanup.
The exact commands and results are in the
[Mac preflight report](../../09_report/native_macos_simple_container_preflight_2026-09-28.md).
The [replay script](../../../scripts/check/check-native-macos-simple-container-sandbox.shs)
is a host preflight only; it cannot mark this TODO complete.

The existing Process Observation V4 owner provides pinned execution, deadlines,
and bounded output on supported hosts, but reports unavailable on macOS and
does not advertise exact descendant containment.
Before admitting untrusted work, establish a real no-detach/no-child authority
and run the detaching-child cleanup case. Keep launch unavailable for that
class until the authority and live evidence exist.

Other-host follow-up is already tracked in TODO 348 (Linux rootless), TODO 353
(Windows Server HCS), and TODO 354 (FreeBSD jail). Each requires its own live
host fixture and exit/destroy/isolation evidence; Mac results do not qualify
those providers.

Do not mark complete from a process launch alone. Confirm the actual App
Sandbox boundary, exact process exit, prohibited host-sentinel access,
identity-bound cancellation, and fresh cleanup. The SimpleOS kernel path has
its separate authenticated-loader bug 355.

2026-09-28 authenticated worker ingress: `worker_protocol_v1.spl` in the Mac
provider directory now implements a bounded byte frame, HMAC-SHA256 binding
of the complete attempt identity and fresh session nonce, strict sequences,
one submit/cancel, and channel close. Focused unit specs include an independent
HMAC known vector and replay, cross-attempt, mutation and size rejection cases;
they remain unrun under this logical session's verification cap. This is a
reusable ingress component, not an executable worker or launch provider.
An accepted request authenticates only possession of the provisioned key.
The transport must bound reads before allocating the full frame; the service
must retain one session and provision fresh secret/nonce values through an
OS-authenticated channel. Closing the channel does not prove process cleanup.

Native integration remains blocked by missing Simple bindings for independent
XPC/app service launch, audit-token/code-signing peer validation and secure
session provisioning. The existing Unix socket and parent-result frame
surfaces do not supply those Mac authorities. Process Observation V4's native
capability function returns unavailable/ENOTSUP outside Linux, and the browser
sandbox spawn implementation is also Linux-only. Generic process spawning
cannot replace the required pinned identity, independent sandbox, or
no-detach/no-child authority. Implement these native owners and live evidence
before connecting ingress acceptance to any container lifecycle transition.

2026-09-28 native bundle generator: `src/app/macos_xpc_bundle/` now stages a
macOS `.app` with an embedded `.xpc` service from two supplied native
executables. It writes the required metadata and independent service sandbox
entitlement, signs the nested service before the host app, and verifies both.
Explicit `-` ad-hoc signing supports local development without a certificate.
The generator and its focused Simple specs are unrun under this session's
verification cap. A separate host-only signing experiment using copies of
`/usr/bin/true` confirmed that this Mac accepts the same ad-hoc hardened-runtime
nested signing and strict verification order; it did not launch an XPC service.
Build the real Simple XPC client and `xpc_main` service, then connect and test
them on an authorized unrestricted Mac. Supplied executables must be
self-contained; the generator does not bundle non-system dynamic libraries or
resources. This generator alone does not complete
the native container provider.
