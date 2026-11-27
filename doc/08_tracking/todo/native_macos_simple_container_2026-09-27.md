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

## 2026-11-13 verification on Linux aarch64 (no Mac available)

Host: Linux aarch64 (`Linux 6.17.0-1032-nvidia`), release/1.0.0 at
`517f20ae777`. Binary: Rust seed built from that head. Per
`.claude/rules/bootstrap.md` seed verdicts are **seed-diagnostic**, not
self-hosted qualification; the sys_test plan still requires the self-hosted
runtime. Every run was capped (`systemd-run --user --scope -p MemoryMax=16G
timeout 900`) and run serially. This section supersedes the "unrun" notes
above for the specs listed.

### (a) Host-independent: ran here

| Item | Spec | Result |
|---|---|---|
| Mach-O format preflight (REQ-NMC-001 part) | `test/01_unit/lib/nogc_async_mut/container/providers/macos/executable_preflight_v1_spec.spl` | 15/15 pass |
| Authenticated worker ingress (HMAC, replay, size) | `.../providers/macos/worker_protocol_v1_spec.spl` | 10/10 pass |
| Provider admission/provision/framing, fail-closed lifecycle | `.../providers/macos/native_sandbox_provider_v1_spec.spl` | 9/9 pass |
| XPC `.app` bundle generator (staging, plist, sign order, as spec mocks it) | `test/01_unit/app/macos_xpc_bundle/generator_spec.spl` | 8/8 pass |
| Host capability contract incl. `native-sandbox` (REQ-NMC-005 part) | `test/01_unit/lib/common/contracts/container/host_capability_v1_spec.spl` | 14/14 pass |
| Host capability SDN source | `test/01_unit/lib/common/contracts/container/host_capability_sdn_v1_spec.spl` | 6/6 pass |
| Superseded VM-route host preflight, faked `uname`/QEMU | `test/00_unit/scripts/macos_simpleos_container_host_spec.shs` | PASS (contract only) |
| Superseded VM-route guest dispatcher rejection paths | `test/01_unit/os/services/container/macos_simpleos_guest_dispatch_v1_spec.spl` | 2/3 pass; 3rd blocked (see toolchain row) |

### Bugs found and fixed here (red -> green on the seed)

1. **`ContainerWorld.image_digest_of` never existed.**
   `src/os/services/container/container_runtime.spl:79` calls it on every
   `start_into_scheduler`, but `container_manager.spl` never defined it
   (`git log -S'fn image_digest_of' --all` is empty). Every SimpleOS container
   launch, including the Mac guest dispatcher's, failed with
   `method image_digest_of not found`. Fixed by adding the accessor over the
   create-time RO base digest (`images[idx].base_digest`, which GC keeps).
   Red: `container_runtime_spec` 2/5, guest dispatch 2/3, both on that error.
   Green: `container_runtime_spec` 4/5, and the error is gone in both.
2. **Spec ELF fixtures violated PT_LOAD congruence.** The fixtures in
   `container_runtime_spec.spl` and `macos_simpleos_guest_dispatch_v1_spec.spl`
   placed `p_offset=0x80` at `p_vaddr=0x400000` with `p_align=0x1000`. The
   loader (`elf_loader.spl:355`, hardened in `c6cd52b5574`) correctly rejects
   this (`ELF PT_LOAD alignment is invalid` -> `-8`). Fixed in the fixtures
   (`p_vaddr`/`e_entry` = `0x400080`); the loader is unchanged.

### Toolchain-blocked (neither PASS nor Mac-blocked)

The remaining live-launch cases (`container_runtime_spec` "marks running only
after a hash-bound policy creates a live task", guest dispatch "publishes only
the matching scheduler-observed task exit") now fail with `-13` from the
managed launch seam. `test/01_unit/os/kernel/loader/managed_workload_launch_spec.spl`
fails the same way on the same seed (3/5, `expected -13 to be greater than 0`),
so this is the seed defect already tracked by bug 355
(`simpleos_managed_container_launch_authority_mismatch_2026-09-27.md` and its
two seed blockers), not a container defect. Re-run on the self-hosted binary.

### (b) Needs a real Mac: still BLOCKED (not PASS, not skipped)

| Item | Why |
|---|---|
| REQ-NMC-002 signed helper launches pinned program; changed signature fails | `codesign`, App Sandbox entitlements |
| REQ-NMC-003 live nonzero exit, host sentinel denied, cancel/timeout, detaching child | App Sandbox, launchd/XPC |
| XPC client + `xpc_main` service connect | XPC / `launchd` |
| Audit-token / code-signing peer validation; OS-authenticated key provisioning | Security.framework, XPC |
| Process Observation V4 native capability on macOS | returns unavailable outside Linux |
| Generator output actually signs and verifies (`codesign --verify --strict`) | `codesign` |

Missing host: an unrestricted macOS login (Apple Silicon, ad-hoc signing is
enough for local qualification; zero distribution identities was the last
recorded state). Resume, from the repo root on that Mac:

```bash
printf 'host-secret\n' > /tmp/simple-host-sentinel
sh scripts/check/check-native-macos-simple-container-sandbox.shs /tmp/simple-host-sentinel
bin/simple test test/01_unit/lib/nogc_async_mut/container/providers/macos/
bin/simple test test/01_unit/app/macos_xpc_bundle/generator_spec.spl
```

Expected artifacts: the script's `signed CLI status:` and signed `.app`
status lines showing the probe reached `main` with the App Sandbox active and
the sentinel read **denied** (exit 0 from the script); the three provider
specs and the generator spec green on the self-hosted `bin/simple`; then the
first real REQ-NMC-002/003 receipts once the XPC client/service exist.
