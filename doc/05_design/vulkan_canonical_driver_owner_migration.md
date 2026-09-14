<!-- codex-design: Astra escalation, not implemented or executed evidence -->
# Canonical Pure Simple Vulkan ownership migration

Status: **DESIGNED / IMPLEMENTATION REQUIRED**. Review basis is commit
`80a110f561cab439ef6ce8552cea989dd4312498` and the rejected uncommitted
framebuffer-membership candidate recovered on 2026-09-14. This design refines
the selected O1 + B/N2 architecture; it does not select a different renderer.

## Why the framebuffer candidate cannot be accepted

The candidate embedded a mutable `VulkanDriverResourceOwner` in each
`VulkanSession` value. It compared `vulkan_get_device()` with a locally supplied
positive identity. The canonical provider returns **1 when a device exists and
0 otherwise**; this is not a device identity or a replacement generation.
Session-local generation 1 and membership 1 can therefore collide in distinct
copies. Mutating one copy does not establish that another copy observes it.

There are two further production failures beyond that table:

1. `vulkan_backend_retain_session` calls `session.retain()` and then stores
   the original value. The returned ownership reference is discarded. Similar
   ignored-return calls exist in `Render2dX86Session.retain` and the Vulkan
   provider probe. A new nonce cannot protect lifecycle while these call sites
   discard it. The old release specifications fabricate positive session
   fields and expressly expect them to authorize teardown.
2. `VulkanBackend.shutdown` flushes its *local* command, then destroys its image
   pool, presenter, font buffers and descriptors before consulting the session.
   Primitive/image batching and both packed/unpacked font paths create and
   publish commands independently. Canonicalizing only the framebuffer leaves
   those copied command and pool records outside the release authority.

Concrete counterexample: copy backend A into B while its local command is zero;
A records a glyph/image batch; B still sees zero and its flush reports success.
B's shutdown can then release resources used by A. A session refcount or a
framebuffer width check does not observe A's recording. Copying after recording
creates the complementary stale-command/double-descriptor-release case.

Raw mutexes and module-global mutable registries **are available** in Pure
Simple. This is a missing production ownership migration, not proof that the
language lacks the primitive. The rejected candidate is removed rather than
being presented as a partially safe version of that migration.

## One owner, explicit handles, bounded state

`vulkan_driver_owner.spl` will own one process-level native Vulkan device domain,
its canonical session state, and every managed Engine2D surface record. It
uses one eagerly constructed opaque raw mutex through
`std.thread_sffi.{mutex_raw_create, mutex_raw_lock, mutex_raw_unlock}`.
Initialization failure rejects without native mutation. A failed unlock
quarantines the owner and publishes no success. Never probe pthread normal
mutexes with a double unlock. The established shape is
`std.nogc_sync_mut.db.dbfs_driver.device_commit_owner`; it is a pattern to reuse,
not a second registry to import or share with Vulkan.

All mutable authority stays in module-global slots accessed under that lock.
No public handle contains a mutable table, a refcount, or the canonical backend
record. All public mutators resolve their exact handle at entry. Read-only
diagnostic snapshots and cached scalar shader handles cannot authorize calls.
Implement private `*_locked` operations so nested session/font/batch paths do
not recursively acquire the mutex. Keep source files below 800 lines by splitting
private session, surface, recording, and release operations under this owner.

The existing synchronous domain remains bound to its creating OS thread using
`thread_current_id()`. Foreign-thread entry rejects before mutation; it does
not gain an implicit executor or queue. The mutex serializes registry lifecycle;
it is not GPU-completion evidence. Host event producers continue to send their
existing immutable events to the compositor owner.

Initial bounds are 256 retained session references and 256 managed surfaces
per native owner. Keep each surface's existing 256 command-dependency/image-pool
limits and 64 MiB CPU upload scratch budget. Enforce aggregate counters as well
as individual array bounds. No unbounded closed-token history is introduced.

| Handle | Exact binding |
|---|---|
| Session reference | Owner slot, owner epoch, reference slot, reference generation, issued nonce |
| Surface lease | Session reference, surface slot, surface generation, issued nonce |
| Framebuffer lease | Surface lease, native buffer handle, kind, width, height, bytes, exact usage `0x80` |
| Recording lease | Surface lease, recording generation/nonce, exact command handle and dependencies |
| Pool entry | Owning surface, allocation generation, actual capacity/bytes, last recording reader |

An owner epoch identifies the **Pure Simple owner**. Never label it a native
`VkDevice` identity. Advance it when a new native ownership lifetime is created.
Reusing any slot advances that slot's generation; exhausting a generation
permanently retires that slot. Nonces are owner-issued, positive and monotonic;
exhaustion fails before allocation and never wraps. A stale handle remains
invalid even if the native allocator reuses its integer handle.

An ordinary value copy is an alias of the *same revocable reference*, not an
implicit retain. Releasing that reference invalidates all its aliases. An
explicit successful retain returns a **new** reference slot/generation/nonce.
Distinct retained references keep the session alive independently. No reference
count is inferred from the number of language-level values.

## Session and surface lifecycle

Session states are `vacant -> initializing -> live -> closing -> vacant`, with
`quarantined` terminal for uncertain native ownership. Reserve a slot/epoch and
initial reference before calling native initialization. Record every shader,
pipeline and instance acquisition in the owner immediately. A partial failure
releases only acquisitions belonging to that initialization, in dependency
order. Check each destroy result; retain unresolved handles and quarantine on
failure. Do not mark a resource released before its native release succeeds.

Opening another surface on the same live selected device obtains a new retained
reference to the existing canonical session. It must not reselect the global
native device or compile a competing pipeline set. Device replacement requires
zero retained references, surfaces, recording/presenter pins and unresolved
releases. Raw unsafe SFFI clients remain outside this managed guarantee; do not
silently claim registry protection for those callers.

Surface allocation receives dimensions from the real backend initialization
path, checks positive dimensions and multiplication overflow, and computes
`byte_count = width * height * 4`. Only exact usage `0x80` and the framebuffer
kind enter this table. Allocate through the canonical native facade while the
reservation is owned, then commit the returned handle into that exact slot.
A duplicate live native handle quarantines the owner; do not free an ambiguous
handle or issue a lease. Failed native allocation returns the reservation.

Admission compares the lease against both the canonical table and the
production backend's expected framebuffer handle/width/height/byte count. A
self-consistent lease for a different surface is insufficient. Release checks
the same complete binding and refuses while recording, submitted, presenter,
or capture readers remain. A failed native free leaves the record unresolved;
it cannot release the session or reuse the slot. Duplicate release has no
native side effect. Last-reference teardown requires *all* canonical resource
and reader counts to be zero and no quarantine record.

## Recording and pool ownership are part of the same change

Canonical surface state owns the pending command, descriptor arrays, image
pool, font atlas/parameter pools, and their generation/revision bindings. The
backend value must resolve this state; it cannot retain a competing mutable
copy. A copied local command field is only a stale diagnostic snapshot.

Reserve a recording lease before creating or publishing a command. Every
primitive, image, packed-font and unpacked-font producer appends to that exact
lease through owner operations. Record dependencies before issuing native
commands that consume them. Reusing a pipeline/descriptor/atlas requires the
matching canonical generation and the existing dependency/barrier contract.

Closing a surface atomically closes its admission. It consults the canonical
recording state even when the caller's cached command is zero. Before native
discard/submit/flush, resolve the recording nonce and exact command again;
retiring an already retired or mismatched copied command has no native effect.
After the existing completion mechanism succeeds, retire the exact dependency
set once. An ambiguous submit or failed dependency release quarantines the same
record. Preserve the current recovery behavior; add no idle wait, readback,
full-frame serialization, polling loop, or sleep.

All pooled resources are pinned by their canonical surface and latest reader.
Shutdown may not free presenter/font/image resources before resolving that
surface's release state. This handles both copy-before-record and
copy-after-record cases; adding a command counter to a copyable session would
not. Native session `create_command_buffer` callers must use the same recording
owner rather than opening an untracked command escape path.

## Public compatibility migration

Keep public rendering results and event/pixel semantics. Change internal
ownership transport together in one reviewable package:

- `vulkan_session.spl`: make the public session an opaque reference plus
  non-authoritative diagnostics. Resolve init/retain/validity/font installation/
  command creation/release through the owner. Eliminate fabricated-field
  validity and direct private cleanup entry from arbitrary public values.
- `backend_vulkan.spl`: consume the returned retained reference, allocate the
  exact surface lease, resolve canonical state for all native entrypoints,
  and close through the owner before any resource destruction.
- `backend_vulkan_helpers.spl`: migrate both command producers, flush/discard,
  descriptor release/quarantine and image pool lifecycle together.
- `backend_vulkan_font.spl`: migrate packed/unpacked command creation and
  publication, atlas replacement and parameter/descriptor pools together.
- `render_2d_x86_session.spl`: retain into the returned wrapper, preserving the
  original wrapper's reference. Releasing either wrapper must not consume the
  other's nonce. Audit its independent wrapper refcount at the same boundary.
- `gpu_provider_probes.spl`: remove the ignored-return extra retain; release
  the probe's actual initialized reference exactly once.
- `vulkan_resident_2d.spl`: pair arena resources/recordings with an issued
  session reference. Its unregistered buffers cannot outlive last release.
- `vulkan_context_admission.spl`: resolve canonical expected framebuffer
  membership before reporting it. Keep native-context and async support false.

Use a free `vulkan_session_retain` function if the native mutating class-return
hazard persists; it must still return an issued handle and callers must consume
it. Do not retain by returning a copied record containing another mutable owner.
Record a compiler bug if the concise typed form fails, rather than claiming
source formatting proved its semantics.

## Acceptance boundary

The linked [system plan](../03_plan/sys_test/browser_renderer_gpu_surface_owner.md)
defines the focused lifecycle and production cases. Device-free injected driver
tests exercise the same private owner transitions with controlled native
allocation/release outcomes. Their injection adapter is a test-only build input,
not an exported production `activate(identity)` or `register(raw_handle)` bypass.
They prove state transitions, not a live Vulkan provider.

Current root `bin/simple` points to the Rust bootstrap seed. The root Mach-O
compiler receipt records `simple-bootstrap 1.0.0-beta` and native smoke only;
it does not admit this general test workload. No deployed runtime exists in the
recovered worktree. Keep tests `TEST_BLOCKED` until an admitted Pure Simple
runner executes them; no source scan establishes lifecycle execution.

Even after this registry passes, `context_binding_supported=false` and
`async_claim=false` remain mandatory until the native same-live context and
presenter release port execute the selected production path. This migration
does not build Chrome, establish a C/Simple ratio, or prove an async speedup.
