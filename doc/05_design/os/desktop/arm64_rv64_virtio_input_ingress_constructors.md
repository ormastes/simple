<!-- codex-design -->
# ARM64 and RV64 VirtIO WM ingress constructors

## Decision

Each architecture owns a one-shot constructor that initializes its real
VirtIO input producer, requires both keyboard and pointer readiness, retains
one shared decoder in architecture-local storage, and registers a module
callback in the bounded baremetal input registry. The result is an opaque
positive handle; zero denotes every refusal. `DesktopShell` remains free of
ARM64 and RV64 platform imports.

The constructors are intentionally not wired into the existing architecture
desktop entry loops in this change. Those loops still own direct decoder state
and detailed device receipts. A later composition-root migration must remove
that direct owner at the same time it installs the returned registry handle;
running both would split decoder state and steal events from one queue.

## Safety and ordering

- Invalid dimensions, absent devices, partial readiness, duplicate creation,
  and registry exhaustion fail closed.
- Each architecture retains exactly one decoder for the boot lifetime. No
  optional aggregate unwrap crosses the callback boundary.
- One callback invocation returns at most one `HostInputEvent`. The existing
  backend preserves key-before-pointer sequence ordering and bounds raw-event
  pumping to 64 records.
- Admission and the single array insertion occur only during construction.
  Registry refusal rolls that insertion back exactly. The polling path has no
  explicit collection growth or whole-compositor copy; runtime allocation
  behavior remains unverified.
- x86 keeps its existing explicit legacy readiness capability unchanged.

The constructor is a boot-composition API and must run on the single boot
thread before scheduler or secondary-hart activation. It is not a concurrent
runtime registration API. The duplicate-create guard also rejects reentrant
use after owner publication.

## Composition follow-up

Migrate each ARM64/RV64 entry atomically: remove its direct input-backend poll,
construct the architecture ingress once after display dimensions are known,
install the returned handle in the shell, and move architecture evidence to a
non-consuming observation surface. Until that migration is coherent, the new
constructors remain available but unused.
