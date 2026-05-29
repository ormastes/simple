# MDSOC+ Template for `sj` / `jj-wrapper-daemon`

**Scope:** Implementation guide for Phase-5 engineers (I-A, I-B, I-C, I-D).  
**Date:** 2026-04-26  
**Status:** Locked — do not diverge without updating state.md and this doc.

---

## 1. What is MDSOC+?

MDSOC+ = **MDSOC outer** (module / concern split) + **ECS inner** (business logic as
components/systems on entities). Kernel and drivers use MDSOC-only. Userland services
(like `sj`) use MDSOC+.

- **MDSOC outer:** Each architectural concern is a separate `.spl` file/module with
  explicit imports. No concern imports from a peer concern except through a declared
  public API. Lifecycle only imports from server, queue, lease, audit. Client imports
  nothing from the daemon side.

- **ECS inner:** Business logic inside each concern is modeled as:
  - **Entities:** `Request`, `Lease`, `Operation` (plain structs with an `id: text` field)
  - **Components:** data attached to entities (e.g. `LeaseKind`, `LeaseExpiry`, `VerbEntry`)
  - **Systems:** functions that advance entity state on each daemon tick

---

## 2. File Layout

```
src/lib/nogc_sync_mut/service/          # AC-1 generic service base (I-A, I-B)
  lifecycle.spl                         # Capsule: PID file, SIGTERM handler
  uds_server.spl                        # Capsule: UDS accept loop, JSON framing
  request_queue.spl                     # Capsule: FIFO + priority lanes
  lease_manager.spl                     # Capsule: exclusive/shared leases, ghost reclaim

src/app/sj/                             # AC-4 bin/sj CLI + daemon (I-C, I-D)
  main.spl                              # Entry point: parse argv, route to daemon or in-process
  client.spl                            # Capsule: UDS client, BUSY/error surface
  policy.spl                            # Capsule: pre-queue forbid check
  translator.spl                        # Capsule: git→jj verb string-table dispatch
  jj_exec.spl                           # Capsule: jj/git subprocess execution, flag injection
  audit.spl                             # Capsule: audit log writer (.sj/audit.log)
  daemon.spl                            # Capsule: composes service base + vcs-specific concerns

src/lib/nogc_sync_mut/service/extern.spl  # Where rt_unix_socket_* extern declarations live
```

---

## 3. Module Naming Convention

| File | Module path (use statement) | Public type |
|------|-----------------------------|-------------|
| `lifecycle.spl` | `std.service.lifecycle` | `DaemonConfig`, `DaemonHandle` |
| `uds_server.spl` | `std.service.uds_server` | `UdsServer`, `UdsClient` |
| `request_queue.spl` | `std.service.request_queue` | `RequestQueue`, `QueueEntry` |
| `lease_manager.spl` | `std.service.lease_manager` | `LeaseManager`, `Lease`, `LeaseKind` |
| `policy.spl` | `app.sj.policy` | `check_forbidden` |
| `translator.spl` | `app.sj.translator` | `translate`, `VerbEntry`, `Classification` |
| `jj_exec.spl` | `app.sj.jj_exec` | `exec_jj`, `inject_read_flags` |
| `client.spl` | `app.sj.client` | `SjClient`, `SjResult` |

---

## 4. Capsule Import Rules

```
lifecycle  ←  (no daemon peers; imports only std.io_runtime, extern.spl)
uds_server ←  extern.spl, std.io_runtime
request_queue ← lease_manager (reads lease state to classify), std.io_runtime
lease_manager ← audit.spl, std.io_runtime
audit      ← std.io_runtime (writes only; no imports from other capsules)
client     ← std.io_runtime (UDS send/recv only; does NOT import daemon-side modules)
policy     ← translator (reads VerbEntry.classification)
translator ← (pure; no runtime imports; string table only)
jj_exec    ← translator, std.io_runtime
daemon     ← lifecycle, uds_server, request_queue, lease_manager, audit, policy, translator, jj_exec
```

**Rule:** No circular imports. `client.spl` is the only module imported by `bin/sj` callers.
The daemon side (`daemon.spl`) is never imported by the client.

---

## 5. ECS Component/System Convention

### Entities (plain structs)

```simple
# In lease_manager.spl
struct Request:
    id: text
    verb: text
    argv: [text]
    lease_kind: LeaseKind
    submitted_at_ms: i64

struct Lease:
    id: text
    holder_pid: i32
    kind: LeaseKind
    granted_at_ms: i64
    ttl_ms: i64
    max_hold_ms: i64

struct Operation:
    lease_id: text
    jj_pid: i32
    started_at_ms: i64
```

### Components (attached to entities via wrapper structs, not inheritance)

```simple
struct LeaseExpiry:
    lease_id: text
    expires_at_ms: i64

struct GhostCandidate:
    lock_path: text
    mtime_ms: i64
    lsof_empty: bool
    no_live_lease: bool
```

### Systems (functions called each tick)

```simple
fn tick_watchdog(mgr: LeaseManager, now_ms: i64)  # fires SIGTERM on max_hold exceeded
fn tick_ghost_reclaim(mgr: LeaseManager, now_ms: i64)  # reclaims dead-PID or TTL-elapsed leases
fn tick_queue_drain(queue: RequestQueue, mgr: LeaseManager)  # dequeues and dispatches
```

---

## 6. Where Extern Declarations Live

All `extern fn rt_unix_socket_*` declarations go in:

```
src/lib/nogc_sync_mut/service/extern.spl
```

Only `uds_server.spl` imports this file. Other modules never touch the externs directly.
After adding externs, run:
```
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```
(per `feedback_extern_bootstrap_rebuild.md` — `bin/simple build` silently no-ops for new externs.)

---

## 7. Where Traits Live

Traits shared across capsules go in:

```
src/lib/nogc_sync_mut/service/traits.spl
```

Use `impl Trait for X { ... }` blocks, **never** header-form `class X: Trait`
(per `feedback_class_trait_header_form_also_fails.md`).

Example:

```simple
# traits.spl
trait Drainable:
    fn drain(self) -> bool

# request_queue.spl
use std.service.traits

impl Drainable for RequestQueue:
    fn drain(self) -> bool:
        # drain implementation
        self.entries.is_empty()
```

---

## 8. Minimal Skeleton (5–10 lines)

```simple
# src/lib/nogc_sync_mut/service/lifecycle.spl
use std.io_runtime

struct DaemonConfig:
    pid_path: text
    socket_path: text
    max_hold_ms: i64

struct DaemonHandle:
    pid: i32
    config: DaemonConfig

fn start_daemon(config: DaemonConfig) -> Result<DaemonHandle, text>:
    # Write PID file, register SIGTERM handler, return handle
    Result.err("not yet implemented")
```

---

## 9. Phase-5 Gate Order

1. **I-A first:** `extern.spl` + `uds_server.spl` + bootstrap rebuild → run `uds_extern_spec.spl` green  
2. **I-B:** `lifecycle.spl`, `request_queue.spl`, `lease_manager.spl` → run `service_lifecycle_spec`, `request_queue_spec`, lease specs  
3. **I-C:** `policy.spl`, `translator.spl`, `jj_exec.spl`, `client.spl` → run all `app/sj/*` unit specs  
4. **I-D:** `daemon.spl` integration → run `test/system/sj_concurrency_spec`, `sj_ghost_index_lock_spec`, `sj_push_pattern_spec`
