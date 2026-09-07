# `ipc_wire.spl` is orphaned; the canonical syscall-21 dest-buffer recv ABI never landed

- **Filed:** 2026-09-06
- **Area:** os / kernel / ipc
- **Status:** OPEN — codec guarded, wiring absent
- **Base examined:** `origin/main` @ `4699194f81e`
- **Guarding spec:** `test/01_unit/os/kernel/ipc/ipc_wire_transfer_spec.spl`
  (16 cases, 16 passed under the Sep-5 bootstrap seed)

## Summary

`src/os/kernel/ipc/ipc_wire.spl` ships a complete, correct, well-documented
envelope codec and ring-3 pointer policy, and **nothing under `src/` imports
it**. The syscall and client halves that its header comment describes as its
consumers do not read it, and the canonical receive ABI those consumers were
supposed to grow was never written. The codec is therefore dead code that
happens to be right; this record is the ratchet that says so out loud rather
than letting a green spec imply a live data path.

## Evidence

### `ipc_wire.spl` has zero importers

```
grep -rn "ipc_wire" src --include='*.spl' | grep -v "^src/os/kernel/ipc/ipc_wire.spl"
```
returns nothing. `src/os/kernel/ipc/syscall_ipc.spl` does not import it. The
only other mention in the tree is by name, in
`test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl`.

### The canonical syscall-21 dest-buffer ABI does not exist

A 434-line, 30-case spec at the same path as the new spec was added in
`d13c3636740` (2026-08-30) and deliberately deleted in `f91b3a48702`
(2026-08-31, "drop two stray specs") because 21 of its 30 cases failed. It
imported, from `os.kernel.ipc.syscall_ipc`:

- `ipc_decode_send_args`, `ipc_decode_recv_args`
- `ipc_check_user_read`, `ipc_check_user_write`

and, from `IpcManager`: `create_named_port`, `send_with_payload`, `recv_wire`,
`queued_message_count`, `queued_owned_payload_bytes`. **None of those nine
symbols exists anywhere on origin**; `git log -S ipc_decode_recv_args -- src/`
finds no commit. `d13c3636740` is retained as the *design reference* for the
intended contract, not as a claim that it shipped.

What origin actually implements for syscall 21 is
`_handle_ipc_recv_state` (`src/os/kernel/ipc/syscall_ipc.spl:144`): args are
`arg0 = port`, `arg1 = timeout`, and on delivery it returns
`_ipc_materialize_received(header, payload)` — a **kernel virtual address** of
a materialized envelope, not a count of bytes written into a ring-3 buffer.
`a3`/`a4` are unused. The intended `a3 == 0 && a4 == 0 && a2 >= 32` legacy
discrimination has nothing to discriminate.

Related but distinct, and stated so the deferral is not overclaimed: syscalls
**132/133** (`_handle_ipc_send_owned_v1_state` /
`_handle_ipc_recv_owned_v1_state`) *do* implement a dest-buffer form
(`arg2` = user pointer, `arg3` = capacity, EFAULT on a null pointer, EMSGSIZE
below 32 bytes). They have their own spec,
`test/01_unit/os/kernel/ipc/ipc_owned_syscall_v1_spec.spl` — which is itself
`outcome=ERROR executed=0` on this base, see below. The deferred contract in
this record is specifically syscall **21**.

### `IpcManager.send_owned`'s success path calls an undefined function

`src/os/kernel/ipc/ipc.spl:353` calls `_copy_owned_payload(payload)`. That
function is **defined nowhere in `src/`** — the call site is the only
occurrence in the tree, and `git log -S 'fn _copy_owned_payload' --all -- src/`
finds no commit that ever added a definition. Every `send_owned` that passes
its preconditions dies:

```
✗ round trips a payload
  semantic: function `_copy_owned_payload` not found
```

Consequence: the manager-level send→recv payload round trip cannot be
guarded. The new spec therefore covers only `send_owned`'s **rejection**
paths (`-4` over-page payload, `-1` unknown destination), which return before
reaching line 353.

### `OwnedIpcReceiveStatus` / `OwnedIpcReceiveResult` are referenced but never defined

`src/os/kernel/ipc/ipc.spl` uses `OwnedIpcReceiveStatus.<variant>` and
constructs `OwnedIpcReceiveResult(...)`; `src/os/kernel/ipc/syscall_ipc.spl:7`
imports `OwnedIpcReceiveStatus` from `os.kernel.types.ipc_types`. That module
is 35 lines and defines `IpcPort`, `IpcEndpoint`, `IpcMessage` and `IpcFlags`
only. Neither name is defined anywhere under `src/`. The seed tolerates the
import rather than failing it, which is how this stayed invisible.

### Every scenario needing the syscall/scheduler closure is unloadable on this base

Importing `os.kernel.ipc.syscall_ipc` and `os.kernel.scheduler.scheduler`
aborts the whole file before any example runs:

```
error[E1002]: function `sosix_fs_kernel_uninstalled_positioned_state_v1` not found
  = help: check the function name or import the module that defines it
SPEC FILE VERDICT: ... outcome=ERROR declared>=2 executed=0 passed=0 failed=0
```

The symbol is imported at `src/os/kernel/abi/syscall_shim_positioned.spl:21`
from `os.sosix.fs.kernel_positioned_dispatch_v1`; that module exists and does
not define it. This is **pre-existing and not caused by the new spec** — the
already-tracked `ipc_owned_syscall_v1_spec.spl` fails identically on the same
base (`outcome=ERROR declared>=8 executed=0`). The tip `4699194f81e` is PR
#388 "sosix-runtime-unification", merged 2026-09-06, which is the first place
to look.

Because of this, the two planned hosted syscall-21 scenarios (non-blocking
`EAGAIN` on an empty port; `-1` on a missing port) are **not shipped**. A spec
file that is `executed=0` guards nothing, so they were dropped rather than
left permanently red.

### Enum-to-integer casts all yield 0 on this lane

Probed directly under the Sep-5 seed:

```
CapTransfer as u32 = 0
Sync as u32 = 0
```

`IpcFlags` declares `Sync, Async, CapTransfer, Reply`, so `CapTransfer as u32`
should be 2. Because `send_owned` guards with
`header.flags == (IpcFlags.CapTransfer as u32)` (`ipc.spl:329`), **every
message with `flags == 0` is rejected as `-7`
(`IPC_OWNED_CAPABILITY_UNSUPPORTED`)** on this lane — an undocumented,
silently over-broad refusal. A sender must set a non-zero flags word (e.g.
`IPC_WIRE_V1_FLAG`) to get past it, which is the accident that makes the new
spec's `-1` unknown-destination case reachable at all.

## What is guarded now

`test/01_unit/os/kernel/ipc/ipc_wire_transfer_spec.spl`, 16 cases, all green:

- the 32-byte header byte layout at +0/+8/+16/+20/+24/+28/+32, little-endian,
  including the two offsets the ring-3 client reads (`msg+24`, `msg+32`);
- header-only envelopes, and truncation of an over-page payload to
  `IPC_WIRE_CAPACITY` with a `payload_len` that cannot over-promise;
- fail-closed out-of-range behaviour of `ipc_wire_read_u32` / `_u64`;
- extreme-scalar round trip (u64 max port, u32 max method/flags);
- the compositor method lift out of the first payload word;
- mutual consistency of the geometry constants;
- the full `ipc_user_range_check` policy: null/low-page, kernel-half,
  end-of-range, wraparound, the length band, and the zero-length
  short-circuit, including both inclusive/exclusive boundaries;
- `send_owned`'s `-4` and `-1` rejections.

## Unblock condition

1. Define `_copy_owned_payload`, `OwnedIpcReceiveStatus` and
   `OwnedIpcReceiveResult`, so `IpcManager.send_owned`/`recv_owned` can
   execute end to end.
2. Repair `sosix_fs_kernel_uninstalled_positioned_state_v1` so the kernel
   syscall closure loads; then restore the two syscall-21 scenarios here and
   un-red `ipc_owned_syscall_v1_spec.spl`.
3. Wire `ipc_wire_encode` and `ipc_user_range_check` into
   `src/os/kernel/ipc/syscall_ipc.spl` and into the ring-3 client
   `examples/09_embedded/simpleos_remote_gui/remote_window_runtime.c`, so the
   codec becomes the single encoder rather than a second, unused one.
4. Only then is the canonical syscall-21 dest-buffer ABI assertable. Do not
   assert it before the code exists.

## Explicitly not done

Resurrecting the deleted 434-line spec, or implementing the nine missing
symbols to make it pass. `f91b3a48702` refused exactly that, and doing it
under a "recovery" label would be new kernel ABI work.
