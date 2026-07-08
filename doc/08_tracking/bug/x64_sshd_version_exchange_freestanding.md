# BUG: x86_64 sshd fails SSH version exchange under freestanding native-build

**Status:** open
**Severity:** high (blocks all x86_64 SSH login; rv64 SSH login is proven, x64 is not)
**Component:** sshd version exchange / net recv facade under freestanding native-build
**Found:** 2026-07-08, booting a merged ring-3 + sshd x86_64 kernel

## Symptom

A real host `ssh -p 2222 root@127.0.0.1 true` connects to the in-guest x86_64
sshd, the TCP connection is accepted and the server banner is sent, the client
version IS received correctly C-side, but the server then reads an EMPTY client
version and aborts:

```
[tcp] Connection established on port 22
[sshd] accepted client fd=200
[sshd-session] version banner send rc=22
[tcp-recv-version] text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16   <- correct C-side
[sshd-session] version raw bytes len=41 hex=57579a5757575757...     <- GARBAGE (Simple-side)
[rt-net] version recv raw-fast
[rt-net] version recv raw-fast done text=                            <- EMPTY
[sshd-session] version recv text=
[sshd-session] invalid client version text=
[sshd-session] run stop version_exchange
```

QEMU serial: `build/os/x64-ssh-ring3.serial.log` from the boot of
`build/os/simpleos_ssh_ring3.elf`.

## Analysis

Two freestanding-native-build issues in the version-exchange path:

1. **Double-take consumes the buffered version.** `rt_net_recv_version_bytes`
   (`src/os/kernel/net/rt_net_socket_facade.spl:366`) calls
   `rt_boot_tcp_take_version_bytes(fd)` (extern, L18) which appears to CONSUME the
   buffered version; the subsequent `rt_net_recv_version_text` (L326) →
   `rt_boot_tcp_take_version_text(fd)` (L17) then returns empty. The session
   (`src/os/apps/sshd/ssh_session.spl`) takes both, so whichever runs second gets
   nothing. Either the C "take" must be non-consuming (return the same buffer), or
   the session must take exactly once and derive both text+bytes from it.
2. **`[u8]` read-back is boxed.** The Simple-side hex dump of the 41 received bytes
   (`version raw bytes … hex=5757…`) is garbage while the C-side text is correct —
   the boxed-`[u8]` stride-1 read hazard (same class fixed in
   `x86_64_fs_exec_ring3.spl` via `rt_bytes_u8_at`/mmio and in the loader frame via
   `.to_u64()`-boxing). Any `arr[i]` over the received `[u8]` reads garbage; use
   `rt_bytes_u8_at` / the C helpers consistently.

Why rv64 passes and x64 does not: rv64 is the proven SSH lane with durable serial
transcripts (`build/os/rv64-ssh-live.serial.log`); the x64 ssh_live spec has never
produced passing evidence (`doc/08_tracking/test/test_result.md` shows 100%
failure). The freestanding `[u8]`/take semantics differ on the x64 codegen path.

## Repro

Build + boot the merged kernel (proven to build, boot, and reach the sshd accept
loop AFTER vmm_init — net survives vmm):
`examples/09_embedded/simple_os/arch/x86_64/ssh_ring3_entry.spl`, native-build to
`build/os/simpleos_ssh_ring3.elf` (see
`doc/05_design/os/ssh/simpleos_ssh_ring3_exec_plan.md`), boot under QEMU q35 with
`-netdev user,hostfwd=tcp::2222-:22 -device virtio-net-pci` + an NVMe disk, then
`ssh -p 2222 root@127.0.0.1 true` (password `simpleos`).

## Deeper root cause (traced 2026-07-08)

It is NOT merely a double-take that a reorder fixes — the underlying byte access is
corrupt on the x64 freestanding codegen:

- The C marshalling is correct: `_tls_runtime_array_from_bytes` (baremetal_stubs.c
  :10325) builds the `[u8]` as `out->items[i] = ENCODE_INT(buf[i])` over the correct
  string data (`rt_boot_tcp_take_version_bytes` :7512 → `rt_net_recv_version_text`
  → `s->data`, and the C side prints the correct `SSH-2.0-OpenSSH…`).
- Yet the Simple side reads it back corrupt: `_u8_at` = `rt_bytes_u8_at(data,i)`
  (`ssh_session_helpers.spl:58`, the authoritative raw decoder) returns non-`S` for
  index 0, so `_ssh_identification_bytes_start_ssh2` fails. Length is correct (41),
  values are wrong — an ENCODE_INT/decode or element-stride mismatch specific to the
  x64 freestanding native-build.
- The text→bytes reconstruction path is ALSO flagged unreliable by the existing
  design comment (`ssh_session.spl:806-808`: "the live text object can print
  correctly while returning corrupt values from split/char_at byte reconstruction").

So under x64 freestanding native-build there is currently **no reliable way to
recover the exact client-version bytes** — needed both to parse the version AND to
compute the KEX exchange hash H (which signs V_C/V_S exactly). This is a **core
runtime string/`[u8]` byte-access correctness bug on x64 freestanding**, not a
sshd-local logic bug; it will recur through KEX/packet/auth. Fixing it means making
`rt_bytes_u8_at` (and `char_at`) agree with `_tls_runtime_array_from_bytes`'
element encoding on the x64 native-build path — the same ENCODE/decode/stride class
already seen in the loader (`x86_64_fs_exec_ring3.spl` uses raw mmio + explicit
`rt_bytes_u8_at`, and the frame builder hit `.to_u64()`-literal boxing). A
speculative sshd reorder is NOT a fix and risks the proven rv64 lane.

## Deepest conclusion: a C↔Simple RuntimeValue ABI mismatch on x64 native-build

The C runtime is internally consistent, so the corruption is NOT in the sshd or the
C helpers:
- `_tls_runtime_array_from_bytes` (:10325) stores `runtime_array_inline_items(out)[i]
  = ENCODE_INT(buf[i])` and sets `out->items` to that inline location.
- `rt_bytes_u8_at` (:9623) reads `_rv_byte(runtime_array_items(arr)[idx])`;
  `runtime_array_items` (:310) returns `a->items` (= the inline location);
  `_rv_byte` (:6212) does `IS_INT(v) ? DECODE_INT(v) : v` → recovers the byte.

Build and read are both C in the same file with the same structs, so C→C is exact.
The value is corrupted only because the `[u8]` RuntimeValue **round-trips through
the Simple x64 native-build codegen** (C `rt_boot_tcp_take_version_bytes` → Simple
facade `rt_net_recv_version_bytes` → Simple `do_version_exchange` locals → C
`rt_bytes_u8_at`). This points to a **C↔Simple `RuntimeValue`/`[u8]` ABI or
representation mismatch on the x86_64 freestanding native-build path** (calling
convention / tag handling for heap RuntimeValues passed across the C boundary).

Corroborating evidence elsewhere on x64 freestanding:
- The ring-3 loader deliberately AVOIDS `[u8]` and reads the ELF via `mmio`/raw
  buffers (`x86_64_fs_exec_ring3.spl`), because `[u8]` element reads were garbage.
- The prod entry's own magic check prints `magic=248,3,0,0` (garbage) for a valid
  ELF `[u8]`, and the loader ignores it, parsing via mmio instead.

Fixing this is a compiler/runtime ABI task (make Simple x64 native-build pass heap
`RuntimeValue`/`[u8]` to/from the C runtime with the same representation the C
runtime uses), NOT a sshd change. It unblocks the entire x64 SSH protocol (version
→ KEX → packet → auth) at once, since all of it is `[u8]`-based.

## Impact

This is the gate for "hello world over SSH" on x86_64: the ring-3 FS-exec path and
the merged kernel (nvme+vmm+net+sshd, net survives vmm) are proven; SSH LOGIN must
work before an SSH command can drive `fs_exec_spawn_ring3`. Fixing the version
exchange (then verifying KEX/packet/auth for the same `[u8]`/take hazards) makes
x64 SSH login work; the remaining exec wiring is small (route the resolved path to
`fs_exec_spawn_ring3`).
