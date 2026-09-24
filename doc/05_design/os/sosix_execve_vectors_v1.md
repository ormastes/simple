# SOSIX execve vector delivery V1

Date: 2026-09-14. Status: source implementation; runtime and guest evidence missing.
Requirement: REQ-SOSIX-EXECVE-VECTORS-001 (the unified SimpleOS compiler launch
path must preserve bounded argv/environment values through execve).

## Ownership and ABI

`sosix_process_execve` invokes `os.userlib.execve.user_execve` synchronously and
records only its returned errno/status in the request slot. The caller owns
its text arrays. `execve_plan_v1` copies validated bytes into a pointer-free
value plan; the userlib owner acquires one raw block, materializes byte data
and actual absolute pointer tables, invokes syscall 59 and releases the block
on every returning path. No raw address is published in an async request or
returned to the caller. A successful nonreturning exec discards the allocation
with the old address space. The kernel must copy both vectors before committing
the replacement image; `vmm_copyin_string_vector` already owns that step.

The five-argument syscall boundary remains:

| Field | Value |
|---|---|
| arg0 | address of copied path bytes |
| arg1 | path byte length, excluding NUL |
| arg2 | address of NUL-terminated u64 argv pointer table |
| arg3 | address of NUL-terminated u64 envp pointer table |
| arg4 | zero |

The packet contains argv slots, envp slots, path bytes plus NUL, argv strings
plus NUL, envp strings plus NUL, then padding to eight-byte alignment. Table
entries are patched only inside the raw allocation. Simple arrays may store
tagged values, so their `.ptr()` addresses cannot serve as C byte or pointer
arrays. The existing no-GC sync raw-memory owner supplies allocation, aligned
word stores and free; this slice introduces no new extern or C provider.
The current kernel representation uses little-endian u64 table slots, including
on its existing 32-bit compatibility call surfaces. New pointer widths or
byte orders require an explicitly versioned ABI.

## Bounds and error behavior

The source-contract spec pins userlib bounds to the current kernel constants.
The 64 argv/128 envp slot limits include the NULL terminator, so the maximum
payload counts are 63/127. A path has at most 256 bytes. Each argument or
environment string occupies at most 4096 bytes including NUL, and each vector
has a separate 32768-byte aggregate budget including all NULs. The current
kernel does not define a combined argv+envp budget; this owner preserves that
ABI rather than silently imposing another limit. Raw allocation is bounded by
67336 bytes including tables, a path and alignment.

Empty argv defaults to `[path]`. Explicit empty argv[0] returns `-EINVAL`;
other empty arguments and empty environment entries are preserved. Embedded
NUL and invalid UTF-8 return `-EINVAL`. Exceeded vector/string limits return
`-E2BIG`; path length returns `-ENAMETOOLONG`; allocation failure returns
`-ENOMEM`. Inputs are fully validated before acquiring raw storage or issuing
a syscall. Allocation extent overflow releases the allocation and returns
`-EFAULT`. Every ordinary returned kernel status is forwarded unchanged after
release. Text/array allocation failures follow the existing Simple runtime
allocation contract; this slice does not add recoverable array OOM semantics.

`vmm_copyin_cstr` formerly converted every byte into a separate codepoint,
corrupting UTF-8. Its terminal conversion now uses the shared strict, linear
UTF-8 decoder. Invalid copied bytes yield `EINVAL`; valid bytes become one
kernel-owned text without expansion. This does not validate hostile user
pointers by itself: existing VMM translation, read bounds and fault checks
remain responsible for those.

## Verification and residual boundaries

- Unit plan spec: fixed layout, caller-independent bytes, empty/default argv,
  UTF-8/NUL errors, exact count/string/path/aggregate limits.
- Kernel decoder unit spec: lossless multibyte input, empty input, malformed
  input with accurate consumed-byte counts; no MMIO or live-copy claim.
- System spec: host fixtures for invalid production-owner calls and value
  snapshots; source contracts for forwarding, ownership and kernel bound parity.
- Required physical follow-up: compile the actual owner against admitted raw
  allocation/write/syscall providers; fault-inject allocation and kernel errors;
  assert no outstanding raw block after a returned syscall. Boot an admitted
  guest and observe compiler argv/envp plus unchanged image on rejected exec.

No admitted pure-Simple test/docgen runtime is currently available. Authored
specs/manuals and structural checks are not execution evidence. Guest
qualification remains `MissingEvidence`. Packed SpawnBinary, the six-argument
ABI, fork child-return behavior and process-image commit/rollback are unchanged.
