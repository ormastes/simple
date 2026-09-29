# Stage 3 dies at `hir 0/717`: `rt_mem_snapshot_open` receives `len=0` from the seed-compiled stage2

- **Date:** 2026-08-28
- **Component:** extern `text` ABI tables (Rust seed `text_arg_indices`, pure-Simple `src/compiler/50.mir/text_extern_abi.spl`)
- **Severity:** high (phase-3 blocker whenever `SIMPLE_MEM_SNAPSHOT_FILE` / `SIMPLE_COMPILER_PHASE_PROFILE_FILE` is set, which the bootstrap stage-3 lane always does)
- **Status:** pure-Simple twin FIXED in this change (`text_extern_abi.spl`: `rt_mem_snapshot_open` -> `[0]`, `rt_mem_snapshot_record` -> `[2, 3, 5]`); Rust seed twin OPEN (out of this lane's edit scope)

## Evidence

`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log` ends with
`hir unknown/unknown step 2/6 +220265ms failed` and
`error: in-process native-build: SIMPLE_MEM_SNAPSHOT_FILE could not be established safely`,
and no `memory-snapshot-v1.events` / `phase-profile-v1.events` file exists in the provenance dir.

Reproduced path-independently with a three-line hello world and
`SIMPLE_MEM_SNAPSHOT_FILE=<scratch>/mem.events` (same error, rc=1, no file).
`strace -f -e openat,open,write` shows **no** `open`/`openat` between the
`hir 0/1 pending` write and the failure — the runtime rejects the argument
before any syscall. Disassembly of the stage2 binary at
`compiler__driver__driver_mem_snapshot__mem_snapshot_begin`:

```
aea15b: mov %rbx,%rdi        ; boxed text word
aea15e: xor %esi,%esi        ; path_len = 0
aea160: call rt_mem_snapshot_open
```

`rt_mem_snapshot_open(const char*, int64_t)` returns -1 on `path_len <= 0`.
Neither `text_arg_indices` twin listed the `rt_mem_snapshot_*` family, so the
`text` argument was passed as a single collapsed word instead of the
`(ptr, len)` pair (`doc/08_tracking/bug/pure_simple_text_extern_abi_audit_2026-07-30.md`).
`SIMPLE_COMPILER_PHASE_PROFILE_FILE` (`driver_log_helpers.spl:_append_phase_profile`)
uses the same open and was silently empty for the same reason.

## What remains

Stage2 is compiled by the Rust seed, so the seed's
`src/compiler_rust/compiler/src/codegen/instr/calls.rs:text_arg_indices` must
carry the same two rows (kept in lockstep by hand per the table's header) for
the *stage2* binary to stop failing. Verified after a seed rebuild of stage2
from this tree: the rebuilt binary still fails the same way (the seed twin is
what governs stage2's own call sites). The pure-Simple row fixes stage3 and
later, i.e. any compiler compiled by a pure-Simple compiler.
