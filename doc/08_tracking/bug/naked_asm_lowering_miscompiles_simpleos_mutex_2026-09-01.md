# `@naked` is ignored by the cranelift freestanding backend — SimpleOS's critical-section provider is miscompiled

- **Date:** 2026-09-01
- **Severity:** HIGH — silent miscompile. Anything relying on `@naked` + `asm volatile`
  is compiled to code that jumps to an arbitrary address. There is no diagnostic.
- **Status:** OPEN
- **Found by:** the SimpleOS **dbfs** server round-trip lane
  (`scripts/check/check-simpleos-dbfs-server-roundtrip-ovmf.shs`), while trying to give
  DBFS's device commit owner an audited critical-section provider.

## Why this matters

`src/os/kernel/net/thread_shim.spl` is SimpleOS's critical-section provider. Its SOURCE
is good: `@export("C") spl_mutex_create/lock/try_lock/unlock/destroy` over a bounded
boot-lifetime arena word, a per-architecture acquire/release CAS, a lock word carrying
`cpu_id + 1` so a core that did not acquire cannot release, fail-stop on double unlock,
and a bounded spin budget. It is exactly the provider DBFS needs.

It does not survive codegen.

## Evidence

Built with the exact dbfs lane command (rust seed, `--backend cranelift`,
`--target x86_64-unknown-none`, `--entry-closure`), after adding
`use os.kernel.net.thread_shim.{}` to the entry so the real provider is in the closure
(`nm` confirms `spl_mutex_create` at `0x8031670` with a real body, not the 6-byte
freestanding stub).

**1. The `@naked` function gets a frame prologue anyway.** Each `asm volatile` body is
emitted as a separate `__simple_asm_H<hash>` thunk, and a prologue is prepended:

```
00000000080004e0 <__simple_asm_H9630faa93e1d40d9>:     # _mutex_word_cas, x86_64
 80004e0: 55                 pushq  %rbp               # <-- NOT in the source
 80004e1: 48 89 e5           movq   %rsp, %rbp         # <-- NOT in the source
 80004e4: 89 f0              movl   %esi, %eax
 80004e6: f0 0f b1 17        lock cmpxchgl %edx, (%rdi)
 80004ea: 0f 94 c0           sete   %al
 80004ed: 0f b6 c0           movzbl %al, %eax
 80004f0: c3                 retq                      # <-- pops the SAVED RBP
 80004f1: 5d                 popq   %rbp               # unreachable epilogue
 80004f2: c3                 retq
```

At entry `%rsp` points at the return address. `pushq %rbp` puts the caller's `%rbp`
on top of it, so the body's own `retq` pops **that** as the return address and jumps
to whatever the caller's frame pointer happened to be. The `lock cmpxchg` is correct
and does execute; control flow after it is not.

`_mutex_cpu_id`'s thunk (`__simple_asm_Hbd593c9b998b19fc`, `cpuid`-based APIC id) has
the identical defect.

**2. The caller cannot receive a return either.** The Simple-level wrapper is lowered
as an indirect call followed by an unconditional trap:

```
0000000008031473 <src__os__kernel__net__thread_shim___mutex_word_cas>:
 8031473: 55                 pushq  %rbp
 8031474: 48 89 e5           movq   %rsp, %rbp
 8031477: 48 be e0 04 ...    movabsq $0x80004e0, %rsi
 8031481: ff d6              callq  *%rsi
 8031483: 0f 0b              ud2                       # <-- trap on return
```

So even if the prologue were suppressed, a correctly-returning thunk lands on `ud2`.
**This is not a "drop the prologue" two-liner.** Naked semantics need the thunk emitted
with no prologue/epilogue AND the call lowered as a tail `jmp` (or a real call whose
return value is propagated and which is not marked unreachable).

## Consequence for DBFS / the dbfs gate

`check-simpleos-dbfs-server-roundtrip-ovmf.shs` stays **RED**, missing L5-L10, and the
root cause is now precise rather than inferred. Two independently sufficient blockers:

1. Without the `thread_shim` import, `--entry-closure` +
   `SIMPLE_ALLOW_FREESTANDING_STUBS=1` satisfies `spl_mutex_*` with stubs that are
   **actively deceptive**: `spl_mutex_create` returns **8** (a nonzero fake handle) and
   `spl_mutex_lock` returns **3** (truthy). A `handle > 0 and lock succeeded` readiness
   test is fooled by them.
2. With the import, the real provider is linked and immediately miscompiled per above,
   so the first `mutex_raw_lock` wild-jumps during module init — before any serial rung
   prints. That is strictly worse than a clean refusal, so the import is deliberately
   **not** taken (see the comment block in
   `examples/09_embedded/simple_os/arch/x86_64/dbfs_server_roundtrip_entry.spl`).

The mitigation landed for (1) is a **behavioural admission probe** in
`src/lib/nogc_sync_mut/db/dbfs_driver/device_commit_owner.spl`: a provider on a
non-allowlisted platform is admitted only after create / lock / unlock /
**double-unlock-must-FAIL** / relock / release. The double-unlock leg is what rejects a
constant-return stub. Pinned by
`test/01_unit/storage/dbfs/dbfs_critical_section_probe_spec.spl` (7/7). Allowlisted
hosts are never probed — double unlock on a pthread normal mutex is UB.

## Answer to "is the riscv64 mutex port audited or merely present?"

**x86_64: merely present, and miscompiled** — proven above. The `__simple_asm_*` thunk
mechanism is architecture-independent, so the riscv64 `lr.w.aq`/`sc.w.rl` and arm64
`ldaxr`/`stlxr` bodies in the same file are **suspect for the same reason**. Not
verified here (this lane does not own those targets); verify by disassembling a riscv64
freestanding kernel that links `thread_shim` and checking for a prologue before the
`lr.w.aq` and for `call`+trap at the wrapper.

## Fix sketch

In the seed's cranelift native backend:
1. Emit `__simple_asm_*` thunks for `@naked` functions with **no** prologue/epilogue.
2. Lower the wrapper as a tail `jmp` to the thunk (no `ud2`), or propagate the return.
3. Add a codegen regression test that disassembles a `@naked` fixture and asserts the
   first instruction is the asm body's first instruction and that no `ud2` follows the
   transfer. A source-level test cannot catch this — the source is already correct.

Until then, treat `@naked` as unsupported on this backend rather than silently broken.

## Ceiling of the DBFS lock, when it does work

One global `_DBFS_DEVICE_OWNER_MUTEX` serializes **every** device binding and every
durable/pending generation transition — a single coarse lock, not per-instance. Its
SimpleOS backing is a spin lock with a 65536-spin budget and no blocking or preemption,
correct only because bring-up is single-core and serialized. Upgrade path: fix the
naked lowering, then replace the spin lock with a scheduler-backed blocking lock when
SMP lands, then split the coarse lock per device instance.
