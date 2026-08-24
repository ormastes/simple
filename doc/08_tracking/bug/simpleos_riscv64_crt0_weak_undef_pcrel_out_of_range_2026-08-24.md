# riscv64-unknown-simpleos: crt0's weak-undefined symbol probes cannot be formed PC-relatively (2026-08-24)

- Status: OPEN (blocks riscv64 only; aarch64 is GREEN)
- Found in `/mnt/data/worktrees/goal-lane-f-simpleos-link` at `6a1d98f9c10`.
- Successor to
  `simpleos_target_build_link_omits_simple_core_archive_2026-08-24.md`. That bug
  is FIXED; riscv64 now resolves **every** symbol and fails one step later, here.

## Symptom

```
$ sh scripts/ci/build-simpleos-toolchain.shs --only riscv64      # rc=1
Build failed: link failed: ld.lld: error:
  build/os/sysroot-riscv64/lib/crt0.o:(function _start: .text+0x9c):
  relocation R_RISCV_PCREL_HI20 out of range: -1048576 is not in [-524288, 524287];
  references '__simple_startup_before_main'
```

Undefined-symbol count at this point is **0** (`grep -c "undefined symbol:"` on
the build log). This is purely a relocation-range failure, not a missing symbol.

## Mechanism

`scripts/os/simpleos-sysroot-riscv64.shs` generates a crt0 that probes several
optional runtime hooks with the standard weak-symbol idiom — take the address,
branch if it is null:

```asm
    la t0, __simple_startup_before_main
    beqz t0, .Lstartup_before_main_done
    ...
.weak __simple_startup_before_main
```

The same shape is used for `rt_set_args` and `__simple_call_module_inits`.

`la` on riscv64 expands to `auipc`+`addi` (`R_RISCV_PCREL_HI20`/`LO12`), i.e. a
**PC-relative** address. The weak symbol is undefined, so lld resolves it to
absolute address 0, and a PC-relative form cannot express "address 0" from a
`.text` placed at the SimpleOS user base. The idiom only works when the address
can be materialised **absolutely**.

aarch64 is not affected in practice: its `adrp`+`add` has a +-4GiB reach, so the
same idiom happens to stay in range. That asymmetry is why aarch64 went green
with the link-line fix and riscv64 did not.

## Ruled out by measurement

- Not a missing symbol: 0 undefined at failure.
- Not the code model, and not linker relaxation. `-mcmodel=medany -mno-relax`
  was added to all three riscv64 `.S` assembly steps (crt0, syscall, setjmp) --
  the crt0 was indeed the only riscv64 object built WITHOUT the `-mcmodel=medany`
  that `CFLAGS`/`RT_CFLAGS` pass to every other object, so this looked promising --
  and the error is **byte-identical** afterwards. That change was therefore
  reverted rather than left in as an unevidenced codegen change.
- Not the softfloat addition: `__extenddftf2` is defined and resolves; the log's
  previous complaint about it is gone.

## Fix direction (not yet implemented)

The weak-undef probe needs an absolute materialisation rather than a PC-relative
one. Candidates, cheapest first:

1. Assemble the probes under `.option push` / `.option norelax` with an explicit
   `lui`/`addi` absolute sequence for the weak symbols only (crt0 already uses
   exactly this `.option` bracket for `__global_pointer$`).
2. Give the weak hooks real no-op default definitions in the SimpleOS libc, so
   they are never undefined and `la` always has an in-range target. This also
   removes the null-probe branches entirely and is the most robust option, but
   changes crt0 semantics and should be reviewed against the aarch64/x86_64
   crt0s so the three stay consistent.

Option 2 is likely correct long-term: the null-address probe idiom is fragile on
any target whose only address form is PC-relative.

## Scope note

This is riscv64-only. `aarch64-unknown-simpleos` builds, links and installs:

```
aarch64-unknown-simpleos: OK bin/release/aarch64-unknown-simpleos/simple
  (4393120 bytes, first PT_LOAD 0x0000000050000000)
RESULT: PASS
```
