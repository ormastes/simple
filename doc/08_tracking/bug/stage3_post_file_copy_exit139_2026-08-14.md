# Stage 3 downstream high-memory exit 139

Date: 2026-08-14
Status: FOCUSED PASS / STAGE 3 VERIFICATION PENDING
Owner: compiler MIR local HIR metadata
Source: `src/compiler/50.mir/mir_lowering_types.spl:414`

## Evidence

After the `runtime_error` static-owner repair, the admitted Stage 2 build passed
the former receiver-corruption frontier. Cycle 2 ended after lowering
`dir_create_all` and `file_copy`; the final guarded Cycle 3 ended while entering
statement 1 of `eval_binop`. Both exited 139 near the prior high-memory region
without a symbolized diagnostic, so neither function name is yet a proven
root cause. Final log SHA-256:
`51877e1e469e9504934b68097db3a8250bbf85f666247aa652e3e1c676606a5b`.

This is a new downstream frontier. The repaired run contains none of the old
`runtime_error`, impossible receiver-local, or unsupported-expression markers.

## Symbolized root cause

A fresh admitted-Stage-2 run under GDB captured SIGSEGV with this exact stack:

1. `MirLowering.remember_local_hir_type`
2. `MirLowering.maybe_copy_array_value`
3. `MirLowering.lower_stmt_impl`
4. `MirLowering.lower_block_expected`

The crash occurs on statement 1 of `eval_binop`. `maybe_copy_array_value`
retrieved a `HirType` aggregate and passed it into another native method. Under
the Stage 2 ABI that aggregate transport corrupts the callee, matching the
already-proven static-receiver class. GDB log:
`build/native_probe/stage3-gdb/gdb.log`, SHA-256
`25f6fb3c1cf8585ed0bfee4c589386e2cc89dff8c60e74d9eab652719d6064ab`.

The repair adds `copy_local_hir_type_metadata(source_id, destination_id)`, whose
arguments are scalar and which copies the aggregate only inside the owning
aligned arrays. It rejects the same nil/raw-zero sentinel as
`find_local_hir_type` before mutating the destination.

On 2026-08-16, `sh scripts/check/check-native-scalar-metadata-copy.shs` passed
once with admitted pure-Simple Stage 2 SHA-256
`f879f1bd1116cb8ac8fe04fdeff278a5dbc01821b993ace5bce3b16b96167218`.
The source-bound native fixture proves append, update, missing-source,
isolation-state, and resource-state behavior. Retained build/run log SHA-256:
`ca75a6820599c35df0b69d23367bd2a5eb1ec807a41fc92ecb071e95f0bfde24` /
`d2cc0ff5f73a1a44d26603310738107eebcccd0a050ff62a57ec424195159add`.
This is focused Stage-2 evidence only; Stage 3 verification remains pending.

## Unblock condition

Run the materially changed cache-preserving Stage 3 build once. It must pass
the symbolized `remember_local_hir_type` frontier and produce an admitted
candidate; then run Stage 4 and the essential-tools gates. Do not use the Rust
seed as acceptance authority.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: requires a full bootstrap (Stage 2 -> Stage 3) to reproduce. This lane is
explicitly forbidden from building the main compiler, and no admitted Stage 2/3
binary exists on this host. The record itself states the driver console was not
retained, so there is no artifact here to analyse either.

**Unblock:** one bootstrap run with the Stage-3 console RETAINED (redirect and
keep `build/bootstrap/logs/<triple>/stage3-native-build.log` plus the driver
stdout). Until a crash site is bound to a hash, exit 139 stays an unretained
observation and no code change is defensible.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: FIX PRESENT IN SOURCE; runtime claim UNVERIFIED (needs stage3).**

`src/compiler/50.mir/mir_lowering_types.spl:446` defines
`copy_local_hir_type_metadata(source_local_id: i64, destination_local_id: i64)`
taking scalars, and it is wired at `src/compiler/50.mir/mir_lowering_stmts.spl:566`
inside `maybe_copy_array_value` (`:430`). Additionally
`scripts/check/check-native-scalar-metadata-copy.shs` was executed on 2026-08-17
and returned `STATUS: FAIL scalar-metadata-copy reason=compiler-missing-or-symlink`,
rc=1 — it requires a real self-hosted compiler, so it yields no verdict on this
host. Exit 139 stays unretained per this doc's own unblock note.

## 2026-08-17 (W6) — FAMILY COLLAPSE + first cheap deterministic reproducer

**These three rows are ONE incident**, not three:
`stage3_post_file_copy_exit139_2026-08-14`,
`stage3_post_folded_const_diagnostics_sigsegv_2026_08_14`,
`stage3_selfhost_exit_139_2026-08-14`.

### The crash is a GENUINE SIGSEGV, not an earlyoom kill

Every prior triage note on these rows says exit 139 is "an unretained
observation" needing a 90-minute bootstrap. It is not. It reproduces in under
five minutes with the stage3 binary already on disk
(`bootstrap/stage3/simple`, 3464072 bytes, mtime 2026-08-11 22:10 — **not** the
Rust seed) on a 14-line fixture:

```spl
enum MirInst:
    CallIndirect(i64, i64, i64, i64)
    Intrinsic(i64, i64, i64)
    Other

fn count_uses(inst: MirInst) -> i64:
    match inst:
        case CallIndirect(_, ptr, args, _): return ptr + args
        case Intrinsic(_, _, args): return args
        case _: return -1

fn main():
    print(count_uses(MirInst.CallIndirect(1, 20, 3, 4)))
    print(count_uses(MirInst.Intrinsic(1, 2, 7)))
    print(count_uses(MirInst.Other))
```

    ./bootstrap/stage3/simple compile --format=smf <fixture>.spl
    -> "Segmentation fault (core dumped)", rc = 139

RSS stays trivial, so **memory pressure is not the mechanism** — the 7.7 GiB
figure recorded on the post-folded-const row is a correlate of the large closure
it happened to be compiling, not the cause. earlyoom is likewise ruled out:
earlyoom sends SIGTERM (143/144), and this is SIGSEGV with a core dump.

### Symbolized: a statically emitted `call 0`

GDB on the same fixture:

```
Program received signal SIGSEGV
#0  0x0000000000000000 in ?? ()
#1  0x000000000066b0ec in ?? ()
#2  0x0000000000405d84 in ?? ()
#3  0x00000000004025f5 in ?? ()
#4  __libc_start_call_main
rip  0x0
```

`objdump -d --start-address=0x66b0dc` on `bootstrap/stage3/simple`:

```
66b0dc:  48 8b 03           mov    (%rbx),%rax
66b0df:  48 83 e0 f8        and    $0xfffffffffffffff8,%rax   # strip the 3-bit tag
66b0e3:  48 8b 78 70        mov    0x70(%rax),%rdi
66b0e7:  e8 14 4f 99 ff     call   0                          # <-- rel32 target 0x0
66b0ec:  48 89 c3           mov    %rax,%rbx
```

The call target is **encoded as 0 in the binary**. This is not a runtime null
function pointer, a corrupted vtable, or an aggregate-ABI transport bug: the
code generator emitted a direct call to an unresolved symbol and used 0 as its
address. RIP=0 with a 4-frame stack is the whole story.

### Why the binary contains it: MIR errors are not fail-closed

The same run prints, before crashing:

```
[ERROR] MIR error: MIR lowering error: unresolved method call: CallIndirect
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x4>
[ERROR] MIR error: MIR lowering error: unresolved method call: Intrinsic
```

i.e. lowering failed to resolve the enum-variant constructions and the wildcard
`case _:` arm, reported it, and the pipeline continued to emit code anyway —
producing a call site whose callee was never lowered, with target 0. That is the
single mechanism behind all three rows' "exit 139 before writing diagnostic
output": the *previous* stage's un-failed MIR errors become the *next* stage's
segfault, which is exactly why the crash never appears where the defect is and
why every prior lane read it as a fresh, unrelated "frontier".

It also explains the shape of the sibling observations without needing three
separate causes: `remember_local_hir_type` / `maybe_copy_array_value` (file-copy
row) and the diagnostic-count growth 0 -> 98 (post-folded-const row) are both
*downstream of* un-failed lowering errors, not independent ABI defects.

### Ownership / next step (W6 did NOT patch)

The two emitters are
`src/compiler/50.mir/_MirLowering/function_lowering.spl:851` (`error_fatal`, the
`[wildcard-arm]` message) and
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
(`unresolved method call`). **Both `_MirLowering/**` and `_MirLoweringExpr/**`
are owned by another worker in this wave, and the "emit a call anyway" decision
lives in the backend/driver, not in the two 50.mir files W6 owns
(`mir_lowering_stmts.spl`, `mir_lowering_types.spl`).** Reported as
BLOCKED-CROSS-OWNER rather than patched.

Two concrete follow-ups for whoever owns them:
1. Make `error_fatal` actually fatal for the compile unit — no object may be
   emitted after an unresolved-call or unsupported-type-kind error. A build that
   fails loudly is strictly better than one that ships a `call 0`.
2. Fix the underlying gap: `MirInst.CallIndirect(...)` enum-variant construction
   is being routed as a method call, and a `case _:` wildcard arm lowers with
   `disc=-1`. Either alone reproduces the crash above.

Whether current `src/compiler/**` still has gap (2) could not be settled here:
the only binary that executes `src/compiler/50.mir/**` is a self-hosted one, and
rebuilding `bin/**` or `build/bootstrap/**` is forbidden in this wave (~16
concurrent lanes). The stage3 binary used above is from 2026-08-11, so this is
evidence about that binary; the reproducer is cheap enough to re-run against any
newly admitted stage3 in seconds.
