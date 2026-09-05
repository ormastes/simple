# Stage 3 exits 139 after post-folded-constant diagnostics

- **Bug ID:** `stage3_post_folded_const_diagnostics_sigsegv_2026_08_14`
- **Status:** OPEN
- **Severity:** P0 bootstrap blocker
- **Date:** 2026-08-14

## Preserved System evidence

Clean detached worktree `/tmp/simple-stage4-mir-0e900` is pinned to
`0e90035ad3a`. An admitted Stage-2 compiler and runtime from the read-only
qemu-matrix lane compiled current `src/app/cli/bootstrap_main.spl` with LLVM,
one thread, `core-c-bootstrap`, `dynload`, and
`SIMPLE_NO_STUB_FALLBACK=1`, using isolated output/cache paths.

The run remained CPU-active for roughly seven minutes, peaked near 7.7 GiB
RSS, emitted no object, and terminated with exit 139. Its final output was:

```text
[bootstrap-error-count] source_idx=0 point=entry count=0
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=9
[bootstrap-error-count] source_idx=1 point=entry count=9
[bootstrap-error-count] source_idx=1 point=post-lowering count=9
[bootstrap-error-count] source_idx=1 point=post-diagnostics count=95
[bootstrap-error-count] source_idx=2 point=entry count=95
[bootstrap-error-count] source_idx=2 point=post-lowering count=95
[bootstrap-error-count] source_idx=2 point=post-diagnostics count=98
[hir-field-type] struct=CompiledUnit field=entry_point actual=2589120870
[hir-field-type] struct=BackendError field=span actual=2589120870
```

The `actual=2589120870` rows are known benign Optional-variant probes and are
not a root-cause claim. The important boundary is diagnostic growth from zero
to 98 across the first three sources followed by SIGSEGV before object output.

The folded-module-constant diagnostic is absent, proving the preceding MIR
category crossed its failure frontier. This new category must preserve the
exact System evidence, reproduce at the smallest owning Integration boundary,
then add same-mechanism System/Integration/Unit scenarios with 100% branch
coverage for the changed unit owner before a fix is accepted.

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
