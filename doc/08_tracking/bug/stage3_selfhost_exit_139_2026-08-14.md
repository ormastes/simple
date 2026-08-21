# Stage 3 self-host exits 139 after fresh Stage 2

Date: 2026-08-14
Status: OPEN
Owner: compiler bootstrap
Source authority: `f26936914d9833a000044757f6475bc7fd6e62cb`
Internal final reviewer: `/root/higher_model_review` (`gpt-5.6-sol`, 2026-08-14)

## Failure

The third and final bounded bootstrap cycle built Stage 2 and passed its sanity
gate. The fresh pure-Simple Stage 2 compiler then segfaulted while compiling
Stage 3. `stage3-native-build` was observed exiting 139 before writing
diagnostic output. The driver console containing that exit was not retained;
the progress log ends at an alive Stage-3 sample. Therefore exit 139 is an
unretained observation pending the next diagnostic reproduction, not a
hash-bound receipt.

This record is distinct from
`stage3_selfhost_post_hir_segfault_2026-08-14.md`. That restart12 lane retained
a nonempty `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
and narrowed only the last observable frontier to MIR method-call lowering.
The two runs used different source authorities, output directories, candidate
hashes, and evidence retention. Neither log proves a crash site, and evidence
from one run must not be attributed to the other.

Command:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --full-cli \
  --no-mcp --diagnostics=test \
  --diagnostic-child-compiler=/mnt/data/worktrees/restart12-infra/build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple \
  --output=build/restart12-bootstrap --jobs=full \
  --progress=build/restart12-bootstrap/progress-resume.log
```

Retained inputs/evidence:

- Stage 2: `build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
- Stage 2 SHA-256: `7617c924d6848928f3f7495e3d6691d908505fb677d19b9f07f9697ebf9aaec5`
- Progress log: `build/restart12-bootstrap/progress-cycle3.log`
- Progress SHA-256: `d59a1256be2afbe50476919803aca20993ca58e45e7e7a98ee3edd1e07707322`
- Empty child log: `build/restart12-bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`

## Unblock condition

In a fresh session, run the exact command above while retaining driver
stdout/stderr and exit status, obtain a symbolized
owner-path backtrace or the smallest pure-Simple reproducer, fix the
compiler/codegen owner, and complete Stage 3 plus Stage 4 and the bounded
essential-tools smoke gate. Do not use the Rust seed, stale release binary, or
Stage 2 as SPipe/release evidence. The prior session exhausted its three-cycle
cap and must not rerun unchanged commands.

Before another full bootstrap, an independently admitted pure-Simple candidate
may run the bounded exact/adjacent diagnostic with:

```sh
SIMPLE_ADMITTED_COMPILER_SHA256=<admitted-sha256> \
  SIMPLE_ADMITTED_RUNTIME_PATH=/absolute/path/to/admitted/runtime \
  sh scripts/check/check-stage3-aggregate-receiver-native.shs \
  /absolute/path/to/admitted/pure-simple/compiler
```

The restart12 focused lane exhausted three distinct checker cycles. The final
corrected invocation retained
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-13f1b7e0ed21a031/result.env`
with `build_rc=139`, `run_rc=125`, an unchanged candidate hash, no output, and
only an unsymbolized timeout/core-dump message. This independently confirms the
small exact aggregate-receiver fixture triggers the failure class, but does
not localize or repair it and does not admit Stage 3 or Stage 4. Do not rerun
that command unchanged; the next lane must capture a symbolized backtrace or
otherwise distinguish HIR receiver corruption from MIR writeback/resolution.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: identical blocker to `stage3_post_file_copy_exit139_2026-08-14.md`: needs a full
bootstrap plus retained Stage-3 diagnostics. The record already says so itself
("an unretained observation pending the next diagnostic reproduction, not a
hash-bound receipt"), and explicitly warns that evidence from the sibling
restart12 lane must NOT be attributed to this one. No speculative fix attempted:
with no crash site and no retained log, any patch would be a guess dressed as a
fix.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

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

### Addendum (W6, same session): the call-to-zero sites are not a one-off

    objdump -d bootstrap/stage3/simple | grep -cE '\scall\s+0 <'   -> 169
    objdump -d bootstrap/stage2/simple | grep -cE '\scall\s+0 <'   -> 169

169 statically encoded calls to address 0 in each shipped self-hosted binary.
The one symbolized above (`0x66b0e7`) is merely the one this fixture reaches
first. A cheap, non-executing gate is therefore available today and should be
added to the bootstrap admission checks: **a stage binary containing any
`call 0` site must not be admitted.** That single grep would have failed every
one of these three rows' builds at the point the defect was introduced, instead
of surfacing days later as an unattributable exit 139.

---

## Concurrent variant landed on origin/main (merged 2026-08-17, both sides kept)

Neither side was a superset of the other, so this appendix preserves the
origin/main text verbatim rather than dropping evidence. Owning lane should
reconcile the two halves.

# Stage 3 self-host exits 139 after fresh Stage 2

Date: 2026-08-14
Status: OPEN
Owner: compiler bootstrap
Source authority: `f26936914d9833a000044757f6475bc7fd6e62cb`
Internal final reviewer: `/root/higher_model_review` (`gpt-5.6-sol`, 2026-08-14)

## Failure

The third and final bounded bootstrap cycle built Stage 2 and passed its sanity
gate. The fresh pure-Simple Stage 2 compiler then segfaulted while compiling
Stage 3. `stage3-native-build` was observed exiting 139 before writing
diagnostic output. The driver console containing that exit was not retained;
the progress log ends at an alive Stage-3 sample. Therefore exit 139 is an
unretained observation pending the next diagnostic reproduction, not a
hash-bound receipt.

This record is distinct from
`stage3_selfhost_post_hir_segfault_2026-08-14.md`. That restart12 lane retained
a nonempty `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
and narrowed only the last observable frontier to MIR method-call lowering.
The two runs used different source authorities, output directories, candidate
hashes, and evidence retention. Neither log proves a crash site, and evidence
from one run must not be attributed to the other.

Command:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --full-cli \
  --no-mcp --diagnostics=test \
  --diagnostic-child-compiler=/mnt/data/worktrees/restart12-infra/build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple \
  --output=build/restart12-bootstrap --jobs=full \
  --progress=build/restart12-bootstrap/progress-resume.log
```

Retained inputs/evidence:

- Stage 2: `build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
- Stage 2 SHA-256: `7617c924d6848928f3f7495e3d6691d908505fb677d19b9f07f9697ebf9aaec5`
- Progress log: `build/restart12-bootstrap/progress-cycle3.log`
- Progress SHA-256: `d59a1256be2afbe50476919803aca20993ca58e45e7e7a98ee3edd1e07707322`
- Empty child log: `build/restart12-bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`

## Unblock condition

In a fresh session, run the exact command above while retaining driver
stdout/stderr and exit status, obtain a symbolized
owner-path backtrace or the smallest pure-Simple reproducer, fix the
compiler/codegen owner, and complete Stage 3 plus Stage 4 and the bounded
essential-tools smoke gate. Do not use the Rust seed, stale release binary, or
Stage 2 as SPipe/release evidence. The prior session exhausted its three-cycle
cap and must not rerun unchanged commands.

Before another full bootstrap, an independently admitted pure-Simple candidate
may run the bounded exact/adjacent diagnostic with:

```sh
SIMPLE_ADMITTED_COMPILER_SHA256=<admitted-sha256> \
  SIMPLE_ADMITTED_RUNTIME_PATH=/absolute/path/to/admitted/runtime \
  SIMPLE_ADMITTED_RUNTIME_RECEIPT=/absolute/path/to/runtime-admission.env \
  SIMPLE_ADMITTED_RUNTIME_RECEIPT_SHA256=<runtime-receipt-sha256> \
  sh scripts/check/check-stage3-aggregate-receiver-native.shs \
  /absolute/path/to/admitted/pure-simple/compiler
```

The restart12 focused lane exhausted three distinct checker cycles. The final
corrected invocation retained
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-13f1b7e0ed21a031/result.env`
with `build_rc=139`, `run_rc=125`, an unchanged candidate hash, no output, and
only an unsymbolized timeout/core-dump message. This independently confirms the
small exact aggregate-receiver fixture triggers the failure class, but does
not localize or repair it and does not admit Stage 3 or Stage 4. Do not rerun
that command unchanged; the next lane must capture a symbolized backtrace or
otherwise distinguish HIR receiver corruption from MIR writeback/resolution.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: identical blocker to `stage3_post_file_copy_exit139_2026-08-14.md`: needs a full
bootstrap plus retained Stage-3 diagnostics. The record already says so itself
("an unretained observation pending the next diagnostic reproduction, not a
hash-bound receipt"), and explicitly warns that evidence from the sibling
restart12 lane must NOT be attributed to this one. No speculative fix attempted:
with no crash site and no retained log, any patch would be a guess dressed as a
fix.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## Current-source and authority audit 2026-08-17

Audited local `71aedd12c3` and latest `origin/main` `df2e577a89`; the intervening
commits recover Target IR and Intel cmdstream coverage and do not alter this
bootstrap failure lane. No retained row-11 Stage-2 binary, admitted compiler,
runtime authority directory, or hash-bound runtime receipt exists in this
worktree. The historical `/mnt/data/worktrees/restart12-infra/...` path is not
available here. Consequently neither the exact native aggregate-receiver gate
nor a bounded admitted Stage-3 resume can honestly start.

The current compiler contains the separately symbolized sibling repair:
`maybe_copy_array_value` passes scalar local IDs to
`copy_local_hir_type_metadata`, which copies `HirType`, isolation, and resource
state only inside the owning aligned arrays and rejects missing/nil/raw-zero
sources before mutation. Its exact/adjacent fixture covers append, update,
missing source, and both state arrays. That evidence is consistent with this
failure family but is not promoted into a root-cause claim for row 11, whose
original exit 139 remains unretained.

The focused gate was syntax-checked and invoked once against an explicitly
missing candidate. It exited 2 with
`error=candidate_not_executable:.../build/missing-admitted-stage2`, proving it
fails before any Rust seed or unadmitted compiler can become evidence. The
unblock example above was corrected to include the two runtime-receipt
variables the gate actually requires.

**Exact remaining admission blocker:** supply one executable pure-Simple
compiler plus its expected SHA-256, an immutable runtime authority directory,
and a hash-bound runtime admission receipt plus receipt SHA-256. Run the
five-probe gate once; only if all five rows pass may the materially changed,
cache-preserving Stage-3 resume run once with retained driver console and
symbolized crash output. Until then status remains OPEN / ADMISSION BLOCKED;
there is no further evidence-backed source correction in this row.

## 2026-08-22 macOS arm64 retained reproduction

Current-source Phase 2 admitted on macOS arm64 with the SDK-aware Clang
23.1.0-rc3 shim.  The admitted candidate SHA-256 was
`48d7fe033386893f03a0d95a1f003bca38360bd75dc17900b41daf8db078a976`
from source authority `db6ec6e4594c470fa9589cefa02aebb5daae691f` plus the
uncommitted imported-composite wildcard dependency lane.  Stage 3 parsed and
retained all 665 physical / 957 logical surfaces, then died at HIR entry with
`EXC_BAD_ACCESS`, `SIGSEGV`, and `KERN_INVALID_ADDRESS at 0x0`.

The retained macOS reports are:

- `simple-2026-08-22-021119.ips`: fault in
  `CompilerDriver.lower_and_check_streaming_surfaces_impl+308`, loading through
  a null `streaming_module_surfaces_owner` while the ready scalar was true.
- `simple-2026-08-22-022447.ips`: a stable-owner experiment moved the fault to
  `ModuleSurfacesByName.adopt_from+4`, proving the driver field was already null
  before the final owner commit.
- `simple-2026-08-22-023122.ips`: routing through the in-place
  `CompileContext.module_surfaces` optional still faulted at
  `lower_and_check_streaming_surfaces_impl+360`.

Both owner-routing experiments were disproved and removed.  No speculative
fix was committed.  The session's three Stage-3 repair cycles are exhausted;
the next lane must fix the native class/optional reference-field store or its
underlying aggregate layout with a smaller arm64 reproducer before another
full bootstrap.
