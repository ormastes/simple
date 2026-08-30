# Stage 3 HIR lowering errors block MC/DC/RT-HAL verification

Date: 2026-08-25
Status: open / release-blocking
Owner: compiler HIR import/materialization and nested-pattern lowering

## Impact

The MC/DC/RT-HAL hardening feature cannot yet run its self-hosted `check`,
`test`, SPipe, optimizer, or matched performance/RSS gates. AC-13, AC-15,
AC-16, and AC-18 therefore remain unproven; the feature must not be marked
complete.

## Evidence

After two compiler defects were repaired, a fresh Stage 2 completed native
build, passed the positional-entry frontend sanity probe, passed the independent
struct-receiver/runtime capability proof, and was admitted. The provenance-bound
one-thread Stage-3 continuation then loaded 992/992 module surfaces, completed
`export_origins`, entered `surface_freeze`, and terminated with SIGSEGV (139).

Measured immediately before failure:

- process: admitted Pure-Simple Stage 2 compiling Stage 3;
- phase: `surface_freeze` after 992 surface aliases;
- wall time: about 158 seconds;
- RSS: about 10,292,620 KiB;
- CPU: about one fully utilized recovery thread;
- log: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`;
- command receipt: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`.

GDB subsequently proved that `surface_freeze` was only the last progress marker,
not the crash owner. The fault occurred on entry to `HirLowering.error`, while
copying a malformed nested `Span` passed by `flatten_enum_match_arm` during HIR
lowering of `src/compiler/driver/driver.spl`. The transform now reports against
the stable enclosing match span instead of projecting `pat.span` through the
nested aggregate. This is a cold O(1) diagnostic-path change with no added
allocation or hot-path dispatch.

A fresh Stage 2 containing that fix passed native build, positional-entry
sanity, the struct receiver/runtime proof, and admission. The single admitted
Stage-3 continuation no longer segfaulted: it exited normally with structured
HIR diagnostics. The remaining blocker is now explicit: ambiguous callable
dependencies and unresolved types across the full compiler closure, plus six
unsupported nested enum-payload patterns in
`src/compiler/driver/driver_compile_vhdl_lowering.spl`. Evidence remains in
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

The next bounded audit isolated a second import-graph defect. A wildcard
candidate was allowed to chase the target module's private imports, so
`mir_instruction_kinds.*` invented a third route to its private
`mir_types.MirSignature` dependency. The retained ambiguity trace captured two
correct `mir_types::MirSignature` candidates and the false third spelling
`mir_types::compiler.mir.mir_types`. Candidate admission now requires a direct
declaration or a syntactically exported spelling before any re-export chase.

After that gate, Stage 2 again passed native build, compiler sanity, the struct
receiver/runtime proof, and admission. The final Stage-3 run eliminated the
original `Type`/`MirSignature` family and emitted no nested-pattern diagnostic.
It still failed HIR lowering: 2,956 ambiguity rows and 711 unresolved-type rows,
now concentrated in callable owners that depend on glob imports for signature
types (`_CBackendTranslate.class_core`, backend `env`, and split HIR owners).
Explicit owner imports for the dominant families were added after the mandatory
three-cycle cap and remain unverified. One profiling-enabled diagnostic run also
faulted nondeterministically in `flat_ast_to_module`; an otherwise identical
profiling-disabled run completed all 713 parses, so profiler/global-static
interaction remains a separate release risk.

## Cleared blockers in the same audit

1. Borrow checking referenced `unwind_payload_dest` and
   `unwind_type_tag_dest` from ordinary `Call` instructions. Those definitions
   now belong to `CallTerminator`, and Stage-2 native compilation passed.
2. `FrozenNativeModuleCapsuleBatchV1.find` was mis-lowered to `rt_string_find`,
   whose integer result was dereferenced as a capsule. A uniquely named free
   lookup now owns the cold O(n) batch scan; Stage-2 positional-entry sanity
   passed afterward.

## Unblock condition

Verify the explicit owner-import hardening in a fresh bounded session, then
resolve any residual callable-owner ambiguity and the profiler/global-static
interaction. Rebuild and admit Stage 2 and run one canonical Stage-3
continuation. The surface-freeze and nested-pattern failures are cleared; do
not re-investigate them unless new evidence points there.

## Reconfirmed 2026-08-27, and it now masks the 261/713 wall

With `dynamic.spl` reverted so Stage 2 builds (see
`sffi_out_param_capability_violation_blocks_stage2_2026-08-27.md`), the
resulting Stage-2 binary dies EARLIER than the previously recorded wall:

    [build] surface_freeze unknown/unknown step 1/6 +139641ms dt=621ms complete
    [ERROR] phase 2 FAILED (1 recorded error(s))
    Segmentation fault (core dumped)
    rc=139

**Zero** `ambiguous explicit callable dependency` errors and **no**
`[build] hir N/713` line at all — it never reaches HIR. For comparison, two legs
measured 2026-08-26 on an older tree both reached module **261/713** before
failing.

Consequence for anyone chasing the callable-dependency wall: it is currently
**unreachable**, so a restore of that fix cannot be measured end-to-end until
this phase-2 SEGV is fixed. The restore is content-verified only.

Note the log prints `1 recorded error(s)` without the error text, then
segfaults. The message is swallowed, which is its own defect — a phase that
records an error should print it before dying.

### Refined 2026-08-27 by a FAILED fix — the array itself is unreadable

gdb names the faulting frame exactly:

    Program received signal SIGSEGV
    #0  compiler__driver__driver_types__CompileContext_dot_error_message_at ()
    #1  compiler__driver__driver_orchestration__CompilerDriver_dot_compile ()
    #2  compiler.driver.driver.compiler_driver_run_compile ()
    rip 0xebe0d0 <...error_message_at+20>

**The compiler crashes while REPORTING an error**, which is why the log prints
`1 recorded error(s)` and dies without ever naming it. The underlying phase-2
error has still never been seen.

`error_message_at` is bounds-checked and looks correct:

    fn error_message_at(index: i64) -> text:
        if index < 0 or index >= self.errors.len():
            return ""
        self.errors[index]

**Hypothesis tried and REFUTED:** that the loop in `driver_orchestration.spl:136`
bounds on the scalar `self.ctx.error_count_value` while `error_message_at`
bounds on `self.errors.len()`, so a desync (count=1, array empty) walked past
the end. Fix applied: bound the walk by `self.ctx.errors.len()` and log when the
two disagree.

Result: **no change.** `Build complete: 770 compiled, 0 cached, 0 failed`, the
new diagnostic string is present in the binary (`strings | grep -c
'error-list desync'` = 1), and the run still ends `rc=139` — **with the new
diagnostic line never printed.**

That is the discriminating detail. The diagnostic executes BEFORE the loop and
evaluates `self.ctx.errors.len()`. It never printed, so **`self.errors.len()`
is itself the faulting read**. The array is not short or desynced — the field is
unreadable at that point.

**So the defect is one level down:** `CompileContext.errors` is corrupt or nil
when phase 2 reports. A bounds fix cannot help, and neither can any change
inside `error_message_at`. The next step is to find where the `CompileContext`
that phase 2 reports through loses its `errors` field — the stale-snapshot /
value-semantics class this record already names, not an indexing bug.

The failed fix is deliberately NOT landed: it changes no behaviour and would
imply the desync theory is live.
