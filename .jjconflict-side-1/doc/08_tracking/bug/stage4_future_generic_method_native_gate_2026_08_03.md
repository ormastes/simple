# Stage 4 Future generic-method native gate

Status: repair in progress; focused declaration containment passes
Severity: P1 bootstrap blocker
Owner: pure-Simple async Future compiled/interpreter boundary
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `69757e3aae7`

## Exact failure

The second full-resource x86 Stage 4 cycle crossed the repaired backend facade,
the EasyFix `i64` annotation, and the previously masked environment/codegen
imports. It reached HIR progress 608 and then failed while lowering
`lib.nogc_async_mut.async.future`:

```text
generic functions are not supported on the native build path yet:
fn 'map' declares type parameter(s); monomorphization is not implemented (#158 Phase B)
generic functions are not supported on the native build path yet:
fn 'then' declares type parameter(s); monomorphization is not implemented (#158 Phase B)
```

The cycle exited 1 after 50m32.31s at 33,580,496 KiB max RSS. No Stage 4
candidate exists, so exact-candidate sanity, essential-tools smoke, capsule
work, and every post-x86 platform row remain gated.

## Owner boundary

`Future<T>.map<U>` and `Future<T>.then<U>` require method-level native
monomorphization. The native HIR gate deliberately rejects that shape because
erasing `U` previously produced silent wrong results. Widening the compiler's
name-based erased-generic allowlist, weakening the gate, or replacing `U` with
`Any` would reintroduce that correctness defect.

Simple's conditional-compilation contract distinguishes `interpreter` from
`compiled`, so the bounded experiment kept the generic methods for the
interpreter, omitted them from compiled mode, and rewrote in-tree fluent
consumers to immediate poll/match semantics. That experiment was not sound:
the third focused native probe still accepted `future.map(...)`, linked an
executable, and silently produced the wrong result (build exit 0, executable
exit 1, no diagnostic). All production and test-source edits were therefore
restored. No weakened gate, conditional workaround, or consumer rewrite is
committed.

The adjacent `HostFuture<T>` generic-method/impl surface is not in this failed
entry closure and remains a separately visible future monomorphization lane; it
must not be used to broaden this repair without exact evidence.

## Required next repair and regression evidence

1. Implement real generic specialization, or make the native call path reject
   unsupported generic class/method calls before MIR/codegen. Declaration-only
   filtering is insufficient while unresolved calls still link silently.
2. Restore the positive ready/pending value fixture and require exit 30; retain
   a negative `map<U>` probe that must fail compilation with a diagnostic until
   specialization is complete.
3. Keep interpreter `map<U>`/`then<U>` tests green using an admitted pure-Simple
   binary. The attempted 25/25 run used a binary that self-identified as the
   Rust bootstrap seed and is rejected as verification evidence.
4. In a fresh bounded session, cross HIR 608 in the final full-resource x86
   Stage 4 cycle before any candidate is accepted.

## Retained evidence

- `build/bootstrap-stage4-x86-phase4/logs/stage4-fresh2.log`
- `build/bootstrap-stage4-x86-phase4/logs/stage4-fresh2-progress.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- `build/focused/stage4-nogc-async-future/`
- `doc/08_tracking/bug/native_generic_future_value_erasure_2026_08_03.md`

Focused evidence summary: attempt 1 built successfully but ready-value
execution exited 42; attempt 2's declaration-only fixture exited 30 but could
not prove call safety; attempt 3's unsupported `map` call incorrectly built and
then exited 1. The three-cycle cap is exhausted for this scoped session.

## 2026-08-03 fresh repair session

The compiled/interpreter containment is restored only after claiming and
repairing the separate bootstrap MIR diagnostic-drop defect. `map<U>` and
`then<U>` remain available to the interpreter and are omitted from compiled
closures. The eight buffered-I/O consumers and `Future.timeout` now spell out
the same immediate poll/match snapshot behavior without calling those generic
methods.

The positive declaration/import contract built with stub fallback disabled in
3.6 seconds at 156,928 KiB max RSS, then exited 30 with empty output. It also
executes a supported non-generic class method as a control. It deliberately
does not execute `Future<T>` because the separately claimed native generic
value-erasure defect remains open.

The retained Stage 3 compiler still embeds the pre-repair MIR lowering. As a
baseline, it accepted the new negative `Future.map` fixture (build exit 0) and
the resulting executable segfaulted (exit 139, empty output). The negative
build-rejection criterion therefore remains pending until the full Stage 4
rebuild produces a compiler containing the fatal diagnostic drain.

New retained evidence:

- `test/03_system/native/stage4_nogc_async_future_containment.spl`
- `scripts/check/cert/redeploy_gate/fixtures/stage4_native_future_map_rejected.spl`
- `build/focused/stage4-nogc-async-future/contract-new-attempt1.log`
- `build/focused/stage4-nogc-async-future/contract-new-run.log`
- `build/focused/stage4-nogc-async-future/map-rejected-attempt1.log`
- `build/focused/stage4-nogc-async-future/map-rejected-run.log`
