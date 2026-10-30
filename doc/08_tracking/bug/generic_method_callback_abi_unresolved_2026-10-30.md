# Generic method callback ABI kept declaration binders

## Symptom

Native lowering rejected callbacks passed to generic instance methods such as
`Future<T>.then<U>(fn(T) -> Future<U>)`. The declaration-owned function slot
still contained `T` and `U` when MIR selected the lambda ABI, so the closed-ABI
guard correctly refused to lower it. The failure appeared in
`src/lib/nogc_async_mut/io/buffer.spl` at chained `Future.then` calls.

The native baseline reproduced the failure with
`test/fixtures/native_generic_callback_abi/main.spl`. The frozen build log is
`/tmp/simple-generic-callback-baseline-20261030/build/generic-callback-baseline/build.log`
(exit 1, peak 1.74 GiB, `mono generic_fns=1`, `call_sites=0`,
`specializations=0`, `unresolved=0`). The fixture SHA-256 is
`b3c555b15369f3efcb680ea4571fd3ef5a81485e3c3fb867da077188908380e0`.

## Cause

The first repair covered generic `HirImpl.methods`, but the failing source uses
class-body methods represented directly in `HirClass.methods`. The mono
collector enumerated only `module.impls`, so it never registered
`HostFuture::then`; the attempt's `call_sites=0` confirms no method rewrite
was reached. Direct class lowering also typed implicit `self` as
`Named(HostFuture, [])`, dropping the class-owned `T`, so the existing
owner-prefix proof could not match the receiver declaration to its leading
template binder even if the method had been registered.

## Repair

Direct class methods now receive a `self` type containing their exact owner
type-parameter names, and class-owned and explicit/synthetic impl methods share
the same exact-symbol registration path. The mono pass specializes inherent
methods with receiver-owned binders first and unique, non-shadowing method
binders afterward. It infers callback inputs and result from concrete
arguments, expected results, and a checked callback body in an isolated
environment. Imported nominal types cross the declaration and caller scopes
through the existing relocation path. The rewritten method call is an
ordinary direct call carrying its transported specialization signature;
unresolved or conflicting evidence remains a hard mono refusal.

The MIR lambda ABI guard remains fail-closed. Regression coverage is in
`test/01_unit/compiler/mono/generic_method_callback_specialization_spec.spl`.

## Verification status

The old-producer native baseline confirms the failure reproduction only. The
first bounded source-import driver build parsed all 542 modules and HIR-lowered
181 with zero HIR failures. It completed seven
`monomorphize_integration` modules with no source errors, then hit its 240
second timeout before the driver algorithm ran (peak 4.46 GiB). A second
240-second attempt HIR-lowered 229 modules and timed out before driver
execution (peak 4.94 GiB). The 900-second attempt parsed and HIR-lowered all
542 modules and completed mono for all of them (`generic_fns=102`,
`call_sites=1367`, `specializations=678`, `unresolved=0`), but reached the
8-GiB RSS cap during MIR lowering (peak 8,399,280 KiB). The driver algorithm
did not execute. A reduced 442-module no-MIR driver then HIR-lowered all 442
modules and completed mono with 412 specializations and zero unresolved calls,
but also reached the 8-GiB RSS cap before executing the driver. The repair
source and assertions remain unverified. Native fixtures now include a
distinct-binder runtime case (`distinct.spl`) and a conflicting-result
compile-negative case (`conflicting_result.spl`); neither has been run.

The freshly built compiler `908d23f9` reproduced the original failure against
the frozen first-repair source blob `f5d86dc566671538f2d6423951b6d9508e8f6fb9`.
Its native build log is
`/tmp/simple-phase3-campaign-20261030-plan/probe-execution/attempt2/result-build.log`:
`generic_fns=1`, `call_sites=0`, `specializations=0`, `unresolved=0`, followed
by the unresolved lambda ABI diagnostic. This is the direct-class registration
gap described above. The current direct-class registration and receiver-type
fix are new construction input and have not been built or executed.

The next verification attempt must use the freshly qualified pure-Simple
stage-2 compiler for the focused source-import drivers and native fixture
matrix: no-MIR parser/HIR/mono assertions, MIR ABI assertions, both positive
native fixtures, the reachable conflicting-result compile-negative fixture,
and the original native reproduction. Run the SSpec when a qualified runner
with a test command is available; the admitted compiler CLI does not provide
one. Until the available driver and native checks run, this note does not
claim a regression pass.
