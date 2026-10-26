# Concrete Future return context leaves T unsubstituted at native MIR

Status: OPEN. Explicit-static-receiver workaround FAILED native verification.
Real Future constructor control cleared focused MIR and passed conditional manual strict link/run. Canonical native compilation remains FAILED; production-owner qualification remains incomplete.
Canonical ID: `native_future_receiver_typeparam_2026_10_18`.
Authoritative bug DB reconciliation is pending a qualified full CLI.

## Actual authority evidence

Canonical authority attempt 2 used source
`97d8cb355ed527ee0a50c440022500c37f026726` and genuine producer SHA-256
`3c6eafef89dcae8f22db2ff5b4ea831cda494fe19b0dd847f186792f019a2951`
(SPL lineage `f04888bdb33f71acc0cd97c38b412b065edc1fe4`). The raw worker log
`C:/dev/p4i3b/authority-images/tmp/native-build-stderr-28228-2.log` contains:

- MIR terminal: 232 modules, 230 successful, two failed, elapsed 785639 ms.
- `lib.nogc_async_mut.async.cancellation`, module index 172, at +710541 ms:
  error index 170, `E-MIR-TYPE-TypeParam: unsubstituted generic type parameter
  'T' reached MIR lowering`.
- `lib.common.io.read_only_file_view`: five instances of the same diagnostic,
  error indices 172, 174, 175, 176 and 177. The paired owner repair is recorded below.

That owner has one `Future.from_value` in `read_async`, carrying
`Result<FileViewSliceV1, ReadOnlyFileViewErrorV1>`, and four in `prefetch`,
carrying `Result<(), ReadOnlyFileViewErrorV1>`. The separate candidate binds
each existing Result value explicitly and specializes the matching Future
receiver. No result branch or error payload is replaced. Coinciding call/error
counts support this probe scope but do not prove per-call diagnostic mapping.

This is actual module attribution, not attribution inferred from the number
of generic calls. No function/span is present in the emitted diagnostic.

## Rejected explicit-static cancellation source candidate

The original `CancellationToken.guard_future() -> Future<bool>` used
`Future.from_value(true)` and `Future.pending<bool>()`. `from_value` and
`pending` are static methods of `class Future<T>`; `pending` has no independent
method type parameter. The rejected first candidate explicitly specialized the class
receiver: `Future<bool>.from_value(true)` and `Future<bool>.pending()`.
Existing integration specs use the same receiver syntax for `Future<i64>`.

That candidate failed the native control below. It does not establish receiver binding as
the proven compiler root cause. The compiler investigation covers generic
receiver/static-call transport and specialization before MIR. Preserve implicit
inference for the valid `from_value(true)` form; do not require source authors
to spell every inferred type merely to hide an unsubstituted compiler type.
The method-type-argument spelling also needs a precise diagnostic if it is
unsupported, rather than allowing an internal T into MIR.

No generic `Future`/`Poll` declaration, cancellation registry, return type or
control flow changes. A guard remains a poll-once snapshot: Pending before
cancellation, Ready(true) after own or ancestor cancellation; a previously
returned Pending future remains Pending.

Intended-code recovery reference:
`97d8cb355ed527ee0a50c440022500c37f026726`.
Rejected static-receiver candidate source: `b1680b028c7f5b5e2c96b0910f05ec1403cb8b99`.
The constructor repair has focused conditional semantic evidence, but is not fully native-qualified.

## Focused qualification

`test/fixtures/compiler/cancellation_future_receiver/main.spl` imports the
actual production cancellation owner. Native compile/link/run must return 0
and exactly `cancellation-future-receiver-pass`. Nonzero exits distinguish
missing Pending, missing/false Ready payloads, snapshot mutation and unrelated
root contamination. The fixture includes grandchild propagation with an
intervening unrelated allocation, preserving the prior registry regressions.

At initial preparation the fixture was UNRUN; its final admission failure is recorded below. No compiler rebuild, fourth CharLit probe or authority
retry is authorized by this patch. A resource-reviewed focused compile is
required before treating the workaround as native evidence, followed by a
source-changed authority build to qualify the actual owner closure. Existing
full compiler/core/MCP suites remain pending a qualified full CLI.

## Cycle 1 negative evidence and cycle 2 candidate

The shared real-Future/Poll pair at source
`b1680b028c7f5b5e2c96b0910f05ec1403cb8b99` used the original `3c6eafef...`
producer above. Both baseline and explicit-static-receiver control compiled
with exit 1 and emitted zero objects. Each reached MIR 52/52, 51 successful,
one failed, with six unsubstituted T diagnostics; internal elapsed times were
50586 and 49639 ms respectively. The explicit receiver spelling therefore
does not qualify as a workaround. Both actual production-owner fixtures were
UNRUN because the launcher stopped after the failed control.

Evidence: `C:/dev/p4future1/{baseline,explicit_receiver}/result.env` and
compile logs. Guard `C:/dev/p4future1/guard.env`, SHA-256
`521cc7e0db70391bbbc69c9c0a2bed7c802da3b1855d89a50de5da29b9c65f4c`,
is complete, exit 1, quiescent, enforced at 8 GiB, helper-integrity verified,
root 36212/session 10152, peak 1515556 KiB. This is negative native evidence,
not a passing source or compiler fix.

Cycle 2 preserves both failed fixtures and reuses their receipts without
rerunning them. The changed `read_only_future/typed_constructor.spl` fixture
and both production owners construct the existing public `Future<T>` class
with its existing `state: []` and `poll_result` fields. Explicitly typed
`Poll<T>` and `Future<T>` locals preserve the concrete boolean or Result
payload. Ready/Pending selection, read/prefetch behavior, cancellation
snapshot semantics and all original payload checks remain intact. No local
replacement Future, fabricated provider, generic declaration rewrite or
alternate runtime is introduced. The underlying compiler bug stays OPEN.

## Cycle 2 terminal evidence: MIR succeeds, object emission blocks

Source `f37c7cfae4349736124adc40d0de21dde85adac6` used the same genuine
3c6 producer. The real-Future typed-constructor control completed MIR 52/52
with 52 successful and zero failed modules. MIR plus weaving completed at
51922 ms. Native emission produced 41 real object files, then failed with:

`lib.nogc_async_mut.async.poll: MIR module has no functions or static data`.

The native stage terminal elapsed value was 73897 ms. Result
`C:/dev/p4future2/typed_constructor/result.env` records compile exit 1,
object_files 41 and run_exit UNRUN. Both production-owner fixtures remained
UNRUN because the launcher stopped at this failed prerequisite. No executable,
link success or runtime behavior has been demonstrated by this cycle.

The captured codegen receipt is
`build/ice/30516_n4113755797386910143/ice_receipt.tsv` in the shared source
worktree; it attributes the failure to the actual Poll module. Poll contains
a generic enum and generic impl bodies, so calling it parser declaration-only
would be inaccurate. Its zero standalone MIR output needs a legitimate
uninstantiated-template ownership proof, not a fabricated object or dummy
function. That codegen issue is distinct from the six T diagnostics removed
from this focused constructor control. The general static-generic inference
bug remains OPEN and the caller workaround is still unqualified.

Guard `C:/dev/p4future2/guard.env`, SHA-256
`9e4f776f7bc8dc5f97744eac980005a9c0c0acdce23b32ecf924fd35d8671e55`,
is complete, exit 1, quiescent, enforced and helper-integrity verified;
root 26000/session 45024, peak 2149420 KiB. No repeated green MIR run or new
native job was launched to write this evidence update. Full compiler/core/MCP
checks and source-changed authority qualification remain pending.

## Cycle 3 final evidence: conditional tiny execution, owners incomplete

This is the final permitted focused Future cycle. No fourth attempt is
planned or authorized. Source remained
`f37c7cfae4349736124adc40d0de21dde85adac6`; no passing MIR prerequisite was
recompiled for the tiny diagnostic completion.

### Tiny control: manual strict completion only

`C:/dev/p4future3/manual-tiny/terminal.json` records adapter compilation 0,
strict link 0 and execution 0. Exact stdout is `future-receiver-pass` followed
by LF; stderr is empty. Executable SHA-256:
`15808c96d4fd6e497dea4e2818f410d196a824d9f08c5825c15071a36f23ad4c`.

The diagnostic link used the 41 actual SPL objects from cycle 2, 38 retained
runtime objects verified against their source/header/tool/object identities,
and a newly compiled canonical entry adapter with five sorted module-init
calls. No fake Poll anchor, blank object, fabricated provider or permissive
unresolved-symbol link was used. The producer guard's zero functions/statics
predicate and successful strict link support the diagnostic completion for
this exact inventory. They do not establish generic-template/archive custody.

Canonical native compilation still exited 1 on Poll and remains FAILED.
The manual completion proves the tiny control's concrete payload behavior
under that explicit diagnostic link. It is neither a canonical native-build
PASS nor a compiler/bootstrap qualification or repair of the objectless-unit
contract. Its baseline failure and changed-constructor success support this
narrow source workaround; general static-generic inference remains OPEN.

### Actual cancellation owner: admission failed before compilation

`C:/dev/p4future3/cancellation_owner/result.env` records compile exit 1,
zero objects and execution UNRUN. SCV reported `SCV-E-ENTRY: entry absent
from frozen inventory`, before parse/HIR/MIR. The reviewed launcher selected
the read_only_future fixture directory but omitted the sibling
cancellation_future_receiver directory. That tracked fixture was also absent
physically because of sparse checkout. The input SHA was empty: the command
substitution masked the failing file-hash command instead of stopping
admission. This is a fixture materialization/launcher failure, not a native T
failure, and provides no production cancellation execution evidence. No
fallback scan, fixture repair/retry or fourth focused cycle was performed.

### Actual read-only-file owner: new default-argument binding failure

`C:/dev/p4future3/production_owner/result.env` records compile exit 1,
zero objects and execution UNRUN. MIR completed 56 modules: 55 successful,
one failed. No unsubstituted-T diagnostic remained in this run. The actual
error was an undefined `FILE_VIEW_DEFAULT_ADDRESS_SPACE_BUDGET_V1` at
`src/lib/common/io/read_only_file_view.spl:49:33`, reached when the fixture
omitted the optional argument. This exposes a separate default-argument
binding bug; it is not a failure of the Result payload checks, which never
executed. The actual read-only owner is not fully native-qualified.

### Final guard and qualification boundary

Guard `C:/dev/p4future3/guard.env`, SHA-256
`14e0ce1e3a1843fd1e68055dd9470c0a77385b5af286259a62958ec41072693a`,
is complete, exit 1, quiescent, enforced and helper-integrity verified;
root 36400/session 36644, peak 1270212 KiB. All three focused cycles are
terminal. No fourth focused retry is permitted under this feature budget.

The source change is a partial MIR workaround with conditional tiny runtime
evidence. Production cancellation admission, production read-only native
execution, canonical Poll objectless emission, full compiler/core/MCP suites,
full authority native linkage and deployment remain unqualified. The separate
class-static compiler repair is an UNRUN draft; it has not been validated by
these caller probes. Keep this bug OPEN and do not close the authoritative
bug DB or report full native/compiler PASS from these results.

## Phase 3 AsyncFile owner attribution (2026-10-26, Astra lane)

The normal Stage 2 producer acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779 compiled the 389-module hir_codec entry closure from a0aa04ea5df71665466a5c148cd148b6711da23e plus an unrelated explicit HirTypeKind import. Its go-to-end manifest identifies lib.nogc_async_mut.io.file as a MIR failure with E-MIR-TYPE-TypeParam: unsubstituted generic type parameter T. This is actual module attribution. Its FileThreadPool.exec has one Future.from_value(task()) call, matching the existing generic static factory mechanism.

A candidate replaces that call with one evaluation of task(), a typed Poll<i64>.Ready value, and the real Future<i64> constructor. Public signature and synchronous task execution stay unchanged. The intended code recovery reference is a0aa04ea5df71665466a5c148cd148b6711da23e. Native runtime qualification is PENDING; no workaround fix or retirement is claimed. Workaround source commit: [c2bb5f8e27379a0e2a13d383605031fe83db90e5](https://github.com/ormastes/simple/commit/c2bb5f8e27379a0e2a13d383605031fe83db90e5). Qualified bug DB reconciliation remains pending.

Regression fixture: test/fixtures/compiler/async_file_future_receiver/main.spl. It must exit zero and print exactly one async-file-task-called line followed by async-file-future-ready-pass, proving the actual production method invokes the supplied task once and returns Ready(37). Pending or a wrong payload fails. The other unchanged failed owner in the diagnostic closure is io.buffer; its prior six-cycle failure is not cleared by this candidate.

Evidence: C:/dev/wt-s3self/build/native_probe/phase3-hir-codec-import/cycle2-serial-parse/worker-output.exe.go-to-end.sdn and retained full-worker-stderr-1.log/full-worker-stderr-2.log. The command exited 1, with 387 successful MIR modules and two failed owners; aggregate dependency failures blocked all object emission in entry-object mode.

Source review confirms that the supplied task is evaluated exactly once and that the concrete constructor preserves the original Future.from_value fields (empty state and Ready payload). No known runtime regression was found by source review; this does not claim a completed runtime test. The first file-workaround attempt passed HIR/mono for 390 modules but was refused before MIR because ordinary dynload selects Both output. The existing cycle2-native-mode job uses the supported one-binary output mode and remains the pending native qualification; no new retry is implied by this record.
