# Generic extern specialization changes the provider's C symbol

Tracking key: BUG-GENERIC-EXTERN-LINK-NAME-20261028.
Canonical BugDB insertion is pending its existing malformed-data blocker.
This report is not a database write.

## Observed failure

GNU Phase2 compiler SHA256
`c0e2853893ff2cdc4dc93176985bad8e407a74098335e202a138a3bb70b457d7`
compiled the tracked `test/fixtures/compiler/native_mutex_integer_gate/main.spl`
through code generation, then failed linking on `rt_mutex_lock$i64`,
`rt_mutex_new$i64`, and `rt_mutex_unlock$i64`. The real runtime defines the
unsuffixed C names. No alias or unresolved-symbol override was added.

Evidence: integration lane
`build/phase2-descendants-20261028/runner-mutex-gate-explicit-types/compile.log`.

The earlier runner's E-MONO-032 calls needed explicit mutex type arguments
and a concrete optional type for thread spawn's nil environment. After these
source repairs, the full 292-module attempt exceeded its 10 GiB watchdog cap:
exit 88, peak 10,530,084 KiB. That attempt has no semantic compile verdict.
It does not establish a performance regression against an equal-work baseline.
Evidence: `runner-explicit-runtime-types/rss.env` and retained partial log in
the same descendants directory. The fixed 24 GiB shard headroom admitted no
HIR workers on this host; no headroom or memory guard was disabled.

## Root cause and repair

`substitute_function_node_v1` and `request_specialization` both replaced an
extern declaration's name with the generic specialization name. MIR correctly
treated that declaration name as the provider's physical C symbol.

Extern specializations now retain their original C declaration name and their
concrete types. Their unique SymbolIds and mangled specialization-map keys
remain distinct. Mangled HIR call spelling and internal `sym_names` identity
are retained; MIR resolves the concrete SymbolId through its typed symbol row
to the original C name. Ordinary generic function names remain mangled.

Placement validation derives the expected extern name from its original
template signature. Declaration-only extern instances still receive typed
symbol rows but are excluded from complete emitted-body placement evidence.
No HIR schema field, provider alias, or relaxed signature validation is used.

## Verification scope

The authored `generic_extern_linkage_v1_spec.spl` checks distinct concrete
specializations, typed symbol rows, preserved C names, mangled call identity,
and an ordinary generic control. It remains UNRUN until a full test CLI exists.
The integer mutex fixture is the real native compile/link/run regression.
Bool HIR shape assertions do not establish the native bool or aggregate ABI.

The older module-scoped placement route still has pre-existing untyped symbol
rows and applies COMDAT metadata to declarations. No qualification of that
route is claimed. The isolated checked placement path is the unit test's scope.

The replacement Phase2 image
`8365cec04eb7292695e9e10850af68c0dab61e86a5bacae5ad5d3e51f0183f60`
built with six modules compiled, 1602 reused, and zero failures, then compiled
Hello and executed its exact expected output (both exits zero). This is
provisional Hello qualification, not canonical admission or a runner PASS.

That exact replacement also built and linked the tracked native integer mutex
fixture and executed it successfully (build 0, run 0). The fixture checks
two real acquisitions, the stored zero sentinel, and intervening unlocks.
Evidence: integration lane
`build/phase2-descendants-20261028/runner-mutex-gate-extern-linkage/`.
The watchdog run receipt independently records exit 0, peak RSS 2628 KiB.
An inline-shell printf mangled the auxiliary `run.exit` text to `0n` on
Windows; `result.sdn` identifies that artifact and binds the observed tool
exit and unchanged watchdog receipt instead. No green execution was rerun.

## Archive replay follow-up

The full runner reached its GNU link under a 14 GiB cap (peak 11,091,820 KiB),
but its 52,202-byte command exceeded Windows CreateProcess limits (error 206).
A diagnostic Clang response-file invocation reached LLD and exposed six
mangled array-extern references in the type-pool module. The ordinary native
cache already binds the executable hash, and the affected object was freshly
created during the replacement build. No ordinary-cache key defect was proven.

Two archive replay consumers still forced `function.name = item.mangled_name`
after shared specialization. They now preserve the canonical extern name.
`MonoTemplateSignatureV1` carries an explicit `is_extern` discriminator through
all three projections; its v4 digest binds that discriminator. Specialized
extern signature names retain the C spelling, while archive publication keeps
`state.sym_names` keyed to the mangled internal spelling.

The retained-path control uses the real standalone
`test/01_unit/compiler/bootstrap/type_pool_root_rank_native.spl` entry with a
cold cache under the 8365cec compiler. It built, linked, and ran successfully,
printing exactly `PASS type-pool-root-rank: two scopes retained text/scalar/nested owners`.
The first attempted fixture file was its helper without `main` and correctly
failed with missing `__simple_main`; that attempt provides no runtime evidence.
Both attempts are retained under `runner-type-pool-{cold-83,native-cold-83}`.

Archive signature/name regressions were added to the existing
`archive_generic_linkage_metadata_spec.spl`; these SPL specs remain UNRUN.
The archive fix and response-file transport are being rebuilt together before
the next full-runner attempt. The earlier real frontend smoke in both modes,
version comparison and unsupported-command rejection passed for 8365cec.

## Final bounded result

This supersedes the pending-rebuild status above. Extern HIR call spelling now
uses the canonical C name; unique SymbolIds and internal lookup keys retain
the mangled specialization identity. An exact-ID guard prevents completed
extern calls from being rediscovered as unspecialized templates. Caller-module
signature mappings are added only for extern specializations.

Producer `a757895813b3f6e31c31dead703ee4cd3e5434df75a138bfc7ad3ffed6a885fc`
compiled 292/292 native runner modules and linked 232/232 inputs successfully.
The outer build exited 88 afterward during separate SMF cache generation.
The retained PE is diagnostic evidence, not an admitted runner. New SPL
regressions remain UNRUN. Canonical BugDB registration remains pending because
the available database has malformed records and the real writer is unavailable.
