# Native function owners and optional struct coalescing

**Status: native callback regression repaired in the authorized 2026-09-29 follow-up below.** The earlier three-cycle investigation and its failures remain recorded here. The focused callback fixture now executes successfully; this does not establish full Stage2/Stage4 bootstrap qualification.

## Production evidence

Frozen main `d9281560d8f3d84687cbc50ea25eeff4d62c3c33` failed strict bootstrap verification on both hosts.

- Linux full CLI compiled 2489 files with zero compile failures. The retained object for `plugins/backend_registry/full_static_backend_ports.spl` defines owner-qualified `_gpu`, but references bare `_gpu` from four function-value assignments.
- An ordinary private `spl_language_manifest` definition was kept bare by the definition mangler's blanket `spl_` exemption; an imported caller references its module-qualified owner.
- Windows run5 emitted 22 unresolved-symbol stubs despite `SIMPLE_NO_STUB_FALLBACK=1`. The run was stopped and its executable rejected. Its output is diagnostic evidence, not an admitted compiler.
- Four stub names (`rt_hal_unavailable_spawn/join/cancel/effect`) are ordinary Simple functions assigned to function slots in `parallel_executor.spl`, rather than missing external runtime providers.
- Seven stub names are fields of `RtHalIsolatedHostPort`. Those calls use inferred `rt_hal_host ?? rt_hal_unavailable_isolated_host()` bindings. The explicitly annotated `join_exact_until_fn` call did not appear in the stub list.

## Cause and scope

Function-value references use MIR `GlobalLoad`/`GlobalStore`. Their mangling previously skipped runtime-looking names and relied on suffix lookup instead of lexical function ownership. Imported same-suffix candidates can make that lookup ambiguous. Resolve real local globals first, then local functions, before runtime/suffix fallback. Explicit external, export and global ABI names retain their existing contracts.

HIR's `local_globals` set also contains function and type symbol metadata. MIR copies that set but excludes functions from its `globals` data declarations. Checking the metadata set alone incorrectly treats functions as real data globals. The precedence guard therefore uses the intersection of declared MIR globals and local metadata. A regression lowers the actual callback fixture before mangling and checks both this distinction and the resulting owner-qualified references.

Definition mangling must not infer an external ABI from the spelling `spl_` alone. Ordinary private Simple functions have module owners; actual extern declarations and explicit export/global attributes keep bare symbols. The canonical `main` to `spl_main` entry ABI remains.

The existing MIR callable-field implementation already emits `FieldGet` plus typed `IndirectCall`. It accepts a concrete struct receiver. Optional struct coalescing retains `SharedPointer<Struct>` metadata, which prevents that implementation from recognizing the fields. The prior array correction narrows only arrays. A precise imported HIR regression records this failure before any struct correction.

No app annotations, invented providers, unresolved-symbol stubs or duplicate callable-field dispatch are acceptable fixes. Scalar optional payload rules remain separate because tagged and raw scalar representations differ.

## Executable regression

`compiler/tests/native_symbol_owner_binding.rs` lowers the real three-file `test/fixtures/native/symbol_owner_binding` import closure and checks nominal struct metadata plus typed indirect calls. It then builds and executes the same fixture using `NativeProjectBuilder` under bootstrap and strict-stub flags.

The fixture covers imported private `spl_*`, local `_gpu` and `rt_*` function values, optional struct nil/present cases, annotated control, callback state and return values, one receiver evaluation, a real method control, and the real external `spl_ordered_key_cmp` ABI. Mangler unit tests cover imported suffix ambiguity, actual-global precedence, explicit ABI exports and the entry ABI.

Results are recorded in task evidence after execution. No Stage2 or Stage4 pass is claimed by these focused tests.

The actual pre-fix imported HIR test failed with coalesced type `TypeId(24)` (`SharedPointer`, inner `TypeId(16)`) while both the imported struct and concrete fallback had type `TypeId(16)`. After the struct-only correction, HIR/MIR passed one test with zero failures or ignored cases. Struct narrowing requires the default to have the same concrete inner type; nil and optional defaults keep the wrapper. Existing array behavior and scalar boxing rules are unchanged.

## Final recorded results

The first native attempt failed linking bare `_gpu` and `rt_hal_unavailable_spawn`, exposing the local function metadata distinction above. After correcting the guard to use actual data declarations, the final native link succeeds. Runtime behavior remains unresolved.

| Check | Recorded result |
| --- | --- |
| Six mangler ABI/ownership controls, production cycle 2 | 6 passed, 0 failed, 0 ignored |
| Actual imported struct HIR/MIR, production cycle 2 | 1 passed, 0 failed, 0 ignored |
| New regression from actual callback source lowering and mangling, production cycle 3 | 1 passed, 0 failed, 0 ignored |
| Native fixture compilation, production cycle 3 | 3 compiled, 0 reused, 0 failed |
| Native fixture link, production cycle 3 | PASS; 42 KB executable via clang |
| Native fixture execution, production cycle 3 | FAIL; executable exit 1, empty stdout/stderr; first callback returned false |

The final callback regression proves that actual function-value references retain their module owner. The earlier six controls and HIR/MIR check were not repeated. Passing compilation, linking and type assertions do not establish callable runtime behavior; later assertions in the native fixture were not reached. Cargo reports test exit 101 for the execution failure.

Local evidence is retained on D-backed storage:

- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/hir-red-cycle3/`: actual pre-fix shared-pointer type failure.
- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/green-cycle2/{mangle,hir,native}.log`: six controls, imported HIR/MIR pass and the preceding native link failure.
- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/green-cycle3/{causal-mir,native}.log`, `inputs.sha256`, `result.env` and `probe.sha256`: final checks and exact inputs.
- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/tmp/.tmpxpT4RR/probe`: retained failing executable and adjacent native cache. SHA256 `150c3948f75cdb4c46a348fd0e6fbb6c0840e5d3ead95abd9119ea8bc50030d3`.
- `D:/dev/simple-bootstrap-bootstrap-tools-fix-20260929/build/mini_builds/symbol-owner-review/final-cycle3-owned-inputs/`: immutable snapshot of eight tested owned files, scoped patch and hash manifest. This results update is a documentation-only addition after that snapshot.

Three production verification cycles were used: cycle 1 stopped at a peer test import compile error; cycle 2 passed the controls/type check then failed native linking; cycle 3 passed the actual callback ownership regression and native link, then failed execution. Earlier test-compilation repairs were recorded separately. No further compiler edits or test retries were made after the final failure. The combined patch may be pushed as a draft for review; it is not ready for merge or bootstrap admission.


## 2026-09-29: direct-function ABI and collision-free closure header

The user authorized continued repair after the earlier stopped investigation.
LLVM GlobalLoad and function-global initialization emit direct callable records
`[entry, 0x5344495245435446]`. The old indirect-call emitter always supplied a
hidden closure context, shifting `_gpu`'s text argument and explaining exit 1.
The call now selects the direct signature without that context, or the closure
signature with it, and joins the result with an LLVM PHI.

Review caught a discriminator collision: old LLVM closures placed capture zero
at byte 8, the same slot as the direct marker. LLVM closures now reserve a zero
kind word there and store captures starting at byte 16. Allocation, capture
stores and outlined-body loads agree. The secondary emitter delegates closure
creation and indirect calls to these same helpers. Direct records retain their
existing layout, including the scalar pool runtime's marker requirement.
MIR and Cranelift capture layouts are unchanged.

Existing LLVM closure objects must be regenerated together; mixing old capture
objects with the new layout is unsupported. Native object keys already include
the running compiler's full-byte fingerprint (`native_project/mod.rs`). The
native regression creates a fresh build/cache directory each time.

Verification used official LLVM 23.1.2 Linux ARM64, with release asset SHA-256
`143308c82f8e21707be7fdc135d5e0ddd9a46a377ca9f38befc716fd842cb59b`.
The initial installed LLVM 23.1.0 was rejected by the existing version pin;
no pin was weakened. A command launched outside the Rust workspace also
stopped at dependency selection before compilation and was corrected to the
workspace directory.

- Imported HIR/MIR owner regression and initial native execution: 2 passed,
  0 failed (`/tmp/pr2044-native-callback-fixed.log`).
- After the review correction, the affected native execution test: 1 passed,
  0 failed, 1 filtered out (`/tmp/pr2044-native-callback-marker-fixed.log`).
  It checks direct text/bool and integer calls, optional struct callbacks,
  single receiver evaluation, a captured closure, a capture-free closure,
  floating-point arguments/results, and a capture equal to the direct marker.
- Independent read-only Linux-lane review checked all LLVM closure producers,
  the outlined capture consumer, secondary-emitter delegation, and runtime
  thread/pool discriminator contracts; no remaining concrete blocker found.

This is focused compiler/bootstrap evidence. Full bootstrap and the previously
pending Trace32/hardware/MCP qualification remain separate requirements.

## Windows scalar-pool regression, 2026-09-29

The expanded native fixture passed on the landed compiler at
`2956aef4b4b9008d4c8450f4eecb8d97efb15dc1`: exactly 1 passed, 0 failed,
0 ignored, native Cargo exit 0. The selected test was
`imported_private_functions_struct_slot_values_and_extern_abi_execute`, using
the LLVM backend, bootstrap profile, MSVC target, strict no-stub/delegate flags
and four build jobs. Total build/test time was 460.1 seconds; test execution
was 7.70 seconds. All 24 recorded input hashes remained unchanged.

Real C pool workers accepted a named callback (41 to 42), joined and released
its task, and rejected ordinary, marker-valued and empty closures with -3.
The fixture also checks subsequent captured calls, pool close/destroy,
global callbacks, named/empty/captured VOID calls, and captured bool/text
callbacks. Existing landed callback and floating-point controls remain.

- Main fixture SHA256: `5AEFF4EE8288979B1000399491406005D76F50310D32DE2EA9415CCC4FFE1C25`.
- Ports fixture SHA256: `F7A445C3D39BB662823F00F0589F2A513AEF4C430B1D9D3724F07B659FD4E802`.
- Executed probe SHA256: `29CD22B6D39E4CA96E72995BC0116449AFF8003BE839705C127EA8065D1D8E79`.
- Frozen evidence: `build/mini_builds/callback-windows-cycle2-20260929/`;
  probe: `tmp/.tmp2YRS5a/probe.exe` within that directory.

Linux execution of this expanded fixture remains pending. This result makes
no claim of bootstrap Phase 4 qualification.


## PR #2046 integration review

The independently prepared adapter proposal in commit `6b70440940e` passed its
reported Linux/Windows direct-callback fixtures and LLVM adapter signature
checks. Its new named-function records used a zero kind word and a thunk with
an implicit context. That representation is rejected by the scalar pool APIs
in `runtime_pool.c` and `runtime_thread.c`, which require the direct marker and
call the entry without a context. Those pool paths were outside its fixture.

Integration therefore retains the landed #2047 direct-record contract and
reserved closure kind slot. The proposed adapter helper is superseded; its
platform evidence does not attest this integrated source. The global named
callback regression from #2046 is retained alongside the existing closure and
marker-valued capture controls. The hardware probe's portable I/O facade
changes are independent of the callable representation.

The integrated global-callback native fixture passed with LLVM 23.1.2 ARM64:
1 passed, 0 failed, 1 filtered out. Log: `/tmp/pr2046-global-callback-test.log`.
This additionally exercises the function-global initializer's direct record,
without replacing the scalar pool ABI with the alternative adapter.

## PR #2049 Linux conflict-resolution evidence

The merged fixture retains the landed global callback check and adds the
scalar pool, VOID, and captured bool/text controls. On Linux ARM64 with
LLVM 23.1.2, the expanded native test passed: 1 passed, 0 failed, 1 filtered
out. Cargo used `CARGO_BUILD_JOBS=10`; the focused fixture itself retains its
serial native compilation configuration. Log: `/tmp/pr2049-expanded-native-test.log`.
This result does not qualify a full Linux or FreeBSD bootstrap.
