# SCV warm inventory misses a tracked source revert to HEAD

Status: OPEN. Scope: Item 6 source-event authority and warm admission.

## Reproduction

An earlier diagnostic run temporarily changed `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` and then restored its committed bytes. Its persistent source inventory still held the temporary row (SHA-256 prefix `beb045`, 116672 bytes); the live, committed file had SHA-256 prefix `3e3607`, 116337 bytes. Two Item 5 native compatibility probe launches with the admitted Stage 2 compiler stopped before compilation with `SCV-E-ADMISSION: snapshot-index-drift:src/compiler/80.driver/driver_hir_pipeline_lowering.spl`. A fresh compiler cache did not change that outcome. Receipts: `build/mini_builds/item5_jit_owner_explicit_types_20261010/build.log` and `build/mini_builds/item5_jit_owner_explicit_types_fresh_20261010/build.log`.

The explicit `SIMPLE_SCV_INVENTORY_COLD_INIT=1` run rebuilt source authority. The snapshot's driver and changed type-inference file hashes matched the live files; the probe reached all 1009 HIR modules. Its later HIR type-closure failure is independent of this admission failure. Receipt: `build/mini_builds/item5_jit_owner_explicit_types_cold_20261010/build.log`.

## Suspected boundary and required fix

The warm path can return its unchanged inventory when Git and filesystem event batches are empty (`src/app/compiler_entrypoint/inventory_events.spl`, around line 752). A restored tracked file has no net Git working-tree difference from HEAD; in this reproduction no event advanced the stored inventory row. The exact missing event producer remains to be isolated. Do not silently trust a stale row or turn every warm acquisition into a full source scan.

Add a deterministic regression that publishes an inventory for a modified tracked source, restores its HEAD bytes, and then performs warm acquisition. It must either produce an authoritative event and publish the restored row, or reject with an actionable refresh instruction before snapshot admission. Preserve the no-event startup and RSS budgets. Until repaired, explicit cold init is the supported recovery for this recorded case; native warm correctness and Item 6 performance qualification remain open.

## 2026-10-10 recovery candidate and native limit

The app source-authority owner now retries exactly once with explicit cold inventory when warm snapshot acquisition returns `snapshot-index-drift:`; cold acquisition never recurses. An isolated Git fixture changes a tracked source, publishes the dirty generation, restores HEAD bytes, then requires a newer admitted generation with the restored bytes and both prior snapshots intact. The initial native probe omitted a required compiler source root. With the complete source closure, 135 HIR modules passed; an imported generic call in `inventory_scratch.spl` then required an explicit `CompileSourceEventV1` type argument. The corrected probe passed HIR and monomorphization, but MIR rejected unrelated reached library constructs (including unsupported iterable lowering and unresolved method calls) before linking. Receipts: `build/mini_builds/item6_warm_revert_native_full_20261010/` and `item6_warm_revert_mono_explicit_20261010/`. Runtime recovery is therefore UNVERIFIED; do not count this as Item 6 acceptance. The three-cycle cap stops further native retries here.

## 2026-10-11 graph rebuild recovery handoff

Current-source review found a second boundary after the bounded inventory retry: `compiler_source_authority_acquire_v1` could return a restored snapshot, but `compiler_entrypoint_admit_v1` still rejected a complete prior graph unless the user separately set `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`. Even an admitted rebuild-pending marker was not consumed by the driver cold selector.

The authority record now carries an internal `recovered_cold` bit only on a successful warm-drift cold retry. Entrypoint admission uses that bit to select the existing `cold-rebuild-pending` transition while preserving old CURRENT. The driver treats that pending marker as cold construction authorization through SOSIX environment access. Explicit cold and ordinary warm authority keep the bit false. The Git revert fixture asserts these signal states.

This is an unverified source candidate. The previous native recovery fixture remains stopped at unrelated MIR failures, and current disk headroom is below compiler bootstrap minimum. It does not qualify automatic full-entrypoint recovery, an event-maintained warm route, or time/RSS budgets. Next evidence must exercise the complete graph-preserving admission and driver rebuild path, then prove unchanged warm requests stay on the warm route.

## 2026-10-11 focused SMF route and regression wiring

The admitted Stage 2 compiler compiled the current warm-revert fixture through parse, 135/135 HIR modules, and monomorphization using compile --format=smf. MIR lowering failed before an SMF was emitted. The first reported fatal error was unresolved method call: split in src/lib/scv/compile_snapshot.spl:275:22; the log also records unrelated enum-payload and iterable-lowering errors. Receipt: build/mini_builds/item6_warm_revert_smf_20261011/compile.log. This route cannot verify runtime recovery.

test/01_unit/app/compiler_entrypoint/source_authority_spec.spl now calls the tracked-file-revert fixture as a real assertion. The test is pending an admitted full runtime; the source change does not establish an Item 6 PASS.

## 2026-10-11 tracked-membership event candidate

The compile event cursor now records an immutable digest of the tracked dirty src/test path set (cursor v4). Warm Git status compares that admitted set with the current dirty set and emits a source modify/delete event for each path that disappeared from status, covering restore to HEAD without a full source listing. The new tracked record is published before inventory CURRENT, discarded on failed publication only when ownership is certain, and the previous record is retired after a successful publication. A v3 cursor fails closed with an explicit cold-init instruction because it lacks the prior dirty set. The production integration spec and isolated native fixture now assert edit → restore-to-HEAD → unchanged warm behavior.

The focused Stage 2 native build reached 110/110 HIR modules and monomorphization (generic_fns=14, call_sites=4, specializations=3, unresolved=0), then failed in MIR on unrelated app.io.env_access_host.spl substring resolution, enum literal payload lowering, and lib.common.sdn.value.SdnValue payload mismatches. Receipt: build/mini_builds/target56_cold_git_refresh_probe_v4/build.log. The source candidate is **not runtime verified**; Item 6 remains open for current-source native build, complete entrypoint recovery, and warm performance/RSS qualification.
