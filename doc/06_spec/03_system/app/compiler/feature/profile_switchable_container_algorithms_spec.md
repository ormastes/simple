# Profile-switchable containers: captured workload reaches native storage

**Status:** Executable SPipe scenarios authored; not run on an admitted source-matched pure-Simple runtime. The forced-profile scenario below is an authored update pending SPipe docgen regeneration and zero-stub validation.

**Executable source:** `test/03_system/app/compiler/feature/profile_switchable_container_algorithms_spec.spl`

## Purpose

Compare source-attributed linear, hash, and ordered text and integer-key generic set/map behavior through interpretation and LLVM native execution, including initialized locals and fields returned by typed factories. Require unsupported ordered keys and mismatched embedded profile targets to fail on both engines. A forced ordered map with matching embedded feedback must preserve its value; a second forced hash map must reject feedback carrying the first map's site. Replay a valid synthetic profile with paired hash collision samples into four auto container families and check their contents. Then show that a captured workload is admitted for the same source, workload, and target; that a native build uses it for the hot sites; and that a target mismatch leaves the previous binary intact. These are system scenarios for REQ-PSC-001 through -006 and -008.

## Preconditions

- Set `SIMPLE_QUALIFIED_RUNTIME` to an admitted, source-matched pure-Simple `simple` executable. The admission helper rejects a Rust bootstrap seed.
- The scenario sets `SIMPLE_NO_STUB_FALLBACK=1` for each native build and restores its previous value afterward.
- Run from the repository root on a Linux/WSL host with the LLVM native backend and `src/lib` available; the shared runtime-admission helper reads its environment through `/bin/sh`.
- The probe is `test/02_integration/compiler/probe_profile_switchable_cli_feedback.spl`.
- The differential semantics fixture is `test/fixtures/profile_switchable/semantics_probe.spl`.
- The generic differential fixture is `test/fixtures/profile_switchable/generic_semantics_probe.spl`.
- The typed factory fixture is `test/fixtures/profile_switchable/typed_factory_attribute_probe.spl`.
- The embedded replay mismatch fixture is `test/fixtures/profile_switchable/embedded_replay_mismatch_probe.spl`.
- The forced-profile mismatch fixture is `test/fixtures/profile_switchable/forced_prior_mismatch_probe.spl`.
- The collision replay fixture is `test/02_integration/compiler/probe_profile_switchable_collision_replay.spl`.

## Procedure and expected evidence

| Step | Action | Required observation |
|---|---|---|
| 1 | Run the semantics fixture through the interpreter and an LLVM native build. | Every representation preserves insert, duplicate, lookup, sorted snapshot, removal, and clear behavior for text sets/maps; both executions print `COLLECTION_SEMANTICS: PASS`. |
| 2 | Run the integer-key generic fixture through the interpreter and an LLVM native build. | Linear, hash, and ordered generic set/map instances preserve those operations; an optional nil map payload retains its key; both executions print `COLLECTION_GENERIC_SEMANTICS: PASS`. |
| 2a | Run the typed factory fixture through the interpreter and an LLVM native build. | An attributed local text map selects hash, a plain factory result remains linear, an attributed generic map and class field select ordered, and all retain their values; both executions print `COLLECTION_TYPED_FACTORY: PASS`. |
| 3 | Run the unsupported ordered-key query probe through the interpreter and an LLVM native build. | Both executions fail with `OrderedMap key type has no supported native order`; neither prints its unreachable marker. |
| 4 | Run the embedded replay mismatch probe through the interpreter and an LLVM native build. | Both executions fail with `embedded collection workload does not match container site and target`; neither prints its unreachable marker. |
| 4a | Run the forced-profile probe through the interpreter and an LLVM native build. | Both executions first print `FORCED_PRIOR_VALID: PASS` after using a matching ordered map, then fail with `embedded collection workload does not match container site and target` for a forced hash map carrying a stale site; neither prints `UNREACHABLE_FORCED_PRIOR_REPLAY`. Interpreter/build/native output and status are retained under `build/test-artifacts/compiler/forced-prior-mismatch-<pid>.txt`. |
| 5 | Prepare a valid exact-site profile with paired hash probe/collision samples, then run the collision fixture through both engines. | Four auto containers choose ordered storage before insertion, preserve set/map values, and remain ordered after clear; the explicitly linear container remains linear. Both executions print `COLLISION_REPLAY: PASS`. |
| 6 | Run the workload probe with `.sprof` capture for `lookup-workload` and `x86_64-v3`. | Process exits successfully; the probe prints its PASS marker and stable `ast://` set/map sites; the profile contains hash probe and collision metric records. |
| 7 | Explain the hot set site with the captured profile. | The CLI reports an admitted exact-site profile and selects hash for the runtime's initial plan. |
| 8 | Native-build the same probe with that profile, then execute the binary. | Native execution succeeds; hot set and map are hash-backed before insertion; cold and explicitly linear instances remain linear. |
| 9 | Attempt a native build of the same output for `aarch64-neon` using the `x86_64-v3` profile. | Admission fails with a target-sample error; the prior binary still exists. |

The scenario removes its profile and binary after collecting the mismatch evidence. It checks real process exit codes, profile bytes, CLI explanation text, and the native program's reported container state.

## Failure interpretation

- A missing qualified runtime raises `MissingEvidence` in every scenario; it is an infrastructure failure, never a skipped or passing result.
- A capture or explanation failure points to source identity, profile validation, parser site mapping, or target matching.
- A native build or execution failure points to profile embedding, compiler lowering, or backend/runtime parity. The forced-profile probe requires a successful native build followed by the expected nonzero child exit; a failed build does not satisfy the rejection scenario.
- A mismatch that overwrites the binary violates atomic rejection of incompatible feedback.

## Coverage limits

These scenarios cover text and integer-key generic set/map semantics, initial representation, and profile replay on one native backend. The new forced-profile scenario calls production map constructors directly; it does not by itself prove parser attribute-to-typed-factory lowering with embedded feedback. Other generic key/value families, typed CollectionPlan-to-MIR substitution, all P6 operation metrics, JIT/other native targets, and performance targets require the remaining tests in `doc/03_plan/sys_test/profile_switchable_container_algorithms.md`. No release PASS is implied until those gates and these scenarios execute on an admitted runner.
