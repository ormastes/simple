# Fresh workload V2 DATA model spec

**Execution status: AUTHORED_NOT_RUN.** These cases exercise pure records,
canonical request binding, the production-used settlement eligibility/history
reducers, modeled operation state, and returned WAL row values. They do not
establish installed custody, machine authority, local admission, native process
creation, successful execution, or actual WAL commit counts.

Executable source: `test/01_unit/lib/container/machine_fresh_workload_record_v2_spec.spl`

## Cases

1. **Accounting conservation:** a valid V1 epoch and retained Linux request
   debit the helper and workload from the existing usable partition. The
   remaining plus charged CPU and memory equal the epoch's usable totals.
2. **Boundary and capacity rejection:** a request that exactly consumes the
   remainder after the helper is accepted. A one-unit CPU excess and a
   one-byte memory excess are rejected with the capacity error.
3. **Immutable request and finite profile:** mismatched plan digest/workload
   identity and mismatched plan host scope are rejected. A host mount and
   terminal request are outside this initial profile and rejected.
4. **Reservation and settlement rows:** initial modeled reservation emits one
   workload record and two uncertain reservation rows. A completed operation
   retains its outcome digest, rejects replay to executing, and settlement
   returns action evidence plus updates for only the workload and its partition.
   The modeled partition charge returns to 3500 CPU millis and 3584 memory
   bytes; no Host reservation or outside-obligation row is emitted.
5. **Action/result validation:** unknown actions, malformed native identity,
   oversized evidence, and nonpositive timestamps are rejected.
6. **Settlement ordering:** an inspect-confirm completion without association
   is refused before modeled release rows are returned. With every modeled
   prerequisite true, preparation reserves three rows; finalization succeeds
   once and rejects a repeated canonical finalization.
7. **History budget:** noncleanup `38 + 6` and cleanup `57 + 7` exact totals
   are accepted; the respective `39 + 6` and `58 + 7` over-budget totals are
   rejected by the preappend budget reducer.
8. **First diagnostic:** later poll, retry, and cleanup diagnostics do not
   replace the first modeled diagnostic.

The Linux request fixture has no device-selection field. The model's reservation
charge encodes an empty exclusive-device list; this is a data assertion and does
not claim a GPU admission check or native-device isolation. Settlement/history
assertions describe the shared canonical DATA protocol only; they do not count
actual WAL appends or claim native-side effects.

The first-profile fixture image uses the required fully qualified registry form. The immutable request binding case additionally rejects a local OCI transport, preventing an image address from becoming an uncontrolled host-object input. Quiet pull's local config ID remains distinct from the requested platform manifest; actual correspondence is the separate real-fixture producer gate, never fabricated by these DATA tests.

## Reservation-publication regression

The ninth case calls the production-used reservation progress functions and actual reserve-row constructor. A staged request followed by invalid initial time cannot satisfy the identical-request retry/effect guard or confirm directly; publication-unknown also refuses retry/effects. Only the final admitted guard succeeds in the modeled confirmation sequence. In production that final transition is called solely after the original writer's reserve CAS and exact history readback. The spec does not construct an authority, fabricate WAL publication, inject a real clock/CAS failure or prove native effects were absent. All execution remains NOT_RUN.
