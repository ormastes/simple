# Resident Simple session owner — implementation candidate

The implementation lives in `observer_resident_owner_v1.spl`, with cold
allocation in `observer_resident_storage_v1.spl` and canonical-to-LLVM patch
translation in `xray_llvm_resident_leaf_v1.spl`. It implements every
`TraceObserverV1` operation and calls the actual resident native adapter.
It does not use `TraceReferenceModelV1`.

The candidate constructor registers the live main executable after the native
runtime-ready marker. All facade instances share one process owner protected
by the native nonblocking control guard. Hook entry rejects cold operations.
Every cold operation also requires the selected allocator's Process identity;
Session/Transient scopes are rejected before creating the owner record or
mutating retained control state. The module-level empty array initializer
precedes this guard: its actual allocation ownership needs startup evidence
and may require an allocation-free empty representation. The guard alone does
not prove that initializer's lifetime. No user callback or scope transition
runs inside an operation.
Registration is attempted once, reserving its complete 32 MiB budget even on
failure. The candidate manifest is issued by actual-image binding; selection
must match its incarnation and canonical module/site IDs. Only the mapped leaf
passes LLVM IDs to compiler-rt.
The selection helper returns a fresh array of scalar site IDs selected by
owner/key, never the internal manifest, metadata arrays or binding rows.

Each successful preparation allocates a fresh contiguous descriptor, context
pool and slots, sorted dispatch map, one channel per context, and poll scratch.
Allocation attempts are charged before allocation and never refunded. Raw
resident storage has a 64 MiB process limit, 16-generation ceiling and
64-context ceiling. Every published address remains resident until exit;
logical release only invalidates the current handle. Simple metadata carrier
layout and RSS are still unqualified; the reservation is not a measured RSS
claim.

Stop closes native admission without unpatching: armed sleds and their exact
IDs remain resident, and preparation/restart cannot reuse that adapter.
This requires no post-start physical patch authority. Drain first checks native
callback pins, then closes each channel and requires every queued record to
have been polled. A timeout preserves the generation and Draining state.
Flush checks pending records without discarding them. Poll has a 4096-record
bound and rotates contexts. Loss counters are lower bounds whenever
`backend_errors` is nonzero: native reentry/contention, pool sentinel and
channel inexactness contribute an explicit diagnostic. Queue high-water is
currently the maximum observed queue depth at poll, not an exact producer
high-water measurement.

## Qualification remains open

- `observer_resident_admission_v1.spl` is the shared public authority.
  Capabilities advertise no admitted backend/profile; both public prepare and
  start return UnsupportedProfile before touching native/runtime state.
  The former candidate profile string no longer authorizes anything. Start
  also requires a runtime-owned quiescent handoff, currently explicitly
  unavailable. Neither runtime readiness nor a config enum proves quiescence.
  The private owner mechanisms remain source candidates with dynamic/raw-edge
  restrictions; no public route can invoke them to activate instrumentation.
- Native integration and compiler-generated ABI execution have not run for
  these files. No native build is authorized while the concurrent bootstrap
  holds its memory reservation.
- Exact generated aggregate/global/trait carrier behavior, metadata memory
  cap, implicit ordinary application startup wiring and end-to-end evidence
  remain required before opening public admission.
- Faulted captures retain all allocations and remain blocked; the facade does
  not yet expose adapter recovery. No stop/unpatch failure is treated as
  successful drain or release.
- Starting from an actual quiescent root refreshes its TLS generation. Failed
  root attachment closes/unpatches and returns BackendFailure, retaining a
  faulted inaccessible generation instead of returning an Active handle.
- Exact producer high-water, completion/loss diagnostic event delivery and
  platform/profile performance gates need qualification before V1 completion.

Focused allocation-budget specs cover complete layout accounting, extreme
unsigned inputs and per-generation bounds. They are source candidates until
run by an admitted self-hosted tool. Astra accepted the corrected source-only
checkpoint under an incorrect assumption that the candidate route was private.
Follow-up review found the callable public profile-string bypass; the shared
closed admission authority above corrects it. Tests now exercise the actual
public prepare/start refusal for the former magic profile and guessed handles.
The checkpoint explicitly retains the initializer
ownership, actual quiescence and native qualification gaps. No release/merge
readiness is claimed.
