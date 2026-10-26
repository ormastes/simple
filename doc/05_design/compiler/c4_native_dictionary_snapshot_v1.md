# Private bounded ordinary dictionary values snapshot

Source checkpoint only; all new executable controls UNRUN. This is not a safe
general Dict API or complete compiler request admission. Actual MirLowering
invocation confinement and canonical Array<MirFunction> lowering remain required.

Input qualification uses the existing immortal registry BEFORE header access.
Positive immutable dictionary read_owner is birth identity for scoped and
persistent dictionaries; read_epoch/read_backing/entries/cap/len/tombstones are
revalidated at fill. SOURCE dictionaries are rejected. Observation/fill take
nonwaiting lifecycle→registry locks, allocate nothing and call no user code.
Ordinary alias writes do not take those locks: actual synchronous compiler
owner must exclude callbacks, tasks, reentry and map writes across the sequence.
TLS is not that authority; fixed records are private data, not receipts.

Input qualification Q = 16*immortalCapacity+256 bounds one full registry lookup
including misses. Fill work = 2*Q + 32*scopedCapacity + 16*dictCapacity +
8*liveCount + 256. The two Q cover input/output registry qualification; scoped
capacity pays actual output birth lookup, dictionary capacity pays every slot,
and liveCount pays copies. This is logical conservative work, not physical
CPU/wall-clock/RSS qualification. Bound observation itself requires a fixed
prepaid owner permit; caller must debit the SAME actual compiler invocation
account before all bound/observe/allocator/fill calls. Raw API does not debit it.

Canonical array owner cost is computed under locks BEFORE allocations/lookups:
actual header sizeof, max(length,4)*8 payload, immortal resize bytes/slots and
oldCapacity*newCapacity collision multiplicity, scoped index equivalent,
actual active scope/session ledger resize/copy, and insertion/rollback probes.
Bound metrics are revalidated from CURRENT dimensions on array_new; insufficient
work/fields/bytes refuses before header allocation or index lookup. Existing
canonical registration malloc-under-registry-lock semantics are retained by
explicit root decision; finite lock acquisition can refuse, no spin/retry.
Ordinary array creation still calls the identical extracted lock-aware immortal
registration core through its original locking wrapper.

Array_new produces a fresh canonical registered array and a C-owner stack
witness containing exact scoped birth/owner/data/capacity. Output requires an
actual active module/session scope (caller activation remains an integration
prerequisite). Private unpublished array marker0x40 is disjoint from existing
tuple1/bytes8/u64packed16. The handle must stay inside this private transaction;
ordinary operations/clone/deepfree are not permitted on the unpublished handle.
Fill authenticates actual registry+scoped identity and marker, len0/data/cap,
checks nonalias and exact observation, then copies unchanged native value words
in normal hash-slot order. Only successful fill sets len and clears marker.
Marker prevents a copied prepublication witness from disposing even a published
zero-length output. Failed fill leaves length unpublished and witness live for
exactly one private dispose; dispose unregisters canonical identity before free.
Stale ledger rows remain safe because canonical scoped birth no longer matches.

Typed integration must use actual lower_dict_keys_or_values_array metadata:
Array(MirType.Struct(MirFunctionSymbol),0), runtime_array_locals and
array_element_struct_syms, then normal indexed decode_runtime_value. There is no
raw-word→MirFunction cast, reboxing or guessed backend Struct tag. Pure/hosted
implementations unsupported; no CapLevel parity or complete SOURCE claim.

Authored native controls: forged tagged address, observation/array/fill one-unit
short, zero length and copied witness after publication, sparse/tombstone map,
raw unchanged values, actual mutation, deterministic owner/epoch/backing/cap/
tombstone changes, SOURCE flag refusal, exactly-once disposal. No jobs run.
