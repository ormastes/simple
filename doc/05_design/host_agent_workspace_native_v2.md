# Native workspace Host continuation V2

Status: **UNREVIEWED source integration**, runtime/compiler/native NOT_RUN.
Frozen Host V1 source and old packet decoders remain unchanged. This additive
consumer requires separately reviewed actual source V2 and common native ports.

The native packet has its own strict kind/version and native-profile-version
discriminator. The native bootstrap consumes explicit full manifest V2 containing the strict V1
base plus the independently bounded executable profile. Old bootstrap/codecs stay
strict. Independent invocation authorization uses a different V2 environment
domain and operation identity, so an old staging approval cannot authorize the
native path even with identical manifest bytes. The full installed V2 profile
digest remains covered by the signed stage manifest. There is no signer derived
from SSH/configuration and no public DATA-to-owner factory.

The actual Host entry authenticates the exact Host and invocation packets and
original opaque selection before acquiring source custody. The closed common
facade opens the original source using the actual container's paired reader and
storage; it captures cleanup inside that same fresh capsule before returning a
borrowed source loan. The Host adopts the returned container/lease/source before
checking an error. It then checks actual installed V2 profile, program/config,
quota root, complete request and fresh signatures, archives exact inputs, and
begins the existing real Host capacity transaction. Any begin error can follow
WAL publication, requires recovery, and never permits staging.

Success allocates an optional native payload in the **existing**
`host_execution_progress_slots_v4` registry and returns its existing opaque
`HostExecutionContinuationV4`. There is no second registry/journal/root. Each
native step validates the actual current writer, original lease/authority/scope,
nonregressing journal sequence and installed context. Benign same-writer helper
transactions can advance sequence; the actual original operation and ledger
reservation still have to match before effects.

The bounded phases are source V2 staging, same-capsule workspace enablement,
Prepare, Create, InputConfiguration, Start and Inspect. Enablement derives the
actual binding internally from the same retained source's `begin_binding_v3`;
the caller cannot supply binding DATA. All native helpers use the common closed
action enum and typed begin/step turns. Pending state retains the actual common
owner and advances only when a genuine operation is returned. No synthetic
pending runtime status or synchronous payload wait is used.

Create must complete the native producer's actual held-parent/46-field config
and container-image-container checks before its private Start prerequisite can
be satisfied. Host independently consumes actual InputConfiguration and compares
exact request, runtime, bootstrap argv, immutable image, cwd, rootfs and TTY/input
facts. Native runtime observation never implies approved agent image observation,
Input/Geometry permission, terminal adoption or InteractiveReady.

Changed/expired authority while a helper is pending invokes the helper-only
workflow-cancel/drain port, which must forbid future payload effects while
retaining real cleanup. It does not kill the primary. Primary Stop requires
independent current `host_workload_cancel_v1` grant and approval, bound to the
original exact operation/manifest/scope under current installed policy. Stop
does not destroy storage, settle accounting or clear the continuation.

Running, partial/error and stopped turns retain actual Host capacity, container,
source loan, original storage lease and canonical continuation. The service must
retain all returned owners before decoding diagnostics or delivering a reply.
Source loans must never be independently closed: the actual common capsule owns
source cleanup. No public phase/boolean removes the registry entry or releases
capacity/storage. Final release requires actual lower retirement and transport
cleanup, Host helper acknowledgements and an authorized original-source cleanup
transition; the final combined owner review must establish that seam.

The source/probe producer and native ports are external owned dependencies. A
known Linux refusal in generic Windows V4 execution is never used as a probe
producer. Eight authored tests cover wire/cryptographic separation only; no fake
source, opaque selection or capsule supplies a positive native execution test.
No operational route, qualified launch, cleanup or full feature completion is
claimed by this source snapshot alone.

The Host obtains executable policy from the same actual protected Source V2
reader, compares its canonical bytes with the full manifest, and requires real
original Host operation/reservation and actual source projection memory to meet
the checked image + bootstrap + agent + 65536 scratch minimum before staging.
The bootstrap budget must include its actual runtime/argv/hash workspace and the
Git helper peak; scratch is not a claim that all overhead fits 65536 bytes.
ISA and exact image-size bounds are explicit, including AArch64 and large ELF
images. No generic executable pin cap is weakened or allocation inferred from
these public fields. The actual native capsule separately validates its original
parent resource admission; no second parent is opened for extra budget.

The protected compiled-bootstrap profile separately rejects a bootstrap budget
at or below the exact known Git/helper/image/argv/native-arena/hash floor. Its
excess is administrator-approved runtime working allowance, not a measured RSS
bound. The generic executable-profile codec deliberately remains reusable DATA.
Actual reservation proof is read from the current Prepared/Executing Host ledger
row and exact journal operation, including the returned post-begin owner; the
request's declared amount cannot stand in for it.
