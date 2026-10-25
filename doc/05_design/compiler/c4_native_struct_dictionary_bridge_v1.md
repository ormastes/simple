# Native Struct to Dictionary bridge

Status: source implementation and fixtures authored; execution UNRUN during
Phase3. This does not enable SOURCE admission.

Operation17 is `rt_source_region_struct_dict_write_v1(control,generation,
destination,slot,dictionary,work) -> advanced_epoch/error`. The unsafe Simple
facade uses the existing paid dictionary-observation/three-metric preparation
on its actual runtime account. It does not obtain or refresh a consumer stamp.

The native dictionary owner authenticates tag2 registration, current backing,
and allocated capacity before prefix access. SOURCE-only registration gains a
capacity word, updated with backing replacement under that owner; ordinary
dictionary header64 and registry word8 remain unchanged. Birth reservation is
19 fixed fields plus entry fields, with bytes computed from the actual record.

The nonwaiting lock order is dictionary owner then region owner, including
bound observation and retirement. Operation17 pays current dictionary
observation plus operation9 region bound plus256 bridge work. Fields and bytes
are zero. Region entry revalidates its current bound before lookup. A refused
lock, stale allowance, wrong region/generation, active lease/ticket, wrong slot
or exhausted epoch causes no store or epoch advancement.

The region helper requires an actual same-region source allocation and exact
shape1 slot `[offset,8,2,4]`. It holds both owners through the indivisible store
and epoch increment, without allocation, callback or account reservation. Old
operations7/8/9 reject dictionary slots. The C-owner-only helper is not a raw
SOURCE FFI authority.

Compiler nominal evidence remains separate: typed containing-Struct descriptor,
private token5, actual Dict key/value and birth recipes, backend type snapshots,
and emitted/final-link seals are prerequisites. Physical row4 is not a nominal
type certificate. Actual caller, pin, HIR query and full SOURCE execution remain
open dependencies.

Fixtures cover the actual Root/Dictionary/Child path, raw/tagged Struct values,
alias Stale behavior, same-value and replacement writes, rehash, foreign and
ordinary dictionaries, malformed capacity/backing, old-operation refusal,
active leases, fuel-one-short, retirement, and shared facade account effects.
They are authored assertions, not passing evidence.
