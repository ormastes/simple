# Guarded optional reference binding retains nullable type and misclassifies builtin `len`

Status: FIXED (P1, narrow guarded optional-reference binding) — 31 focused Rust unit tests, 28 focused native checks, and Astra-reviewed MIR mechanism evidence pass. No Phase 2/3 qualification is claimed.

## Scope and source evidence

The source diagnosis is now in guarded optional-reference binding in the Rust
seed HIR lowering/type-resolution path, rather than an LLVM `inline_len`
boxing defect. A guarded binding retains a nullable type where the value in the
guarded body should have the non-null inner type. This causes builtin `len` to
be misclassified in the resulting typed MIR path; the resulting comparison can
pair an unboxed length with a boxed integer and reach `rt_native_eq` with
incompatible representations. The compile-only evidence below observes that
comparison shape but does not, by itself, prove the upstream cause.

The Astra-reviewed repair is a four-owner HIR change: optional provenance
tracking (`HashSet` and `register_optional`), a central optional type resolver,
and guarded inner-binding handling for Array, String, Struct, and Enum values,
with regression tests. The current seed build and native results are recorded
below. Astra reviewed the later native campaign's offline mechanism receipt
`D5F3077A70BAC048221F7025E2303A88536F0E02EBEC0B5DA5760B2B8490D719` and
approved its scoped finding. The corrected focused Rust optional-binding test
run passed; do not infer an LLVM `Any`-destination fix from the earlier
proposal.

## Current seed and native campaign

The current source patch SHA256 is
`DC039428B99305C7DC396B96D3FD78F2C921D9BABBE0EB7BEB4D895C3A856D39`. Its
immutable seed build record is
`C:/dev/p3new/s2_optional_binding_seed_20261103/attempt_02/artifact.sdn`
(SHA256
`415F8332CAE18D80916D9FA73D48605AEC6A6C44F59EA8136EC911E9F0465E87`), which
records uncertified seed SHA256
`D18AE3386F580A96530FD6CE8DB5164DDA55435F04AE3CDE1AC46F1743288E9A`, rc 0,
235.0 seconds, and 3.87 GiB peak process-tree RSS. The native campaign at
`C:/dev/p3new/tuple_abi_optional_verify_20261103/attempt_01` reports
`NO_COMPLETE_NATIVE_PASS` (result SHA256
`6484AE58E8223E77DA5F582214A6F2E5F0C57C88F98262DA36EBCE1FE9D7C6E6`):

- The original-form guarded optional-array case passed all 20 checks; result
  SHA256 `AC93E43F33B96D3E9E28D1AD84D9D9EB9955117F40CC45AC08516839F7B7619B`.
- The focused guarded-optional-reference case passed all 8 checks; result
  SHA256 `75DBD777CEF860F5E7BD89554AB50F6494A7633536B36C5E0745C43999A3FB08`.
- The generic optional-tuple case failed before its 24-check end marker with
  `panic: tuple ABI probe failed: true optional bool projection`; result SHA256
  `BB024BFBECF813FC1350612EE81BFEF2010F0E95B807EA6E62B314B92A937A3C`.

The first two cases therefore provide 28 passing focused native checks for
guarded optional inner binding on this seed. The generic optional-boolean
failure is a separate finding and is not counted as a guarded-binding pass or
as proof that the tuple getter declaration is defective. Offline disassembly
shows the true input boxed through `rt_value_int`, while optional projection
uses `rt_value_as_bool`, which accepts the tagged special boolean form; this
explains the observed failing path but does not establish a production fix or
shared cause. Keep generic tuple/boolean behavior, the existing candidate AV,
and LayoutAttr requalification separately OPEN.

The SSpec wrapper was statically reviewed but was not executed by the
self-hosted runner. Native execution evidence above came from a bounded
PowerShell campaign.

The initial `optional_` selection produced 30 passes and one failure caused by
the test's parameter offset. A corrected exact-test retry, with test-only
source diff SHA256
`C5F6145293B57237D054136091EA360C8597F329ADF297AB522A8612D3D38405`, passed
that remaining test in the Rust test harness using corrected `cfg(test)`
source. The immutable native D18 seed remained unchanged; no seed rebuild or
30-test rerun was performed. The retry result SHA256 is
`2F8207C35ACCDDA5F0B1A405FF3548F6F7BC99EDB1EDFFA2AFAF1F93F0A14803` and its
input pin SHA256 is
`26B4C518DBC51E83D9DDA1999DC5F9B652D36B53C2AE1116E5941F42DF4C8A4C`.
Together, the 30 original passing tests plus this retry yield 31 unique focused
tests passing, including all five new optional-binding tests. No Phase 2 or
Phase 3 qualification is claimed. The separate generic optional-boolean
failure remains tracked in
`doc/08_tracking/bug/seed_enum_bool_payload_boxed_as_int_2026_11_03.md`.

The earlier two LLVM-owner changes in `functions.rs` and `functions/calls.rs`
are withdrawn and archived; their source hashes and the supplemental fixture
hash are historical provenance only, not the current owner or accepted
correction:

- `functions/calls.rs` SHA256
  `923488079E4791BA71D38C9D85626A7D1F3E7AAE196FD5B53972410FC3BC3389`
- `functions.rs` SHA256
  `823EE46E9FB0967776CC7BDFA63797FEAA40F113DB784F99AF65C839CDEEE01F`
- Supplemental fixture SHA256
  `5A6CA7F73AE04A405D0DE273F66ACEA783A4301E6E95010155EA77BE0CCB517A`

The withdrawn LLVM experiments do not alter the current HIR repair status;
their build and failure limits remain historical. The FIXED status here is
limited to guarded optional inner binding, with no broader qualification.

## Historical withdrawn LLVM proposal — build only

An immutable seed build for the withdrawn LLVM proposal was produced from source head
`f9025d3235a82bd5e48e9f415315dd1b765971ae` plus source diff SHA256
`F0C048FC743EF355607D1692C9E81C3EE2270617C46DD8185D295728B64A6928`
(branch `work/seed-inline-len-tagging-20261103`). The retained artifact record
`C:/dev/p3new/s2_inline_len_seed_20261103/attempt_01/artifact.sdn`, SHA256
`77603F463DFF1D247C7E5A5AB714FEC3D2231AC2A1057230CFCA7F48E3BED406`, records
build status `built_uncertified_seed`, rc 0, elapsed 274.1 seconds, peak tree
RSS 3.9 GiB, and immutable executable SHA256
`54D6945ED0C879EA4F019C2FD5C850B2109A478090C2DBDF84D7C5D3EEC96C51`.
The input pin record SHA256 is
`245ADE21F05798C27B2825003DB1E2F09FD5BC552AD104C5205BFC7F0D109D26` and the
result record SHA256 is
`5728ED7DCFCFEE66D36812E1307470E0FABD8025D23B479F5350E921DCF097AC`.
This establishes build completion for the withdrawn LLVM proposal only. It is
not a build of the current guarded optional-reference repair; its executable
does not qualify that repair. The current repair's later seed, tests, and
verification are recorded above.

## Historical LLVM trial and compile-only MIR capture

A later fixed-native one-binary attempt at
`C:/dev/p3new/tuple_abi_native_verify_20261103/attempt_01` records
`NO_COMPLETE_NATIVE_PASS` (top-level result SHA256
`11FB0ED43AAA386629ED6B0CEEE5E6A45F66F5D45C8E065C2C55C2B7A64601D9`). The
original tuple ABI candidate failed: it saw its begin marker, exited 1 before
its pass marker, and reported `panic: tuple ABI probe failed: array payload
length` (case result SHA256
`FE945A933793E4D920C3CD6503DBB6F032EC3E640A61034C28E16FFD861BE396`). The
separate supplemental inline-length fixture associated with the withdrawn
LLVM proposal passed natively (case result SHA256
`41BC78E3A9AD7092BBE34949710585236C8073748121FBDE66633F395A10DFD9`). That
pass is useful fixture evidence, but does not prove which conversion path was
exercised or establish that the withdrawn LLVM proposal repairs the mismatch.
Neither case qualifies Phase 2 or Phase 3; this historical trial does not
establish any broader status.

A separate compile-only capture at
`C:/dev/p3new/tuple_abi_mir_diag_20261103/attempt_01` completed with rc 0 in
15.6 seconds and 0.18 GiB peak process-tree RSS; its status explicitly says no
executable was run. This historical compile-only receipt SHA256 is
`DF1692B194D43D7A590EDBD44689A8D4970381E81B6898C6300E18878D95F0B1`. It records
MIR `MethodCallStatic` `len` with receiver VReg(144), destination VReg(146),
and receiver type ID 71, followed by integer literal 2 boxed to VReg(148) and
`rt_native_eq(VReg(146), VReg(148))`. Its source-derived type-map review says
the `len` result has no vreg type entry (not `TypeId::ANY`); the receipt does
not assign a semantic name to type ID 71 or explain why upstream lowering
selected `rt_native_eq`. This is an observed raw-versus-boxed comparison shape
consistent with the refined guarded-binding diagnosis, but it does not alone
prove that diagnosis or the repair. In particular, the `len` result itself
has no type-map entry, so an LLVM patch conditional on a known `Any`
destination does not address the upstream missing/non-null type information.

Together, these outcomes do not establish that the FFI declaration hypothesis
caused the tuple panic, that the supplemental fixture exercised the failing
comparison, or that both failures share a cause. The earlier LLVM patch remains
withdrawn. The later Astra-reviewed guarded optional-reference HIR repair and
its scoped verification are recorded above.

## Mini attempt and limits

The retained experiment at
`C:/dev/p3new/tuple_abi_mini_20261102/attempt_01` is not a run of the proposed
`inline_len` source repair. Its comparison record SHA256 is
`25DC8ED05C7EA34616873E5E4FDDB39F1BEF4A10D4B05B52C12372E0A5B5028C` and says
`NO_VALID_DIFFERENTIAL_PASS`. Both baseline and candidate failed before the
20-assertion completion marker (`completed_20_seen=false`): baseline exited
`-1073741819` (`0xC0000005`), while the candidate exited 1 with
`panic: tuple ABI probe failed: array payload length`. This is not evidence
that the withdrawn LLVM proposal works or that the two failure modes share a
cause.

The mini changed only the Simple declaration of `rt_tuple_get` from `i64` to
`Any?`; the C runtime declaration is `int64_t rt_tuple_get(...)` and its
implementation returns the raw tuple slot. This remains a separate FFI
representation hypothesis, not a confirmed independent bug. The mini receipt
SHA256 is
`37ECEBB5E9F9537BB170481EC1BF03D3514F42E84E4665AE923A04727756801F`;
baseline and candidate fixture hashes are respectively
`7E3B5B223EFE6253C9A7001D8BBC478B012AD8419B05251E7ACC17CEA2564320` and
`1EC3B9195BF6F20ADF76F808D3636B7103FDA5F14F7A67FF32ADAF871261A746`.

The existing Cranelift inline-length tracking issue is a distinct backend and
tag-space problem. The existing candidate native-smoke access-violation record
also remains OPEN; this report does not merge its failures with the guarded
optional-binding diagnosis or assert a shared cause.
