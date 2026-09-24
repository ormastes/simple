# Phase2 host-GPU loader: main lane evidence

Status: focused main-lane cycle3 PASS; combined integration, final review and
canonical Phase2 runner remain pending. No hardware GPU, compiler-matrix or
Phase3 admission claim is made. No full runner/bootstrap/push was performed.

Baseline: `e6ffda6849e6aa7fe01a7d23ddc71e9773286532`.
Partition: `phase2_gpu_loader_abi_2026-09-23.md` (79 exports including the
checksum export exposed by enabling the dynload owner).

## Cause and bounded change

The failed Phase2 runner selected the Rust native-project `host-gpu` core-C
composition, but that composition did not compile `runtime_dynload.c` despite
its contract. The source-matched hosted Rust archive does not supply GPU
exports. The loader itself also lacked the additional public ABI adapters.
The capped linker report showed 20 names; retained-object census found 78
distinct names, then dynload-owner composition exposed the 79th checksum.

The host-GPU builder now includes the provider loader and its admission header
in compilation/fingerprinting, with `SIMPLE_RUNTIME_DYNLOAD_OWNER=1`. Other
core-C and hosted composition modes retain their original selection. No CUDA
or Vulkan backend implementation is statically added. The optional provider
lease/admission remains authoritative; unavailable and invalid inputs fail
with their canonical sentinels.

Main owns 29 exports, byte marshalling, and registry-checked signed-integer
array transfer helpers. `rt_cuda_module_get_function` decodes boxed Simple
text; it cannot assume the text-span expansion used by other CUDA externs.
Packed-byte arrays now use the checked byte accessors, avoiding double
unboxing. Vulkan scalar/text, readback and pipeline adapters are separate
reviewed sidecar ownership partitions.

## Reproduction and checks

Checker: `scripts/check/check-phase2-gpu-loader-abi.shs`.
Native fixture: `test/fixtures/native/phase2_gpu_loader/main.spl`.
Synthetic provider/harness: `test/02_integration/runtime/phase2_gpu_loader_abi.c`.
Untracked evidence root: `build/native_probe/phase2-gpu-loader`.

The checker tests valid provider forwarding with argument/byte verification,
missing required exports, rejected provider ABI, no provider, malformed and
packed arrays, invalid bounds, boxed literal/computed text, and copied text
after unloading. It checks that the executable has no linked provider edge.
The baseline loader fails the same focused link with missing CUDA/Vulkan
adapters (cycle1/baseline-link.log).

1. Cycle1: initial focused C proof and baseline-red link PASS, 3.14 seconds;
   maximum process RSS 162430976 bytes, sampled tree peak 151344 KiB.
2. Cycle2: expanded 29-export fixture plus actual native Simple archive failed
   to link because the minimal fixture omitted canonical `runtime_legacy_core`
   and its `spl_panic` export. This was fixture composition, not a production
   provider defect. No generated stub was used.
3. Cycle3: adding the canonical legacy object made all three provider scenarios
   and actual Simple-boundary checks PASS, 2.96 seconds; maximum process RSS
   161071104 bytes, sampled tree peak 151456 KiB. No unchanged baseline gate was
   repeated. This exhausts the main lane's three verify/fix cycles.

All bounded checks used cap5859375 KiB, observer interval100ms and LLVM23;
cycle3 recorded exit0, observer_errors0, quiescent1. RSS is sampled enforcement,
not a kernel hard memory limit. These totals are focused fixture build/run
costs, not a claim about physical GPU throughput.

## Native provenance

Producer: admitted Stage2 `simple`, SHA256
`0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`.
It compiled the single-module fixture with `native-build --emit-archive
--no-mangle --entry-closure --threads 1 --runtime-bundle core-c-bootstrap`,
its immutable Stage2 runtime capsule, a private phase-bound cache, and
`SIMPLE_NO_STUB_FALLBACK=1`. Archive build passed in 0.27 seconds.
The invocation also set `SIMPLE_NATIVE_BUILD_RUST=1`: this is an actual native
Simple ABI fixture through the admitted executable's Rust-delegated archive
route, not proof that the self-hosted Simple frontend produced the archive.

Native archive SHA256:
`1f3712dd0a347cc193211812c71883cb2ebf12b3bd8efe956f14eae700a91925`.
Cycle3 executable SHA256:
`47fe90c6fc12cf972db6c1990755cc4e4e753de9e02efeff9af52bb7c5612615`.
Runtime dynload source SHA256 at that check:
`e0aeb8c4bf42b2672ccad875872708f9673ba32f20157f257515ca7290cd5f28`.
Runtime native source SHA256 at that check:
`fb631bcbddc07195b4b5edc854950aad91889324aaab733cd6b8be0296425816`.

## Remaining gates

- Main/shared static review found a provider callback type mismatch in
  `rt_cuda_module_load_data`: pointer/u64 must adapt to canonical i64/i64.
  The dedicated ABI correction agent owns its fix/proof; the old forward is
  retained until that reviewed patch arrives. Thus cycle3 runtime success
  does not establish final source approval. Checker non-Darwin libdl linkage
  was corrected statically.
- Reviewed sidecar fragments were integrated with identical patch IDs:
  S `0f0dcc44ea5` -> `1d21646074c`, A `e1044893814` -> `20f647fc0cd`,
  P `0b84b2a9af0` -> `36eb5709088`. Their files do not overlap each other
  or the main production edits. Three includes and explicit Rust fingerprint
  inputs are added; pure-Simple runtime hashing already covers every .c/.h.
- One new combined 79-symbol focused integration gate against retained runner
  objects remains unexecuted. The checker received independent static PASS
  after fixing blank-line handling and propagating nm/awk failures; static
  approval is not execution evidence.
- Rust native-project archive-selection regression execution in a serialized
  parent-authorized Cargo slot; the test is added but not yet executed here.
- Scalar sidecar native proof currently exposes a distinct compiler conversion
  defect for `rt_vulkan_get_last_error`; its C-string ABI must not be changed to
  conceal that defect.
- Source-matched canonical Phase2 full CLI/test runner, compiler tests and all
  supplemental specs belong to the parent-controlled bootstrap lane.
