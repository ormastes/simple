# Phase2 host-GPU loader: main lane evidence

Status: focused main-lane cycle3, combined 79-export link/census, targeted
Rust host-GPU composition test and independent integration review PASS.
Canonical fixture corrections now pass the merged source audit. The corrected
S/main fixtures await rebuilt-producer execution; canonical Phase2 runner
remains pending.
No hardware GPU, compiler-matrix or
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

- Independent final Astra integration review passed after the two execution
  gates, without rerunning them. Working direct-env audit PASS, spec-layout
  executable count0 and whitespace diff check PASS.
- Source-only SFFI audit failed, and exact-base comparison disproved an
  inherited-warning explanation: e6ffda6 has 377 signature-variant symbols
  and 3504 migration entries (PASS); merged source has 400 and 3487 (FAIL,
  unchanged variant limit399). The 23 added variants come from new native
  fixtures redeclaring canonical boolean-return externs as i64, plus array
  element-type differences; private C headers are not scanned. For example,
  canonical `rt_vulkan_shutdown()->bool` is redeclared `()->i64` in the scalar
  fixture. Dedicated owners corrected the fixture declarations/assertions and
  synthetic boolean results, without production changes or a threshold rise.
  Reviewed S/A/P corrections were integrated as `b4110069af1`, `8f93ff332ff`
  and `d1bc875e16f`, with identical original patch identities. Main's two-line
  boolean declaration/assertion correction received independent static PASS.
  The single merged audit retry passed all4 assertions and emitted11142
  source-only warning rows, admission=absent, inventory_rc=0 (retained
  `sffi-canonical-audit.log` and `sffi-canonical-backlog.tsv`).
  A/P supplied fresh corrected-fixture native proofs in their signature-repair
  lanes; S/main corrected-fixture execution explicitly awaits the rebuilt
  producer/full Phase2. The parent prohibited a stale-producer rerun.
  No threshold was weakened and no already-green native/Cargo gate rerun.
  Retained comparison tables: `sffi-base-{contracts,symbols}.tsv` and
  `sffi-merged-{contracts,symbols}.tsv`, with matching inventory logs.
- Main/shared static review found a provider callback type mismatch in
  `rt_cuda_module_load_data`: pointer/u64 must adapt to canonical i64/i64.
  Dedicated reviewed correction `c66adda401f` was integrated as `c3ab99a1aab`
  with identical patch identity; the obsolete main macro was removed.
  Exact adapter SHA256 is
  `cc1d1a81c641069ab79cf9ecf7a4092da3f08325a9b387503494b19ac58f37f7`.
  Its separate evidence covers sanitizer red/green and native Simple ABI, not
  physical GPU or full solver qualification. Checker non-Darwin libdl linkage
  was corrected statically.
- Reviewed sidecar fragments were integrated with identical patch IDs:
  S `0f0dcc44ea5` -> `1d21646074c`, A `e1044893814` -> `20f647fc0cd`,
  P `0b84b2a9af0` -> `36eb5709088`. Their files do not overlap each other
  or the main production edits. Three includes and explicit Rust fingerprint
  inputs are added; pure-Simple runtime hashing already covers every .c/.h.
- Scalar fixture followup `924efdd9b1f` was integrated as `5c32f636772`, preserving
  baseline/custom-header probes after production fragment inclusion; its
  independent review was static only, without repeating passing checks.
- The combined 79-symbol link/census gate ran exactly once and passed in
  2.07 seconds: maximum process RSS 162988032 bytes, sampled tree peak
  158448 KiB, observer_errors0 and quiescent1 under cap5859375 KiB.
  `integration79/source.sha256` and `source-verification.txt` bind the before/
  after runtime/header/composition/manifest/retained-runner sources;
  `artifacts.sha256` binds the resulting executable. Both missing-symbol files
  are empty: all 119 distinct retained runner GPU references are satisfied.
  No provider dylib is directly linked. This tests all 79 export
  addresses and retained runner GPU-symbol closure, not the runner's other
  dependencies, its caller ABI correctness or GPU execution.
- The Rust archive-selection regression ran once in the parent-authorized
  serialized slot and passed: exactly 1 test, 0 failed, 4057 filtered out.
  Total elapsed 40.41 seconds; maximum process RSS 3468279808 bytes, sampled
  tree peak 3436992 KiB, observer_errors0/quiescent1 under cap5859375 KiB.
  Evidence: `cargo-composition.log`, `cargo-composition-rss.env` and retained
  `cargo-composition.sh` (SHA256
  `74263ba93c9eb99ca4eb4cbbe095cbb52cad5b8f54b6f156f65f5190cc106891`).
  The private APFS-cloned cache leaves the prior lane's artifacts untouched.
  This verification-only build used jobs1, opt-level0, LTO=false, codegen256,
  debug0 with pinned LLVM23/nightly, locked/offline dependencies and no-stub
  fallback. It is not a production-profile admission. Existing nonfatal
  rust-objcopy/DYLD debug-stripping warnings remain in the log; no workaround
  or broader toolchain qualification is claimed.
- Scalar sidecar native proof currently exposes a distinct compiler conversion
  defect for `rt_vulkan_get_last_error`; its C-string ABI must not be changed to
  conceal that defect. Parent integrated its compiler fix separately in P0;
  this GPU change deliberately does not duplicate that compiler patch.
- Source-matched canonical Phase2 full CLI/test runner, compiler tests and all
  supplemental specs belong to the parent-controlled bootstrap lane.
