<!-- codex-research -->
# Domain research: environment-optimized dynamic libraries

**Feature scope.** Select and safely execute an implementation of a logical
library/provider that is optimized for the current CPU, operating-system
execution state, GPU device, or JIT executor. The feature includes native
dynamic libraries, SMF-packaged providers, JIT materializations, and optional
device programs; it does not make an artifact portable merely by changing its
filename or container.

**Research date.** 2026-09-07. External pages were checked against upstream
primary documentation on this date. The repository evidence is the saved
source ledger in
`doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md`
(entries R01–R18), not an assumption that all historical plans are shipped.

## Findings from primary sources

### 1. CPU levels are cumulative contracts, not width labels

The x86-64 psABI defines baseline, x86-64-v2, v3, and v4 feature levels and
states that later levels include earlier features. It also requires the full
OS-enabled AVX state checks, including XCR0, before v3/v4 code is considered
usable. The ABI recommends placing optimized shared objects in hardware-capability
directories with a baseline fallback. This supports a catalog of sibling
artifacts, but does not authorize arbitrary optional extensions or a widest-is
always-best policy.

Primary source: [x86-64 psABI low-level system information](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex).

**Implication for Simple:** represent `required_features` separately from
`optional_tuning` and vector-width preference. The baseline loader/facade must
remain baseline-safe; admission must check the complete CPU/OS contract and
retain a truthful scalar or baseline fallback.

### 2. Function multiversioning is useful inside a provider, not a complete
cross-platform deployment model

Clang's `target` attribute changes code generation for an individual function,
while `target_clones` emits several versions and resolves them at runtime. A
default fallback is required. On targets with GNU IFUNC, the resolver runs at
load time. This is a strong implementation technique for a native provider,
but its ABI, resolver, and toolchain support are target-specific.

Primary source: [Clang Attribute Reference: `target` and `target_clones`](https://clang.llvm.org/docs/AttributeReference.html#target-clones).

**Implication for Simple:** permit internal multiversioning where the native
backend supports it, while keeping provider selection, artifact identity,
lifetime, and typed ABI at the shared catalog boundary. Do not require IFUNC
for SMF, Windows, macOS, SimpleOS, or browser/Wasm placements.

### 3. Mature SIMD libraries make implementation choice observable

simdjson documents runtime implementation selection and exposes the selected
implementation; simdutf maintains separate architecture implementations and a
fallback. These projects demonstrate that dispatch must be benchmarked and
observable rather than inferred from a build flag. Their parsing semantics do
not establish Simple grammar correctness.

Primary sources: [simdjson implementation selection](https://simdjson.org/api/4.6.4/md_doc_2implementation-selection.html)
and the [simdutf project](https://github.com/simdutf/simdutf).

**Implication for Simple:** keep a semantic reference provider, record selected
provider identity, and compare scalar/vector results on malformed inputs,
Unicode boundaries, tails, and small workloads. A successful vectorized build
is not evidence that the vector implementation was executed.

### 4. JIT code requires explicit ownership and removal

LLVM ORC models symbols in JITDylibs, uses an ExecutionSession for lookup and
synchronization, and uses ResourceTrackers to remove materialized code. ORC
provides resource lifecycle primitives; it does not itself prove application
quiescence, CPU compatibility, ABI compatibility, or semantic equivalence.

Primary source: [LLVM ORC design and implementation](https://llvm.org/docs/ORCv2.html).

**Implication for Simple:** treat a JIT provider as a generation with exact
target features, backend/compiler digest, ABI, dependencies, and numerical
policy. Publish only after validation; pin in-flight calls and retire code
only after calls, callbacks, and dependent sessions are drained.

### 5. Vector capability includes OS/thread state

Linux AArch64 reports SVE through HWCAP, and SVE vector length is tracked per
thread and can be changed through `prctl`. Linux's RISC-V hardware-probing
interface queries features over a CPU set and can return the intersection for
boolean capabilities; vector execution also has a separate per-process control
interface. Compiled-in ISA support is therefore not sufficient runtime proof.

Primary sources: [Linux AArch64 SVE userspace interface](https://docs.kernel.org/arch/arm64/sve.html),
[Linux RISC-V hardware probing](https://docs.kernel.org/arch/riscv/hwprobe.html),
and [Linux RISC-V vector support](https://docs.kernel.org/arch/riscv/vector.html).

**Implication for Simple:** capability snapshots need architecture-specific
predicates, usable state, CPU-set/affinity scope, and (for SVE) vector-length
contracts. Unknown or unverified state must retain the baseline provider. A
heterogeneous process must bind a provider either to common capabilities or to
a pinned worker domain whose contract is explicit.

### 6. GPU admission is supported-and-enabled, not device-name matching

Vulkan distinguishes physical-device feature support from features enabled at
logical-device creation. Unsupported features cause device creation failure;
limits, formats, extensions, queue behavior, and resource layouts are
additional compatibility inputs. The Vulkan documentation also describes
device/driver identity used by pipeline-cache consumers. CUDA's compiler
driver documents separate host/device compilation and architecture-specific
device image bundles.

Primary sources: [Vulkan features](https://docs.vulkan.org/spec/latest/chapters/features.html),
[Vulkan limits](https://docs.vulkan.org/spec/latest/chapters/limits.html),
[Vulkan physical-device identity](https://docs.vulkan.org/refpages/latest/refpages/source/VkPhysicalDeviceIDProperties.html),
and the [CUDA compiler driver](https://docs.nvidia.com/cuda/cuda-compiler-driver-nvcc/index.html).

**Implication for Simple:** GPU provider descriptors must include API/code
format, actually enabled features, limits, queue/resource requirements, and
device/cache identity. A GPU provider is not a higher CPU SIMD tier; selection
also depends on residency, transfer cost, queue occupancy, and completion/
retirement evidence.

### 7. Dynamic loading has process-lifetime and search semantics

The Linux `dlopen(3)` contract covers loader search order, reference-counted
handles, symbol lookup, and constructors/destructors. A loader adapter must
make dependency search, ABI ownership, initialization, and close/unload
behavior explicit; merely resolving a symbol does not prove a typed provider
contract or safe retirement.

Primary source: [Linux `dlopen(3)`](https://man7.org/linux/man-pages/man3/dlopen.3.html).

**Implication for Simple:** keep native loading behind the existing adapter,
validate inert metadata and dependency closure before mapping, resolve typed
facets before publication, and keep allocator/TLS/unwind/callback ownership
consistent across the host and library.

## Cross-domain synthesis

The robust abstraction is a **catalog-selected sibling provider**:

```text
logical provider request
  -> capability snapshot + policy limits
  -> candidate catalog and dependency validation
  -> typed ABI/facet check
  -> native, SMF, static, or JIT adapter
  -> generation-pinned binding
  -> execution receipt and later retirement
```

Four axes must remain independent:

1. host execution environment (where control code runs),
2. target code-generation profile (where generated code may run),
3. artifact placement (static/native dynlib/SMF/JIT/contained worker), and
4. workload execution policy (reference, hybrid, resident GPU, or auto).

This separation prevents an AVX512 build host from contaminating a baseline
application, prevents an SMF container from being mistaken for executable
proof, and prevents GPU API support from being mistaken for enabled feature or
scene-semantic support.

## Repository evidence and open gaps

The saved local ledger reports these current constraints: SIMD detection and
intrinsics in `src/compiler/30.types/simd_platform.spl` are coarse or
placeholder (R01); runtime C probes already cover useful x86 checks (R02);
variant dispatch/probe/manifest modules are scaffolds without complete
requirements, digests, or safe loading authority (R05–R07); the provider and
aspect lifecycle modules supply boundary and generation patterns but not full
signature/admission proof (R08–R10); `runtime_dynload.c` already owns hosted
GPU loading (R11); and SMF documentation distinguishes registry/session
validation from executable mapping (R12). The shared frontend and automatic
profile seam still need an insertion point and implementation (R13–R14).

The first implementation must therefore close, with executable evidence:

- exact feature/state admission and baseline fallback;
- typed ABI and transitive dependency validation;
- artifact digest/cache identity and invalidation;
- generation pinning, unload/retirement, and callback safety;
- parser/scalar equivalence and actual selected-kernel evidence;
- GPU enabled-feature/resource/completion evidence where GPU is selected;
- explainable `prefer`, `require`, and `max` policy semantics.

No measured speedup, supported platform, native instruction emission, or GPU
execution claim should be promoted until the corresponding artifact and runtime
receipts exist.

## Source ledger

### Repository ledger consumed

`doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md`
is the pinned local audit and contains R01–R18 paths, inspected ranges, and
the canonical repository commit URL. Its recovered predecessor plans are
historical context only; current source findings above take precedence.

### External primary references

| ID | Primary source | Mechanism used |
|---|---|---|
| E01 | [x86-64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex) | cumulative CPU levels, XCR0 checks, hwcaps fallback |
| E02 | [Clang attributes](https://clang.llvm.org/docs/AttributeReference.html#target-clones) | function target attributes and clones |
| E03 | [simdjson selection](https://simdjson.org/api/4.6.4/md_doc_2implementation-selection.html) | observable implementation dispatch |
| E04 | [simdutf](https://github.com/simdutf/simdutf) | architecture families and fallback |
| E05 | [LLVM ORC](https://llvm.org/docs/ORCv2.html) | JIT symbols and resource removal |
| E07 | [CUDA compiler driver](https://docs.nvidia.com/cuda/cuda-compiler-driver-nvcc/index.html) | host/device compilation and image bundles |
| E08 | [Vulkan features](https://docs.vulkan.org/spec/latest/chapters/features.html) | supported versus enabled features |
| E09 | [Vulkan device identity](https://docs.vulkan.org/refpages/latest/refpages/source/VkPhysicalDeviceIDProperties.html) | compatibility identity for device caches |
| E11 | [Linux AArch64 SVE](https://docs.kernel.org/arch/arm64/sve.html) | HWCAP and per-thread vector length |
| E12 | [Linux RISC-V hwprobe](https://docs.kernel.org/arch/riscv/hwprobe.html) | CPU-set hardware capability queries |
| E13 | [Linux RISC-V vector](https://docs.kernel.org/arch/riscv/vector.html) | vector execution control |
| E14 | [Linux `dlopen(3)`](https://man7.org/linux/man-pages/man3/dlopen.3.html) | dynamic-loader lifetime/search semantics |
| E15 | [LLVM `llvm-readobj`](https://llvm.org/docs/CommandGuide/llvm-readobj.html) | machine-oriented JSON object metadata, sections, symbols, relocations, stdin input, and exit status |
| E16 | [LLVM `llvm-objdump`](https://llvm.org/docs/CommandGuide/llvm-objdump.html) | disassembly and raw instruction-byte presentation by object/section/symbol |

The ledger intentionally favors standards, vendor specifications, operating
system documentation, and project-owned implementation documentation over
secondary summaries.

LLVM documents `llvm-readobj` JSON as intended for machine consumption and
provides independent switches for headers, sections, section data, symbols, and
relocations. It also supports stdin with `-`. `llvm-objdump` is a separate
disassembly surface and can include or suppress raw instruction bytes.
Simple should therefore normalize readobj facts first and treat objdump as a
second correlated stream. Tool version, exact executable digest, arguments,
exit status, bounded output digests, and input artifact digest all belong in
receipt identity; successful exit alone is insufficient.
