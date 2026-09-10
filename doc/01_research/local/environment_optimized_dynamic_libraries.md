<!-- codex-research -->

# Local research: environment-optimized dynamic libraries

**Audit basis:** the saved proposal `doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md` and the current working tree. The proposal records revision `da48c000...`; the current checkout is `ab87f91b...` and has unrelated uncommitted changes. This is a source audit only; no build, benchmark, device run, or release claim is made.

## Findings

| Area | Current evidence | Gap / implication |
|---|---|---|
| Runtime CPU SIMD | `src/runtime/runtime_simd_dispatch.h:124-152` checks AVX2 plus OS XMM/YMM state (`XCR0`); `src/runtime/runtime_simd_dispatch.c:68-120` exposes x86/Arm/RVV probes. `src/runtime/runtime_simd_utf8.c:548-601` initializes scalar slots and upgrades to AVX2, SSE2, or AArch64 NEON. | This is usable runtime dispatch evidence, but it is not a catalog of exact x86-v2/v3/v4, AVX-512 subfeatures, SVE vector-length contracts, or artifact admission policy. Keep it as a probe source and avoid adding a competing authority. |
| Simple SIMD model | `src/compiler/30.types/simd_platform.spl:48-116` parses `/proc/cpuinfo` and collapses AVX-512 to `avx512`; `src/lib/nogc_sync_mut/simd/host_cpu_config.spl:14-41,127-203` uses one numeric rank across x86/Arm and models SVE as 256-bit. | The proposal’s concern is verified: feature legality, architecture compatibility, OS state, and vector length are not represented separately. `TierClamp.clamp` at `host_cpu_config.spl:274-281` compares ranks without an architecture check, so an x86 request can remain effective on an Arm maximum. |
| Variant routing | `src/lib/nogc_sync_mut/simd/variant_dispatch.spl:16-30,72-156` creates suffix names and an eight-slot table; `loader_variant_probe.spl:7-30,49-99` probes fabricated `.so` paths and chooses the first marked-found slot. | This is scaffold-level routing, not safe loading or eligibility. It does not validate exact requirements, ABI/semantic identity, artifact digest, or dependency closure. A missing preferred file must not make an unverified sibling eligible. |
| Variant manifest | `src/lib/nogc_sync_mut/simd/variant_manifest.spl:14-47,60-126,197-237` stores only platform/tier/path/size/default in eight flat slots and serializes with colon delimiters. | There is no exact feature set, OS state, target ABI, device requirement, or artifact identity in this record. Colon-delimited paths also need a platform-safe encoding before Windows drive paths are accepted. |
| Composition foundation | `src/lib/nogc_sync_mut/composition/types.spl:16-63` has provider/interface/binding records and an artifact digest; `source.spl:87-92,257-288` validates approved provider paths, kinds, digests, capability bits, and interface references. `provider_generation.spl:12-73,91-119` validates admission flags/digests and retains pinned retired generations. | These are reusable boundaries for a variant catalog and generation-pinned plan. They do not yet carry CPU/device predicates or select among environment variants. `SimpleProviderQueryResultV1` still has a deliberately zero implementation digest for the in-process compiler adapter (`src/compiler/80.driver/driver_provider_contract_v1.spl:70-84`). |
| Aspects / replacement | `src/compiler/99.loader/advice_binding_registry.spl:8-18,91-135` explicitly omits signature checks and the full state machine while providing slot patching. `aspect_lifecycle_gate.spl:5-11,63-112` serializes publication/pin operations; comments state the fallback lacks native concurrency evidence. | Reuse lifecycle/slot machinery only behind typed provider admission. Successful rebinding is not proof of ABI, semantic, trust, or generation compatibility, and the gate must not be put in token/pixel hot loops. |
| Parser insertion seam | `src/compiler/10.frontend/core/frontend.spl:6-48` is the shared compiler/interpreter parse facade and directly calls `compiler.core.parser` before interpolation/placeholder transforms. The current structural adapter (`src/compiler/10.frontend/structural_adapter/core_lexer_adapter.spl:1-27,120-125`) bridges the production `CoreLexer` into the shared byte-span contract; its receipt sets `oracle_verified: false` (`:89-91`). | A parser-provider seam can start at `core_frontend_parse`, but transformation ordering and reset/append/isolation must remain stable. The adapter is lexical, not a second grammar and not parity proof. Tree-sitter remains an outline parser/facade (`src/compiler/10.frontend/treesitter.spl:44-58`), not the full compiler parser authority. |
| Parser acceleration status | `src/lib/nogc_async_mut/structural/parse/runtime.spl:33-45` routes hybrid/GPU modes through the compatibility CPU path; `auto_profile.spl:22-29` always selects `Scalar` with `auto_profile_not_implemented_wave_1`; `parallel_lex.spl:32-47` returns `UnsupportedMode`. | Automatic SIMD/GPU selection, parallel lexing, and evidence-backed parser specialization are not implemented at this seam. Treat the proposal’s parser-only variation as future work, not current product behavior. |
| Native GPU registry | `src/runtime/runtime_dynload.c:47-50,72-77,169-224` owns CUDA/Vulkan/Metal paths, opens with `dlopen`/platform equivalent, then validates ABI/backend bits and required symbols. `doc/07_guide/lib/api/dynlib_api.md:115-144` documents unload/reload and explicitly says acceptance does not prove physical device execution. | This is the existing host-loader bridge to adapt to, not duplicate. Validation occurs after opening the candidate, so constructors/loader side effects are not prevented by metadata checks. Provider unload also requires callers to quiesce resources. |
| SMF/native distinction | `doc/07_guide/lib/api/dynlib_api.md:95-113` says registered SMF symbol values are not executable mapping evidence and host `.so` calls use a separate WFFI path. `src/lib/nogc_sync_mut/composition/cli_registry.spl:107-111` fails native/SMF dynamic query closed until process-callable admission is proved. | Keep metadata admission, symbol resolution, process-callable mapping, and actual execution as separate receipt states. A hosted native call cannot stand in for SMF execution evidence. |
| GPU kernel/queue | `src/lib/common/gpu/engine2d/kernel_registry.spl:1-15,110-170,236-251` provides per-operation/format/size slots, scalar oracle fallback, and sealed registration; its common-tier executor still always calls scalar oracles (`:244-251`). `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl:314-375` has packed admission/submission, but completion and retirement use `device_evidence_none` and carry explicit TODOs. | The registry is a useful typed slot shape and avoids one global SIMD level, but it is not proof that a selected provider executed. GPU resident placement, real fences, and resource retirement remain unproven at this queue seam. |

## Recommended local boundary

1. Make a bounded, versioned variant descriptor/catalog above the existing composition records. Eligibility must check architecture/ABI, exact usable CPU state, artifact/dependency identity, semantic facet, and (for GPU) enabled device features and resource limits before ranking.
2. Use existing runtime CPU probes and GPU registry adapters; do not create a second host loader. Keep native/SMF/JIT placement as separate adapters behind the same typed facet and generation lifetime rules.
3. Introduce parser variation at the shared frontend facade only after a provider preserves parser state isolation and interpolation/placeholder ordering. First require parity receipts against the existing parser; the current structural adapter explicitly does not provide that proof.
4. Keep auto-profile, parallel lexing, GPU device completion, and physical execution as explicit implementation/evidence gates. Current source contains seams and fail-closed fallbacks, not completed optimized execution.

## 2026-09-07 continuation: GPU execution-evidence audit

The implementation now includes an inert environment/device-program admission
adapter at `src/lib/nogc_async_mut/gpu/environment_variant_adapter_v1.spl`.
It proves exact provider/program/image/device/layout/lease correlation and
requires ordered fence, completion, and retirement identities before accepting
an execution claim. It intentionally initializes no device.

The existing runtime path still provides weaker evidence:

- `runtime_dynload.c` proves provider loading, ABI/backend compatibility, and
  required host symbol presence after load;
- `host_gpu_event_queue.spl` proves a process-local modeled packet lifecycle and
  payload identity, but its active backend handle is currently zero;
- queue device timing is host-derived, CUDA lacks stream/event identity, Metal
  lacks completion-token evidence, and Vulkan fence entrypoints are not exposed
  as a uniform provider submission token;
- `gpu_epoch.spl` correctly refuses to derive `device_execution_proven` from
  those routing facts.

Therefore the next integration seam is a typed provider-completion bridge from
an admitted provider generation and device-program image to the existing epoch
receipt. It must consume a real submission token, fence signal, device/driver
identity, negative control, and retirement evidence. The current compatibility
queue must remain routing-only until that bridge is supplied by a backend.

## 2026-09-07 continuation: first native SIMD proof boundary

The narrow x86 native path has connected MIR selection and byte encoders for
aligned `Vec8f` load/binop/store operations (`isel_x86_64.spl` and
`encode_x86_64.spl`), with golden VEX byte tests. This is stronger than a
target flag but still not end-to-end execution evidence. In particular,
`verification_ir.spl` classifies `Vec8f` floating-point semantics as
unsupported, and the C backend explicitly emits unsupported panics for f32x8
arithmetic. Existing unit tests therefore cannot establish a portable generated
library or parser SIMD implementation.

The first truthful executable proof must remain native-x86/AVX2-specific and
must retain: admitted host AVX/OS state, exact MIR fixture, emitted object
digest, inspected VEX instruction evidence, callable artifact identity,
executed result versus scalar oracle, and invocation receipt. It must not be
reported as parser acceleration until a parser provider uses that path and
passes normalized dialect parity.

## 2026-09-07 continuation: scalar parity fixture boundary

`test/01_unit/lib/structural/parse/parse_cpu_reference_spec.spl` provides a
real deterministic scalar runtime and receipt hashing, but only for a synthetic
four-class lexical DFA. Accelerated modes currently demote to that same CPU
implementation and compare its deterministic token hash. This proves bounded
lexical-runtime behavior and fallback truthfulness; it is not an independent
legacy-versus-canonical comparison and covers none of the full Simple, SDN, or
sosh grammars, AST/HIR nodes, interpolation transforms, or recovery diagnostics.

Consequently its `deterministic_hash` can be reused as one normalized lexical
component, but must never satisfy the parser promotion gate alone. Full scalar
parity needs independent implementation identities and generations, source and
grammar/action/schema identities, declared dialect coverage, token/span/node/
diagnostic digests, unsupported-region counts, and non-vacuous fixture counts.

## 2026-09-07 continuation: startup and configuration audit

Help/version argument handling and ordinary compile/native-build dispatch do not
directly initialize GPU services in the inspected source. Side effects begin at
explicit Engine2D/backend viability probes, `ComputeDispatch.auto`, browser
Vulkan setup, and Engine3D Vulkan paths. `Engine2D.list_backends` and deep
viability inspection are not observationally pure. There is no unified
provider/device initialization counter, so source structure is consistent with
lazy startup but cannot provide NFR-009 runtime evidence.

Existing configuration partially overlaps the proposal: `--cpu` /
`SIMPLE_NATIVE_CPU`, host SIMD probes, `--frontend-offload`, and its fallback
policy exist. Missing are a parser-provider selector, provider-level
`prefer`/`require`, parser CPU maximum plumbing, project configuration wiring,
and a full explain receipt. The existing frontend receipt reports only
requested/selected/reason/source; it does not bind provider, exact usable
features, limits, artifact digest, admission, or generation. A target-features
parser exists but is not wired end-to-end through native build.

The safe next step is a pure precedence/policy resolver producing typed inputs
for catalog selection. CLI and environment readers remain narrow adapters; the
resolver must apply administrator restrictions as non-overridable intersections
and keep host execution limits separate from generated target features.

## 2026-09-08 continuation: generated-code evidence producer audit

Repository-wide owned-source search finds the staged target-codegen evidence
types and transition validators only in `target_codegen_profile_v1.spl`; no
compiler backend imports or constructs the backend-acceptance, artifact,
emission, or execution evidence records. The parser SIMD contract consumes a
finalized receipt plus caller-provided inspection, and the native AVX2 proof
joins caller-provided golden, inspection, and execution records. Their evidence
digests must be nonzero but are not recomputed from backend-owned bytes,
disassembly, callable invocation, or scalar-oracle output at these seams.

Thus current code proves contract shape and rejection logic, not a
backend-authored chain of custody. The next policy-independent unit is an
owner-scoped producer colocated with the real backend/build driver. It derives
artifact identity from emitted bytes, inspection identity from the exact
artifact/tool/output, and execution identity from the pinned callable plus
input/output/oracle facts. Freely constructed evidence remains useful for
validator tests but cannot qualify generated SIMD execution.
## 2026-09-08 backend acceptance producer seam addendum

The existing `backend_feature_authority_v1.spl` is explicitly declaration-only:
its caller supplies a backend identity and feature words, and the module states
that it does not authenticate backend acceptance. It must not be used to advance
`ParserBackendTargetEvidenceOwnerV1` to an accepted or inspected stage.

The first concrete byte-producing seams are
`BuiltinBackendCompileAdapter.compile_aot_module`, which returns
`CompiledModule.object_code`, and the direct Cranelift adapter, which returns
`CodegenOutput.object` after reading the emitted object. The driver/backend
session boundary is therefore the correct issuer location: it can bind the
admitted backend session/provider generation, normalized compile options and
target, exact returned bytes, and terminal backend result in one operation.
Issuing evidence later from a filename, cache entry, feature declaration, or
caller-built `TargetCodegenReceiptV1` loses that chain of custody.

The next implementation slice should add a backend-result envelope owned by the
admitted backend session and consumed directly by the parser evidence owner.
It must keep requested features separate from backend-accepted features and
must report unsupported when the backend cannot confirm a requested feature.
Object production alone is not instruction inspection or execution evidence.

Further tracing found two prerequisites. `BackendSession` retains an admission
receipt and a mutable open/closed flag but has no owner-issued session generation
token. Also, `BackendProviderReceipt.features` and the dynamic ABI
`features_wire` describe the request; `BackendPluginBridgeEnvelopeV1` returns
status, result kind, payload, and diagnostics but no accepted-feature set.
Consequently neither builtin nor dynamic compilation can currently distinguish
“requested” from “backend explicitly accepted.” The dynamic extension must be a
versioned ABI addition, not reinterpretation of the V1 request field.

The builtin propagation audit found an earlier break: although
`create_builtin_backend_compile_adapter` receives `BackendPluginRequestV1`, it
constructs `BackendCompileOptions` without the request's `cpu` or `features`.
The retained `Codegen` therefore compiles with backend defaults. The AOT helper
accepts a separate `target_cpu`, but builds `TargetOptContext` from host AVX2 and
does not carry the plugin request feature list. `LlvmBackend` reconstructs
`LlvmTargetConfig` from target/default CPU, and `LlvmLibCodegenAdapter` likewise
uses portable numeric defaults. Thus current successful LLVM object emission
does not prove the admitted request's CPU/features were applied at all.

Acceptance work must first propagate normalized CPU/features into the concrete
LLVM target-machine configuration and preserve the effective configuration
returned by that path. Until then even recognized feature names remain Unknown.

The smaller-model boundary audit found that dynamic V1 is narrower still:
`backend_plugin_request_encode_v1` emits only the fixed 16-byte version, role,
and capability prefix. `runtime_backend_plugin.c` populates only those fields;
the target/CPU/features members declared by the C header are not transported.
The common `BackendPluginWireRequestV1` shape is not evidence that the runtime
bridge populated them. Preserve this frozen V1 behavior and add a separately
versioned V2 request/result wire.

The least-invasive builtin route keeps widely constructed
`BackendCompileOptions` unchanged. `BuiltinBackendCompileAdapter` retains a new
immutable plugin-only target context derived during admission and calls
plugin-specific LLVM/Cranelift entrypoints. Those entrypoints must return
provider-owned effective configuration evidence; compilation success alone
continues to produce Unknown.

## 2026-09-08 external inspection owner audit

The current host has `llvm-readobj` and `llvm-objdump` under the same local LLVM
installation. A direct sample confirms that `llvm-readobj
--elf-output-style=JSON --file-headers --sections --relocations` emits structured
object/section/relocation facts, whereas `llvm-objdump -d` emits presentation
text. These outputs must not be combined by line position or parsed as one
schema.

Current canonical `process_run`/`process_run_timeout` facades accept a command
and argument array but no stdin payload. LLVM supports `-` as readobj input, but
the existing facade cannot provide retained object bytes that way. A production
inspector therefore needs either an owned bounded-stdin process capability, or
an inspector-owned private temporary artifact whose creation, exact rehash,
process use, and deletion are one retry-safe lifecycle. Arbitrary caller paths
are forbidden because they break exact-byte chain of custody.

The pure `parser_binary_inspector_v1` remains an independent preflight and
negative control. It cannot establish complete executable closure because it
selects only `.text`/`.text.*` and does not resolve relocation targets. The
external inspector must enumerate every executable section, symbols, section
groups, and relocations, then correlate disassembly by section/index/address.

The deeper parallel audit found an important existing base below the Simple
facade: `runtime_process_owned.c` implements random 128-bit tokens, Linux
process groups/pidfds/start-identity checks, nonblocking bounded stdout/stderr,
TERM→grace→KILL→reap, one-shot collection, and a 64-KiB drain quantum through
`rt_process_owned_*_v2`. No `.spl` facade currently exposes this V2 lifecycle.
V2 inherits stdin and launches via `execvp`; it binds neither binary input nor
the executed tool image. Separate pinned/piped APIs use raw handles/PIDs and
are not equivalent authority.

Existing pure-Simple `secure_temp_dir` plus `file_write_bytes` can stage exact
NUL/high-byte data and is a plausible development adapter, but introduces file
identity and cleanup state. Highest-assurance review recommends an atomic
owned-process V3 request containing immutable bounded `[u8]` stdin, with the
runtime concurrently feeding input and draining both outputs. Smaller-model
review recommends private staging as the shortest pure-Simple pilot. Both are
retained as explicit options; neither is silently selected.

Live two-COMDAT probing found that this LLVM build emits multiple section groups
inside one JSON object as duplicate `"Group"` keys. The canonical Simple JSON
parser, like ordinary JSON object consumers, applies last-key-wins and would
silently retain only the final group. Therefore `--section-groups` JSON is not
an admissible authority stream for complete closure. The safe route is to run
`--sections --section-data --symbols` and decode every `SHT_GROUP` payload:
little-endian word zero is the group flag, later words are member section
indices, `sh_link` identifies the symbol table, and `sh_info` the signature
symbol. Local clang-generated two-group evidence established this behavior.

The colocated `llvm-objdump -d -` default presentation includes raw instruction
bytes without a separate `--show-raw-insn` switch on this installed version.
A strict decoder can reconstruct each executable section and compare its digest
with independent `llvm-readobj --section-data` evidence. This detects gaps and
substitutions, but remains data validation until an admitted process owner binds
the exact tool image, input, terminal receipt, and output.

The four independent decoder outputs need a fifth coherence boundary because
their exported records can also be synthesized or mutated by callers. The join
must revalidate section universes, executable digests, relocation endpoints,
derived COMDAT membership, instruction byte digests, and gap-free coverage.
It must not infer an ISA feature from a mnemonic alone: operand width and exact
encoding can change the required x86 feature family.

Local clang plus the colocated objdump produced concrete VEX2 (`vpxor`), VEX3
(`vpshufb`), and EVEX (`vpternlogd`) byte rows. The prefix bytes independently
establish encoding family and the encoded L/L'L width. They do not establish
the complete extension set: VEX is shared by AVX and AVX2-era instructions,
while EVEX is shared across distinct AVX-512 families and later extensions.
Admission therefore needs a subsequent exact opcode-map classifier.

The initial exact whitelist demonstrates why feature requirements are sets,
not labels. A 256-bit VEX VPXOR/VPSHUFB row maps to AVX2 while the corresponding
128-bit row maps to AVX. A 512-bit EVEX VPTERNLOGD row requires AVX512F, while
its 128/256-bit forms additionally require AVX512VL. The current normalized V1
instruction record has one `required_feature` field and cannot encode that
conjunction truthfully; integration needs a bounded canonical feature array.

The additive V2 feature layer can preserve V1 terminal compatibility while
binding exact objdump bytes back to the coherent projection. Its safety
relation is equality, not merely `requested subset observed`: an unexpected
observed extension is an undeclared artifact dependency and must reject the
candidate. Legacy instruction legality remains part of baseline closure rather
than being silently called scalar by this vector classifier.

The option-independent terminal join requires two distinct admitted invocations
over the same exact object input: structured readobj and raw-byte objdump. Each
terminal row must be complete, non-overflowed, identity-revalidated, reaped and
collected, with the retained output matching its exact count and digest. This
defines the data contract equally for atomic stdin or private staging; it does
not decide which mechanism owns the process.

All three target-mapping options share an inert validation problem before they
differ on authority. Candidate tables need canonical target tuple text, fixed
architecture name/ID agreement, one-to-one component ID/text relations, unique
profiles/triples/tuples, deterministic ordering, and a framed generation
digest. These checks neither assign IDs nor admit a registry.

Lookup must not trust a previously validated mutable record. Reconstruct and
rehash the candidate on every inert lookup, then bind the selected row to the
complete target-codegen profile tuple. The resulting binding digest detects
row, ABI, format, endian, pointer-width, and target-profile substitution, but
still carries no registry liveness or admission authority.

## Codex selection follow-up — 2026-09-08

<!-- codex-research -->

The user selected target registry **B** and inspector input **1**. Current
source establishes useful prerequisites but not either authority owner:

- `environment_target_identity_mapping_candidate_v1.spl` and
  `environment_target_identity_mapping_lookup_v1.spl` validate and bind
  caller-supplied canonical rows, but deliberately assign no IDs and provide no
  triple parser, alias normalizer, versioned registry generation, or live token.
- `runtime_process_owned.c` provides owned bounded stdout/stderr capture and
  reaping without stdin. The legacy PID-based pipe API can write text chunks,
  but it is not atomic immutable `[u8]` input authority and exposes no matching
  owned close/terminal chain.
- `parser_external_inspection_contract_v1.spl` already models input digest,
  byte count, and fully-written-and-closed facts, while its header correctly
  leaves authoritative issuance to a future registered process owner.

The four requested product checks remain distinct. Shared parser contracts and
provider lifecycle infrastructure exist, but the main frontend still calls the
legacy parser. GPU parser selection remains a fail-closed Wave-0 scaffold.
Generic SIMD text kernels and partial MIR lowering are real, but no admitted
Simple grammar parser SIMD provider executes through the frontend. Tiered JIT
and broad AOT pipelines are real, but parser-specific v3/v4 sibling artifacts,
target-registry binding, binary SIMD proof, and selected/executed receipts are
not integrated end to end.
