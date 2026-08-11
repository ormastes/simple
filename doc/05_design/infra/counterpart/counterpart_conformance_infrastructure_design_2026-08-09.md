# Counterpart Conformance Infrastructure — Detail Design

Date: 2026-08-09
Status: proposed (contracts frozen at Wave 0 by ADR)
Scope: one conformance pipeline under Modern SSpec for all differential/oracle testing
(web, Vulkan/Venus, crypto, compression). Replaces the current split into several
incompatible differential frameworks.

## 0. Direction

Build a **single Counterpart Conformance Infrastructure under Modern SSpec**. Do not add
another independent differential-test framework.

```
Modern SSpec scenario
  → CounterpartEvidenceProvider
  → verified provider adapter
  → raw candidate/reference artifacts
  → versioned converter graph
  → canonical logical artifacts
  → N-way relation engine
  → CanonicalEvidence
  → existing Modern SSpec comparator
  → EvidenceManifest + ManualBlock[]
  → spipe_docgen
```

The dynamically loaded object is normally a **Simple-owned adapter library**, not the
upstream library itself:

```
libsimple_counterpart_zstd.so       └─ links libzstd
libsimple_counterpart_harfbuzz.so   └─ links HarfBuzz
libsimple_counterpart_chrome.so     └─ launches pinned Chrome, talks CDP
libsimple_counterpart_venus.so      └─ controls virglrenderer/vtest or QEMU
```

One stable ABI regardless of whether the backend is an in-process C library, an isolated
worker, a browser process, QEMU plus a guest, or remote hardware.

A direct-dlopen policy for every upstream project cannot work: Chrome is process-driven,
Vulkan uses loader/layer/ICD dispatch, SPIRV-Cross recommends its C API over its unstable
C++ ABI, and tip-of-tree CDP has no backwards-compatibility guarantee (so the Chrome
adapter must pin browser and protocol revision).

## 1. Repository audit

| Area | What exists | Principal problem | Decision |
|---|---|---|---|
| Modern SSpec | Typed selectors, canonical evidence, oracle modes, comparison results, manifests, manual blocks | Live capture sparse; migration incomplete | Make it the sole top-level conformance pipeline |
| GPU/web differential | NormalizedTrace, environment profiles, mapped handles, semantic comparison | Narrow GPU/web schema; real reference adapters mostly planned | Generalize provider/converter infra; retain domain trace validation |
| Chrome DOM/style differential | Real Chrome + Simple extraction, normalization, fail-closed comparison | Shell/Node/JSON-specific; not reusable | Wrap first, then migrate to typed evidence |
| Chrome layout differential | Geometry + line-breaking comparison with useful normalization | Reads retained summaries via shell tools; separate from Modern SSpec | Preserve its rules as versioned converters |
| Dynamic loading | DynLib, versioned loading, symbol-presence checks | Calls effectively integer-only; no buffers, ownership, schemas | Add a dedicated typed counterpart ABI runtime shim |
| spec-to-sspec | Non-fabricating mechanical modernization + manual generation | Line-oriented; sidecar has no semantic AST | Extend additively with explicit evidence binding |
| Cipher/compression gate | Large in-tree spec inventory, perf gate | Runs existing unit specs; no external N-way oracle | Move to provider/converter/matrix framework |
| MDSOC+ | Six-layer structure, CPU/GPU execution modes | Comparison tools don't attach at those boundaries | Add observation ports at MDSOC+ seams, not vendor-shaped internals |

Two gaps dominate: live acquisition covers a small fraction of required evidence domains,
and most of the SSpec inventory is unmigrated. The live-provider pattern is already sound —
capture a real source through an existing repository facade and populate the same structures
fixture-based tests use, leaving downstream stages unchanged. A process capture provider and
a small live terminal example exist; the latter explicitly does not drive an interactive
terminal, settle, or capture redraws.

The existing Chrome stage differential is valuable and must not be discarded: identical
fixtures to both implementations, DOM and computed style compared separately, explicit
normalization rules, zero-comparison rejection, recorded normalization-hiding risk. Its
defect is only the driver shape (independent Node/Chrome/Simple invocations, ad hoc JSON,
shell verdict parsing, hard-coded repo path). The layout differential has similarly strong
domain knowledge (box geometry, UTF-16↔UTF-8 offsets, line grouping, tolerances, vacuity
guards) reached through `sed`/`find` over retained summaries.

`DynLib`/`VersionedDynLib` give path resolution, dlopen, dlsym and symbol checks, but the
call interface is an integer array returning an integer — no pointer+length buffers, typed
result ownership, output writers, cancellation/timeouts, schema negotiation, stream state,
structured errors, crash containment, or process-backed providers. The signature manifest
checks symbol names, not an executable ABI contract. Extending `DynLib.call_n()` with raw
pointers is therefore the wrong first step; a narrow dedicated runtime shim is safer.

## 2. Architectural model

### 2.1 Three evidence planes

Every invocation produces three separate records.

**Logical artifact** — what the component semantically produced:

```
struct LogicalArtifact:
    boundary_id: text
    schema_id: text
    schema_version: i64
    item_count: i64
    canonical_hash: text
    artifact_ref: text
```

Examples: canonical computed-style table; canonical layout-fragment table; glyph run;
Draw IR; decompressed byte string; AES-GCM ciphertext + tag; normalized Vulkan command
trace; image readback.

**Physical execution receipt** — how it was produced:

```
struct ExecutionReceipt:
    provider_id: text
    execution_mode: text       # cpu_reference, simd, vulkan, cuda, qemu...
    device_identity: text
    queue_identity: text
    submission_count: i64
    fence_completed: bool
    device_origin_readback: bool
    fallback_used: bool
    dropped_events: i64
    completed: bool
```

This prevents a GPU test passing because the GPU path silently fell back to CPU.

**Provenance receipt** — why the result is reproducible:

```
struct ProvenanceReceipt:
    package_manifest_hash: text
    provider_manifest_hash: text
    input_hash: text
    converter_route_hash: text
    environment_profile: text
    run_id: text
```

Logical equality and physical execution are intentionally independent: two providers can
agree logically while differing in memory, handle, queue and wire representation.

### 2.2 Test-only MDSOC+ capsule

```
Production MDSOC+ capsules
┌───────────────────────────────────────────────────────────────┐
│ structural_core / parse_framework / resolve_framework         │
│ spatial_layout / execution_framework / object_placement       │
│ Each boundary exposes immutable observation ports only.       │
└───────────────────────┬───────────────────────────────────────┘
                        │ canonical boundary snapshots
                        ▼
Test-only Counterpart Conformance capsule
┌───────────────────────────────────────────────────────────────┐
│ Provider registry / package+build resolver                    │
│ Native loader / isolated worker / process bridge              │
│ Converter graph / N-way relation engine                       │
│ Modern SSpec projection                                       │
└───────────────────────────────────────────────────────────────┘
```

Production code never imports Chrome, Mesa, OpenSSL or zlib; it exposes immutable snapshots
or injected trace sinks at already-meaningful layer seams. The test-only capsule owns all
foreign dependencies. This preserves the existing six shared layers and three execution
modes (`cpu_reference`, `hybrid_vector_gpu`, `resident_gpu`) and the standing warning
against a separate driver or conflated domain semantics.

### 2.3 Align contracts, not implementation classes

"Match the open-source boundary" means: expose a corresponding semantic input/output
contract where a genuine correspondence exists; provide a converter where representation
differs; explicitly mark boundaries non-corresponding where they do not describe the same
operation.

It does **not** mean changing Simple's DOM to Blink classes, exposing Mesa structures from
the Venus driver, importing OpenSSL provider types, mirroring zlib structs, or replacing
MDSOC+ capsules with vendor-shaped layers.

Stable identifier: `<domain>.<mdsoc-layer>.<stage>@<schema-version>`

```
web.parse.node_arena@1          web.resolve.computed_style@1
web.spatial_layout.fragment_table@1
web.execution.shape_glyph_run@1 web.execution.draw_ir@1
web.execution.rgba8_frame@1

vulkan.resolve.spirv_reflection@1  vulkan.execution.command_trace@1
vulkan.execution.readback@1        venus.execution.protocol_trace@1

crypto.execution.aes_gcm@1         compress.execution.zstd_frame@1
```

Each provider's own component name maps to one of these IDs through its manifest.

## 3. Stable provider adapter ABI

### 3.1 Adapter, not arbitrary upstream ABI

Every provider package produces `libsimple_counterpart_<provider>.{so,dylib}` /
`simple_counterpart_<provider>.dll`. The adapter may link an upstream library or control a
process; tests never guess upstream symbol names. A stable C ABI is language-neutral and
wrappable from C++, Rust and Zig. The Simple runtime exposes a safe `CounterpartLibrary`
wrapper and keeps function pointers and raw pointers inside the native runtime shim.

```c
#define SCF_ABI_V1 1u

typedef struct { const uint8_t *data; uint64_t size; } scf_slice_v1;

typedef struct {
    void *context;
    int32_t (*write)(void *context, const uint8_t *data, uint64_t size);
} scf_writer_v1;

typedef struct scf_instance_v1 scf_instance_v1;

typedef struct {
    uint32_t struct_size;
    uint32_t abi_version;
    int32_t (*manifest)(scf_writer_v1 *output);
    int32_t (*open)(scf_slice_v1 configuration, scf_instance_v1 **out_instance);
    int32_t (*invoke)(scf_instance_v1 *instance,
                      scf_slice_v1 component_id,
                      scf_slice_v1 request_envelope,
                      scf_writer_v1 *response_envelope,
                      scf_writer_v1 *trace_envelope);
    int32_t (*reset)(scf_instance_v1 *instance);
    void    (*close)(scf_instance_v1 *instance);
} scf_api_v1;

const scf_api_v1 *scf_get_api(uint32_t requested_abi);
```

Properties: one required bootstrap symbol; versioned function table; explicit struct sizes;
pointer+length data with no NUL assumptions; caller-owned output writer; no upstream object
layout crossing the boundary; explicit instance ownership; reset between corpus cases; no
provider-allocated memory the caller must free; payloads carry schema IDs and versions;
errors are structured result envelopes, not an overloaded integer zero.

### 3.2 Provider kinds

```
enum ProviderKind:
    native_in_process
    native_isolated_worker
    process_bridge
    qemu_guest_bridge
    remote_bridge
```

| Provider type | Default execution |
|---|---|
| Small stable C API (zlib, HarfBuzz) | In-process permitted |
| Complex C++ library / hostile-input parser | Isolated worker |
| Chrome or Servo executable | Process bridge |
| SwiftShader / lavapipe | Isolated worker initially |
| virglrenderer / vtest | Process bridge |
| SimpleOS under QEMU | QEMU guest bridge |
| Physical GPU or board | Remote bridge with signed receipt |

Even when process-backed the adapter remains a shared library; it owns process creation,
protocol selection and conversion into the stable response envelope.

### 3.3 Worker isolation

`simple-counterpart-worker` loads exactly one adapter, validates its manifest, accepts framed
requests on stdin or a local socket, imposes CPU/memory/output/time budgets, returns a
crash/timeout receipt on abnormal termination, and exits after a configurable number of
invocations. A provider crash must yield `provider_status: crashed`,
`comparison_status: failed`, `artifact_status: partial` — never a crashed SSpec process, and
never normalization into "provider unavailable".

## 4. Reproducible build and download

Tests never download "latest" upstream source at runtime.

```
config/counterpart/providers/{chrome,harfbuzz,swiftshader,openssl,zstd}.sdn
config/counterpart/counterpart.lock.sdn
```

Lock record fields: `provider_id, upstream_url, upstream_revision, source_archive_sha256,
patch_set_sha256, adapter_source_sha256, build_recipe_version, toolchain_identity,
target_triple, build_options, license_spdx, artifact_sha256, sbom_sha256`.

```
build/counterparts/<target>/<full-build-digest>/
    libsimple_counterpart_zstd.so
    provider.manifest.sdn  sbom.spdx.json  build.receipt.sdn
```

Commands: `simple counterpart {inspect,fetch,build,verify,list-components,run}`. `fetch` is
the only network phase; normal tests use the local verified cache.

Source builds are authoritative. Verified prebuilt bundles are allowed in normal CI with an
identical lock record, matching artifact hash, matching target/toolchain ABI, SPDX/SBOM data,
a build receipt and a signature or trusted digest. **A missing provider is UNAVAILABLE, never
PASS** — the existing liblz4/libzstd rule becomes framework-wide.

## 5. Component manifests

```
struct ComponentManifest:
    component_id: text
    counterpart_boundary_id: text
    input_schema_id: text
    output_schema_id: text
    stateful: bool
    reset_supported: bool
    deterministic_claim: text
    supported_relations: [text]
    supported_execution_modes: [text]
    capability_requirements: [text]
```

```
provider_id: chromium-cft-151
provider_kind: process_bridge
independence_group: blink
components:
  - chrome.dom_snapshot     → web.parse.node_arena@1
  - chrome.computed_style   → web.resolve.computed_style@1
  - chrome.layout_snapshot  → web.spatial_layout.fragment_table@1
  - chrome.rgba8_capture    → web.execution.rgba8_frame@1

provider_id: simple-web
independence_group: simple-web
components: simple.web.cpu.{style,layout,paint}, simple.web.gpu.{paint,raster}
```

`independence_group` prevents counting two wrappers over one implementation as two
independent references.

## 6. Converter framework

### 6.1 Converter graph

```
enum ConversionLoss:
    identity | representation_only | canonicalizing
    semantic_projection | diagnostic_only

struct ConverterManifest:
    converter_id, converter_version, from_schema, to_schema
    loss: ConversionLoss
    deterministic: bool
    preserved_dimensions: [text]
    dropped_dimensions: [text]
    preconditions: [text]
```

Routes may be multi-edge: `Chrome DOMSnapshot JSON → ChromeSnapshotIR → CanonicalNodeArena`,
or `Simple GPU device buffer → device-origin readback → DrawIR device record → CanonicalDrawIR`.

```
struct ConversionReceipt:
    converter_id, converter_version, input_hash, output_hash
    loss: ConversionLoss
    dropped_dimensions: [text]
    assumptions_applied: [text]
    status: text
```

### 6.2 Four converter classes

- **Representation converter** — encoding change only (JSON→SDN, UTF-16 offsets→resolved
  text spans, LE bytes→integer fields, device SoA→host SoA). Relations: exact / canonical exact.
- **Structural aligner** — identity and ordering (Chrome node indexes→stable structural paths,
  transient Vulkan handles→deterministic logical IDs, workgroup order→stable entity-key order,
  glyph clusters→source spans). Relations: structural or semantic.
- **Semantic projector** — selects genuinely corresponding facts (Venus packets→Vulkan
  operation facts, Chrome layout objects→canonical box geometry, OpenSSL return codes→typed
  crypto error classes, compression frame metadata→canonical frame fields). Deliberately
  lossy; must name dropped dimensions.
- **Execution-mode projector** — separates physical execution from logical results (CPU
  pointers vs GPU device buffers, host calls vs queued commands, software vs hardware
  rasterizer, scalar vs SIMD lane order). Emits both a logical artifact and an execution receipt.

### 6.3 Fail-closed routing

Reject: an exact comparison whose route contains `semantic_projection`; a required dimension
dropped by any converter; an ambiguous equal-priority route; a cycle; missing schema versions;
an undeclared default value; a conversion resolving zero items; a provider output whose schema
differs from its manifest; a converter deriving expected values from candidate output.

No normalization rule may hide inside the comparator. Every rule belongs to a named, versioned
converter and appears in the generated manual.

## 7. N-way comparison engine

```
             Simple CPU  Simple GPU  Chrome  Servo
Simple CPU        —          ✓          ✓      ✓
Simple GPU        ✓          —          ✓      ✓
Chrome            ✓          ✓          —      ✓
Servo             ✓          ✓          ✓      —
```

```
enum OracleAuthority:
    normative_vector | normative_spec_rule | independent_reference
    differential_peer | self_execution_mode | diagnostic_only
```

Consensus is diagnostic and never overrides a normative vector or spec rule. Three
implementations sharing one defective upstream are not stronger than an independent
known-answer vector.

Relations: `byte_exact`, `canonical_exact`, `structural_equal`, `semantic_equal`,
`ordered_equal`, `multiset_equal`, `numeric_bound`, `trace_refinement`, `cross_decode`,
`round_trip`, `metamorphic`, `image_exact`, `image_masked_exact`, `image_threshold`.

Complex relations (e.g. `cross_decode`) stay in the counterpart relation engine, which
projects facts such as `counterpart.cross_decode.executed=16`,
`counterpart.cross_decode.failed=0`, `counterpart.round_trip.failed=0` into CanonicalEvidence —
avoiding premature expansion of the stable Modern SSpec `OracleMode` enum.

## 8. CPU/GPU equivalence rule

```
             Independent external oracle
                    /             \
        Simple CPU reference  ↔  Simple GPU mode
```

Per case: same canonical request to CPU and GPU; same logical output schema; CPU/GPU logical
artifacts compared; GPU emits an execution receipt; an independent provider compared at the
closest genuinely corresponding boundary; final readback independently checked where applicable.

Required GPU assertions:

```
execution_mode ∈ {vulkan, cuda, resident_gpu}
submission_count > 0        fence_completed = true
device_origin_readback = true   fallback_used = false
dropped_events = 0          completed = true
```

Mutation tests must show the gate fails when submission is bypassed, a fence omitted, readback
synthesized on CPU, fallback enabled, one logical record changed, stable ordering removed, or a
converter maps the wrong object identity. Logical artifacts never contain raw GPU pointers,
native handles, allocation addresses or wall-clock timestamps.

## 9. Web renderer design

The production renderer's flat SoA pipeline does not correspond one-for-one with Blink's
object-oriented pipeline. Tokenization, prepaint and compositor layers either have no
production Simple counterpart or serve a different purpose; they must not be forced into false
equivalence.

| Boundary | Canonical request | Canonical result | External counterpart | Relation |
|---|---|---|---|---|
| `web.parse.node_arena@1` | HTML bytes, parser profile | Flat node arena: parentage, text, attributes | Chrome DOMSnapshot; optional Servo | Structural |
| `web.resolve.computed_style@1` | Node arena, rules, environment | Per-node computed-style table | Chrome DOMSnapshot styles | Exact after property canonicalization |
| `web.spatial_layout.fragment_table@1` | Styled nodes, viewport constraints | Box/fragment geometry, line records | Chrome DOMSnapshot layout; Servo | Exact or derived numeric bounds |
| `web.execution.glyph_run@1` | Text, font, script, language, features | Glyph IDs, clusters, advances, offsets | HarfBuzz | Canonical exact or fixed-point bound |
| `web.execution.draw_ir@1` | Fragments, visual styles | Stable Draw IR | Simple CPU vs GPU; instrumented browser | Structural/semantic |
| `web.execution.rgba8_frame@1` | Draw IR, viewport, fixed resources | RGBA8 frame | Simple CPU/GPU, Chrome screenshot, software raster | Exact for pinned Simple lanes; hosted policy otherwise |
| `web.execution.present_receipt@1` | Frame | Presentation/readback receipt | Host/window/browser adapters | Invariant |

Chrome's DOMSnapshot exposes flattened DOM, layout and selected computed styles. RenderingNG
separates main-thread lifecycle, display/paint structures, rasterization and compositor/Viz
execution. LayoutNG's contract shape (DOM + style + parent constraints → immutable fragments)
is a useful contract, not a mandate to adopt Blink internals. HarfBuzz supplies glyph IDs,
clusters, advances and offsets over a stable public C API/ABI — an appropriate in-process
shaping counterpart.

**Chrome adapter.** First version wraps existing tools rather than replacing them: start pinned
Chrome for Testing → invoke existing CDP extraction → capture raw protocol response → run the
existing normalization logic → emit versioned canonical artifacts. Manifest must record
`browser_product, browser_version, browser_revision, cdp_protocol_revision,
command_line_flags, viewport, device_scale_factor, font_profile, locale, timezone`. Tip-of-tree
CDP must not be used unpinned.

**Corpus.** Web Platform Tests for standards-facing coverage plus current minimized repository
fixtures for defect localization. WPT supplies corpus and expected behavior where its tests
define one; it does not supply canonical intermediate DOM/layout artifacts, so stage extractors
are still needed.

**CPU/GPU web gate.** Per fixture: CPU stage → artifact A; GPU stage → artifact B + receipt;
external counterpart → artifact C. Minimum gates: `A == B`; `B.execution.fallback_used == false`;
`B.execution.device_origin_readback == true`; A/C relation passes; B/C relation passes; final
CPU/GPU raster exact under a pinned deterministic profile. For hosted Chrome, pixels stay
supplemental unless environment, fonts, rasterizer and compositor are pinned tightly enough;
DOM, computed style, layout geometry and Draw IR remain the primary oracles.

## 10. SimpleOS Vulkan and Venus

| Provider | Role |
|---|---|
| Khronos Vulkan Loader + validation layers | Dispatch, API validity, validation messages |
| SPIRV-Tools / SPIRV-Cross C adapter | Module validity, reflection, shader conversion |
| SwiftShader | CPU-based independent Vulkan ICD |
| Mesa lavapipe | Second software Vulkan implementation |
| Mesa Venus guest + virglrenderer | Venus protocol counterpart |
| vtest | Fast host-side Venus integration |
| QEMU | Full SimpleOS transport and guest-driver test |
| VK-GL-CTS / dEQP | API conformance corpus |

The loader sits between applications, layers and drivers, and validation layers are themselves
dynamically loaded interception libraries — so a test-only Vulkan layer adapter is the natural
way to capture normalized API events. SwiftShader is a CPU Vulkan ICD with dEQP validation,
useful as a deterministic reference independent of the SimpleOS guest driver. Venus serializes
Vulkan commands over virtio-gpu with guest/host split across Mesa and virglrenderer, so raw
packet equality is the wrong oracle: handle allocation, packet grouping and transport layout may
differ while semantics and readback agree. VK-GL-CTS becomes a separate conformance lane rather
than reimplemented fixtures.

Boundaries: `vulkan.resolve.spirv_validation@1`, `vulkan.resolve.spirv_reflection@1`,
`vulkan.execution.{instance_capabilities,device_capabilities,command_trace,queue_submission,
sync_trace,buffer_readback,image_readback,cts_result}@1`,
`venus.execution.{transport_trace,protocol_trace}@1`.

Compare: operation and state-transition sequence, stable object lineage, descriptor/resource
facts, synchronization dependencies, result and error classes, buffer/image readback, required
capabilities, queue/fence completion, no-fallback evidence. Do not compare: raw handles,
pointers/addresses, exact packet grouping, timestamps, physical allocation order, or raw Venus
bytes (unless testing the serializer against a frozen protocol vector).

`NormalizedTrace` remains a specialized validator for GPU trace completeness and ordering; add
`normalized_trace_to_counterpart_artifact()` and `normalized_trace_to_evidence()` and route the
final result through the common matrix and Modern SSpec pipeline. Once dual-run parity is
proven, the duplicate verdict logic in `differential_conformance.spl` reduces to domain-specific
trace validation.

Profiles: `vulkan-host-swiftshader-deterministic`, `vulkan-host-lavapipe-deterministic`,
`vulkan-host-hardware`, `simpleos-qemu-{x86_64,aarch64,riscv64}-venus`,
`simpleos-hardware-venus`, `vulkan-provider-unavailable-negative`,
`vulkan-fallback-forbidden-negative`. The existing discovery/queue/fence/device-origin-readback/
no-fallback requirements become ordinary execution-receipt fields, not a GPU-only special case.

## 11. Cipher and cryptographic specifications

Oracle order: normative NIST/RFC vectors → algorithm invariants → independent upstream
implementations → Simple CPU/GPU/SIMD mode parity → performance and side-channel diagnostics.

NIST CAVP/ACVP is black-box input/output validation with machine-readable schemas for symmetric
algorithms, hashes, RSA and current PQ algorithms — represented as a **vector provider**, not a
shared-library provider. OpenSSL's provider architecture exposes cipher/digest/MAC/key-management
families through dispatch interfaces; the Simple adapter maps these onto stable boundaries
without exposing OpenSSL structures. Mbed TLS / TF-PSA-Crypto is a second portable provider.

Boundaries: `crypto.execution.{digest,mac,block_cipher,stream_cipher,aead,kdf,key_agreement,
signature,kem}@1`. Algorithm, mode and parameters are request fields, not separate infrastructure.

| Operation | Primary relation |
|---|---|
| SHA, BLAKE, CRC, deterministic MAC | Byte exact |
| AES block modes, fixed parameters | Byte exact |
| AEAD, fixed key/nonce/AAD | Ciphertext and tag exact |
| KDF, fixed inputs | Byte exact |
| Ed25519 deterministic signing | Signature exact plus verify |
| ECDSA with random nonce | Decode and verify; exact only with test-supplied deterministic nonce |
| RSA-PSS | Verify plus parameter validation; exact only with deterministic test salt |
| Key generation | Public/private consistency, cross-provider operation — not raw-key equality |
| KEM | Decapsulation agreement with deterministic test randomness where standardized |
| Error behavior | Typed error-class relation |

Matrices must include zero-length and maximum admitted input; overlapping/in-place buffers where
allowed; streaming chunk partitions; wrong key/tag/nonce; truncation and bit corruption; invalid
key sizes; weak/forbidden parameter rejection; CPU/SIMD/GPU parity; vector-provider provenance.

Secrets must not be copied into generated manuals — use digests or explicit redaction records;
raw secret artifacts only when a profile explicitly permits, with restrictive permissions.

## 12. Compression specifications

zlib/libdeflate, libzstd, liblz4, Brotli and liblzma are the permissively licensed references;
corruption handling, round trips and typed errors are already required.

**Compressed-byte equality is not the default.** Formats define valid streams, not one unique
encoder decision; match selection, block splitting, Huffman choices and entropy tables may all
differ while conforming. Byte equality is limited to a declared canonical encoder profile or a
frozen known-answer vector.

```
                   Simple dec  zlib dec  libdeflate dec
Simple encoder          ✓          ✓            ✓
zlib encoder            ✓          ✓            ✓
libdeflate encoder      ✓          ✓            ✓
```

Required: all encoder outputs decode where the profile is supported; decoded bytes exactly equal
the original; frame/header invariants hold; checksums and dictionary IDs correct;
truncated/corrupt streams fail with a typed classification; resource budgets respected.

Boundaries: `compress.execution.{raw_deflate,zlib,gzip,lz4_block,lz4_frame,zstd,brotli,xz}@1`.

Corpus per format: empty and one-byte input; incompressible data; highly repetitive data; mixed
text/binary; boundary lengths around block/window sizes; streaming chunk partitions; dictionaries;
optional checksums; concatenated frames; invalid distances and malformed entropy tables;
truncation at every important structural boundary; bounded decompression and expansion-ratio
limits; CPU scalar/SIMD/GPU equivalence.

The current cipher/compression runner remains a compatibility facade while cases move into
structured plans and external provider matrices.

## 13. Modern SSpec integration

`CounterpartEvidenceProvider` consumes a `CounterpartPlan` and returns a raw artifact bundle:
plan, package manifests, provider manifests, provider responses, raw stdout/stderr/status,
logical artifacts, execution receipts, conversion receipts, comparison matrix, mismatch contexts,
artifact hashes. It does not render Markdown.

Canonical evidence paths:

```
counterpart.plan.id                     counterpart.boundary.id
counterpart.providers.{requested,executed,unavailable}
counterpart.comparisons.{executed,failed}
counterpart.provider.<id>.{version,artifact_hash,status,independence_group}
counterpart.converter.<id>.{loss_class,input_hash,output_hash}
counterpart.matrix.<left>.<right>.{relation,matched,mismatch_count}
counterpart.execution.<provider>.{mode,submission_count,fence_completed,
                                  device_origin_readback,fallback_used}
```

These use existing exact/semantic/ordered/invariant checks — no new scenario language.

```
describe "GPU web paint remains equivalent to CPU and reference output":
    it "renders the retained fixture through all declared providers":
        step("Load the retained web-rendering fixture")
        step("Render it with the CPU and Vulkan implementations")
        step("Compare their logical output with the independent reference")

        val run = capture_counterpart(
            "counterpart.web.paint.v1",
            "test/fixtures/web/retained_panel.html"
        )
        val evidence = counterpart_run_to_evidence(run)

        val result = compare_evidence(evidence, oracle_spec(
            "counterpart.web.paint.v1",
            [
                check_exact("counterpart.providers.unavailable", "0"),
                check_exact("counterpart.comparisons.failed", "0"),
                check_exact("counterpart.execution.simple_gpu.fallback_used", "false"),
                check_exact("counterpart.execution.simple_gpu.device_origin_readback", "true")
            ]
        ))

        expect(result.status).to_equal(EvidenceStatus.passed)
```

Generated QA manuals show: component boundary and schema version; input fixture and digest;
provider names, versions, build hashes; execution modes and environment; converter routes and
declared loss; comparison matrix; expected vs actual mismatch detail; GPU execution receipt;
ignored fields with reasons; artifact links. Large binaries stay in the content-addressed
artifact store — the sidecar carries hashes and `artifact_link` blocks, not megabytes.

`simple.sspec.evidence.v1` stays stable. An opaque extension payload
`simple.sspec.counterpart.v1` carries `plan_ref, provider_manifest_refs,
conversion_receipt_refs, comparison_matrix_ref, execution_receipt_refs`. The ordinary evidence
manifest remains the authoritative receipt for the generated manual.

## 14. spec-to-sspec extension

The non-fabrication rule stays. New modes:

```
simple spec-to-sspec analyze <spec>
simple spec-to-sspec modernize <spec> --apply
simple spec-to-sspec bind-evidence <spec> --map <mapping.sdn>
simple spec-to-sspec emit-profile <spec>
simple spec-to-sspec verify-no-fabrication <spec>
```

- **analyze** reports shell/process invocation, retained-summary parsing, hard-coded repo paths,
  possible provider components, existing assertions, missing non-vacuity checks, missing
  provenance, possible Modern SSpec profile. Changes nothing.
- **modernize** keeps current behavior: syntax/import repairs, safe step insertion, assertion
  preservation, optional manual regeneration.
- **bind-evidence** applies only an explicit mapping (`scenario_id, counterpart_plan_id,
  boundary_id, profile_id, existing_assertion_mapping`). It may replace shell-summary parsing
  with a structured provider call only when the mapping names the exact provider, component and
  relation. It must never infer an expected value from current output, a tolerance from observed
  differences, equivalence of unlike stages, optionality of a missing provider, sufficiency of a
  screenshot, or which fields may be ignored.
- **emit-profile** generates a skeletal profile with unresolved placeholders and findings, not
  marked accepted.
- **verify-no-fabrication** checks every expected literal existed in source/mapping/normative
  vector; every tolerance has a rationale; every ignore has a reason; no expected artifact was
  copied from candidate output; every binding retains source-span provenance.

## 15. Proposed source layout

```
src/lib/common/spec/evidence/counterpart/
    model.spl schema.spl plan.spl relation.spl
    logical_artifact.spl execution_receipt.spl provenance_receipt.spl
    conversion_receipt.spl evidence_projection.spl manual_projection.spl

src/lib/nogc_sync_mut/spec/evidence/counterpart/
    package_registry.spl provider_registry.spl provider_runner.spl
    native_provider.spl worker_provider.spl process_provider.spl qemu_provider.spl
    converter_registry.spl converter_graph.spl relation_engine.spl
    matrix_compare.spl artifact_store.spl

src/lib/nogc_sync_mut/sffi/counterpart_abi.spl
src/runtime/counterpart_abi_runtime.c
src/runtime/counterpart_worker_runtime.c
src/app/counterpart/{main,fetch,build,verify,inspect,run}.spl

tools/counterpart/sdk/{c,rust}/
tools/counterpart/adapters/web/{chrome,harfbuzz}/
tools/counterpart/adapters/vulkan/{swiftshader,mesa_venus}/
tools/counterpart/adapters/crypto/{openssl,mbedtls}/
tools/counterpart/adapters/compress/{zlib,libdeflate,zstd,lz4,brotli}/

config/counterpart/{counterpart.lock.sdn,providers,profiles,schemas,plans}/

test/01_unit/infra/counterpart/
test/02_integration/infra/counterpart/
test/03_system/counterpart/{web,vulkan,crypto,compress}/
```

Downloaded upstream source and build products live under `build/counterparts/`, not in the owned
source tree. Central registries are generated from provider descriptor files — domain agents add
descriptors in their own directories rather than all editing one registry file.

## 16. Non-negotiable acceptance gates

| Gate | Required result |
|---|---|
| Provider count | ≥1 candidate and ≥1 valid oracle/reference actually executed |
| Comparison count | > 0 |
| Provider absence | Explicit UNAVAILABLE or FAIL per profile |
| Package integrity | Source, adapter and artifact hashes verified |
| License provenance | SPDX and SBOM complete |
| ABI | Version and struct-size negotiation validated |
| Isolation | Adapter crash cannot terminate SSpec |
| Conversion | Every route and loss class recorded |
| Exactness | No exact relation traverses a lossy converter |
| Independence | Providers sharing an implementation not counted independently |
| GPU | Submission, fence, device readback and no-fallback proven |
| Crypto | Normative vectors outrank peer consensus |
| Compression | Cross-decode and round trip required; byte exact only when declared |
| Web | Only genuinely corresponding stages compared |
| Vacuity | Empty inputs, outputs, selectors or matrices fail |
| Sabotage | Deliberate defect is detected |
| Modern SSpec | Result projects to CanonicalEvidence and a generated manual |
| Migration | Legacy/new dual-run parity demonstrated |
| Architecture | Production modules contain no foreign provider imports or types |
| Secrets | Manuals and ordinary artifacts contain no unredacted keys or plaintext |

## References

- Plan: `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- Modern SSpec: `doc/03_plan/infra/sspec/modern_sspec_completion_plan_2026-08-09.md`
- MDSOC+: `doc/04_architecture/compiler/mdsoc_architecture_tobe.md`
