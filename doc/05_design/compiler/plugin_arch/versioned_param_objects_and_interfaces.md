# Versioned Parameter Objects and Concrete Plugin Interfaces

Status: PROPOSED (2026-08-28). Design; sketches are illustrative Simple, not
landed code. Architecture: `doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md`.
Research: `doc/01_research/compiler/plugin_arch/kernel_plugin_versioning_research_2026-08-28.md`.

Constraints honoured: no inheritance (composition, traits, mixins); `<>`
generics; value semantics + COW (never mutate through an alias,
`.claude/rules/code-style.md`); SFFI to C for the dynamic boundary.

## 1. Interface identity

```simple
# src/lib/common/plugin/iface_id.spl  (new, K0)
struct IfaceId:
    name: text          # "simple.codegen.BackendPort"
    major: i64          # breaking-change counter
    minor: i64          # additive counter
    abi_digest: text    # sha256, domain "simple/abi-interface/v1" (§3)

fn iface_id_compatible(host: IfaceId, plugin: IfaceId, accepted: [text]) -> bool:
    host.name == plugin.name and host.major == plugin.major
        and (plugin.abi_digest == host.abi_digest or accepted.contains(plugin.abi_digest))
```

`accepted` is the host's recorded list of digests it was verified against
(§6.1); it is how a plugin built against minor N-1 still loads. Name + major
mismatch is never accepted.

## 2. Parameter objects

### 2.1 Shape (one convention, aligned with `ApkXxxV1` records
`src/lib/common/aspect_pack.spl:123-334` and the extension-identity tuple
`doc/04_architecture/compiler/extension_completeness.md:29-36`)

```simple
struct ParamHeader:
    schema_name: text     # "simple.codegen.CodegenParams"
    schema_major: i64     # layout-breaking counter
    schema_minor: i64     # append-only counter
    present: i64          # bit i set  <=>  field with ordinal i was explicitly set

struct ParamExt:          # typed extension node (Vulkan pNext, but a value array)
    ext_name: text        # "simple.codegen.ext.cuda_sm"
    ext_major: i64
    payload: [u8]         # canonical SDN bytes of the extension record
    payload_schema_hash: text

struct CodegenParamsV1:
    hdr: ParamHeader
    # ordinal 0..n: fixed fields, append-only, never reordered/removed
    target_triple: text          # ordinal 0
    opt_level: i64               # ordinal 1
    debug_info: bool             # ordinal 2
    gc_off: bool                 # ordinal 3
    ext: [ParamExt]              # unknown ext_name entries are skipped by readers

impl CodegenParamsV1:
    fn has(self, ordinal: i64) -> bool: (self.present >> ordinal) & 1 == 1
    fn with_opt_level(self, v: i64) -> CodegenParamsV1:
        var p = self; p.opt_level = v; p.present = p.present | (1 << 1); p
```

Rules (lint-checked, §7):
- Fields carry ordinals by declaration order; new fields are appended and
  bump `schema_minor`. Removal, rename, retype, reorder => `schema_major`+1 and a
  new record name suffix (`V2`), the same convention as `ApkModuleSourceV1/V2/V3`.
- `present` distinguishes "not set" from a default value; a reader built for
  minor N reads a minor N+1 record by masking bits above its known ordinal
  count; a reader for minor N+1 reading a minor N record sees the bit clear and
  applies its default.
- Extensions live in `ext`, tagged by `(ext_name, ext_major, payload_schema_hash)`.
  Readers skip unknown names (protobuf unknown-field rule).
- Since values are COW, `with_*` builders return a new record; no alias
  mutation.

### 2.2 FFI form (P-dyn across C)
A param object crosses the SFFI boundary as `(hdr_ptr, bytes)` where bytes are
canonical SDN produced by the existing canonical encoder
(`action_key.spl:198-200` style `canon_*`), prefixed by a fixed C header:

```c
/* src/runtime/runtime.h (new, K0) */
typedef struct {
    uint32_t cb_size;        /* Win32 cbSize: total header bytes */
    uint32_t schema_major;
    uint32_t schema_minor;
    uint64_t present;
    const char* schema_name;
    const uint8_t* payload; uint64_t payload_len;  /* canonical SDN */
} spl_param_hdr_v1;
#define SPL_PARAM_HDR_V1_SIZE sizeof(spl_param_hdr_v1)
#define SIMPLE_ABI_VERSION 1   /* does not exist today; K0 global */
```

`cb_size` lets an older plugin ignore trailing header fields; `SIMPLE_ABI_VERSION`
folds into `native_build_producer_identity` (`incremental.spl:250-252`).

### 2.3 Aspect parameters (replacing env strings and generated source)
```simple
struct AspectParamsV1:
    hdr: ParamHeader
    log_calls: bool             # was SIMPLE_AOP_LOG_CALLS       (driver_pipeline_aop.spl:70-80)
    log_assignments: bool       # was SIMPLE_AOP_LOG_ASSIGNMENTS
    compile_log_level: i64      # was SIMPLE_AOP_COMPILE_LOG_LEVEL
    runtime_log_level: i64      # was SIMPLE_AOP_RUNTIME_LOG_LEVEL
    mcdc_mode: i64              # was SIMPLE_MCDC_MODE (test_executor_parsing.spl:793-796)
    mcdc_manifest_sha256: text  # was --simple-mcdc-manifest= (:826-834)
    ext: [ParamExt]
```
The env vars stay as a *front-end* that fills this record at the CLI boundary;
the driver, the weaver and the coverage aspect consume only the record. The
coverage preamble/epilogue (`test_executor_parsing.spl:804-869`) becomes an APK
`STARTUP`-mode aspect carrying the same record, not a source rewrite.

## 3. Digest: `simple/abi-interface/v1`

Reuse `interface_digest_with_domain(domain, parts)`
(`src/compiler/35.semantics/interface/compile_interface.spl:39`) with domain
`simple/abi-interface/v1`, parts = for each exported trait/fn/struct in the
interface module, the typed encoder output (`:48-102`) **plus** for each param
struct: `schema_name`, `schema_major`, `schema_minor`, and the ordered
`(ordinal, field_name, field_type)` list. This fixes the two known blind spots:
textual v1 skips struct fields (`action_key.spl:267` comment) and the
`abi_interface_digest` placeholder re-hashes compile-interface parts
(`module_identity.spl:9-22`). `ModuleIdentity.abi_interface_digest` (`:24-31`)
becomes real; nothing else in `ModuleIdentity` changes.

`minor` is derived, not declared: the digest of the record with ordinals
`0..k` for k < n gives the prefix digests; a host records `accepted =
[prefix_digest(k) for k in known_minors]`. `major` is declared in source.

## 4. Interface shape: trait for static, versioned struct-of-fns for dynamic

Precedent: the repo already rejected `di.resolve("Backend") -> Any` and chose a
struct of `any`-typed fn fields, `struct BackendPort{name, run_fn,
supports_jit_fn, target_triple_fn}` (`src/compiler/70.backend/backend_port.spl:15-25`,
one implementor `85.mdsoc/feature/codegen/backends/interpreter/backend.spl:38-49`,
held on `CompileContext.backend` `00.common/compiler_services.spl:147,217`).
This design keeps that shape and types it.

```simple
# K0: src/compiler/70.backend/backend_port.spl (typed)
trait BackendPlugin:                      # P-static implementors
    fn iface(self) -> IfaceId
    fn describe(self) -> BackendDescV1    # param object: name, targets, caps
    fn run(self, params: CodegenParamsV1, mir: MirModule) -> Result<CodegenOut, BackendError>
    fn supports(self, cap: text) -> bool  # optional-method probe (COM QueryInterface analogue)

struct BackendPortV1:                     # P-dyn boundary: fixed slots, append-only
    hdr: ParamHeader                      # schema_name "simple.codegen.BackendPortV1"
    iface: IfaceId
    describe_fn: fn() -> BackendDescV1
    run_fn: fn(CodegenParamsV1, MirModule) -> Result<CodegenOut, BackendError>
    supports_fn: fn(text) -> bool
    ext: [ParamExt]                       # future slots go here, not as new fields

fn backend_port_from_trait<T: BackendPlugin>(p: T) -> BackendPortV1: ...
```

Static plugins implement the trait; the kernel calls through the trait (no
indirection cost beyond one call per compile). Dynamic plugins export
`spl_plugin_entry_v1()` returning a `BackendPortV1` through the FFI header of §2.2.

## 5. Negotiation (fail-closed) and the static/dynamic switch

```simple
struct HostOfferV1:
    hdr: ParamHeader
    simple_abi_version: i64          # SIMPLE_ABI_VERSION
    producer_identity: text          # incremental.spl:250-252 string
    ifaces: [IfaceId]                # what the host serves
    accepted_digests: [text]         # §6.1
    capabilities: [text]

struct PluginAnswerV1:
    hdr: ParamHeader
    implements: IfaceId
    requires_caps: [text]
    plugin_digest: text              # content hash of the plugin unit

enum NegotiateVerdict:
    Ok
    NameMismatch(text)   # "PLUG-E-NAME"
    MajorMismatch(i64, i64)          # "PLUG-E-MAJOR"
    DigestUnaccepted(text)           # "PLUG-E-DIGEST"
    MissingCapability(text)          # "PLUG-E-CAP"
    AbiVersion(i64, i64)             # "PLUG-E-ABI"

fn negotiate(host: HostOfferV1, ans: PluginAnswerV1) -> NegotiateVerdict
```

Both binding modes run the same `negotiate`:

| Mode | Binding site | When `negotiate` runs | Existing mechanism reused |
|---|---|---|---|
| P-static | static plugin table `[BackendPortV1]` built at link | at link (receipt records verdict) and once at startup (table walk, no I/O) | `APK_ACT_STATIC` (`aspect_pack.spl:65-119`); `SIMPLE_LINK_OBJECTS` projection (`llvm_native_link_stage4_projection.spl:40-123`) |
| P-dyn | APK facet or `.so` from `--emit-shared` | at first `apk_load_facet` / `spl_dlopen_checked` | gate `aspect_pack.spl:2125-2205` — `negotiate` replaces the opt-in `required_core_*` checks (`:2196-2205`) with mandatory ones; `dynamic_versioned.spl:170-187` filename match replaced by `PluginAnswerV1` read via `spl_dlsym_checked("spl_plugin_entry_v1")` |

Switching a plugin between modes is a manifest change (`simple.sdn` §6.2
`link: static|dynamic`), not a source change, and never a kernel change.

## 6. Where identity is recorded and checked

### 6.1 Manifests
- `SmfManifestEntry` (`watcher/smf_manifest.spl:26-41`): add `abi_digest: text`,
  `provides: [text]` (iface ids as `name@major:digest`), `requires: [text]`.
  Bump `SmfManifest.version` to 4 and make the reader reject unknown/greater
  versions instead of defaulting to 1 (`:220,231-233`); turn
  `smf_manifest_entry_iface_verdict` (`:163-188`) from print into rejection.
- `simple.sdn` (`src/lib/simple.sdn`; readers `package_pins.spl:343-356`,
  `link_deps.spl:3`): add
  ```sdn
  provides:
    - iface: simple.codegen.BackendPort   major: 1   digest: sha256:...
  requires:
    - iface: simple.core.ValueAbi         major: 1   range: "[1.0,2)"   # OSGi consumer range
  link: static        # or dynamic; consumed by the bootstrap projection
  ```
  Provider ranges are narrow, consumer ranges wide (OSGi asymmetry); `^`/`~`
  from `package/semver_old.spl:257-267` are the only range operators.
- APK catalog: `ApkCatalogEntryV2` already carries the facet contract ABI hash
  (`aspect_pack.spl:2125-2205`); add `iface: IfaceId` and `plugin_digest`.
- Bootstrap receipt (`src/app/build/bootstrap_receipt_planner.spl`) records
  every `negotiate` verdict for P-static units; `CompilerArtifactManifestV1`
  (today only in `scripts/bootstrap/stage4-tooling-matrix.shs`) gets a `.spl`
  definition carrying the same rows.

### 6.2 Load-time detection and reporting
`negotiate` verdict codes `PLUG-E-*` follow the `MCDC-E-DYNAMIC-*` precedent
(`mcdc/dynamic_aspect.spl:128-163`) and the APK codes (`APK_ABI_MISMATCH`,
`APK_SIGNATURE_*` `:2607-2623`). A refused plugin is reported with
`(name, host major/digest, plugin major/digest, code)` and the process fails
unless the caller passed `PluginPolicy.optional` for that iface; nil is never
returned (closes the class in
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`).

### 6.3 Enforcement by existing tooling
- Cache keys: `abi_digest` of each `requires` entry joins `dep_ifaces`
  (`block_key.spl:30-31`, `ActionDep.iface_digest` `action_key.spl:31`) so a
  plugin interface change re-keys exactly its consumers.
- Bootstrap gate: `bootstrap_wide_inputs_hash` (`bootstrap-from-scratch.sh:1018-1028`)
  hashes a `kernel_closure.sdn` list (K0+K1 files) plus the sorted `abi_digest`
  set of `provides` from P-static units, instead of `src/compiler/**`.
- Lint (§7) and a fail-closed check script
  `scripts/check/check-param-object-evolution.shs` (same verdict convention as
  the other guards: `PASS — n checked` / `FAIL` / `ERROR — nothing was checked`).

## 7. Lint rules (P-static, in `90.tools/lint/`)
- `PARAM-001` a struct whose first field is `hdr: ParamHeader` must have
  `ext: [ParamExt]` as its last field.
- `PARAM-002` versioned record names end in `V<n>`; a `V<n+1>` must be a
  prefix-compatible superset of `V<n>` (ordinals preserved) or declare
  `schema_major` > `V<n>`'s.
- `PARAM-003` no `env_get("SIMPLE_AOP_*")`/`SIMPLE_MCDC_*` outside
  `src/app/cli` and `src/app/io` (env is CLI front-end only).
- `PLUG-001` a `BackendPortV1`/`*PortV1` struct gains fields only via `ext`.
Each rule ships with a reproduce spec and a mutation-red twin
(`test/01_unit/compiler/plugin_arch/`).

## 8. Example: one plugin, both link modes

```simple
# src/plugins/backend_c/plugin.spl  (P-static by default)
struct CBackend: ...
impl BackendPlugin for CBackend:
    fn iface(self) -> IfaceId: IfaceId("simple.codegen.BackendPort", 1, 0, BACKEND_PORT_ABI_V1)
    fn describe(self) -> BackendDescV1: BackendDescV1.new("c").with_targets(["x86_64-unknown-linux-gnu"])
    fn run(self, params: CodegenParamsV1, mir: MirModule) -> Result<CodegenOut, BackendError>: ...
    fn supports(self, cap: text) -> bool: cap == "emit-object"

# static: listed in the plugin table; simple.sdn `link: static`
# dynamic: `simple compile src/plugins/backend_c/plugin.spl --native --emit-shared`
#          (compile_targets.spl:668) and simple.sdn `link: dynamic`; loader resolves
#          `spl_plugin_entry_v1` -> BackendPortV1 -> negotiate(...)
export fn spl_plugin_entry_v1() -> BackendPortV1: backend_port_from_trait(CBackend.new())
```
Adding `lto: bool` to `CodegenParamsV1` later: append as ordinal 4,
`schema_minor` 0->1, digest changes, host `accepted` gains the old prefix
digest; the C backend plugin above loads unchanged.
