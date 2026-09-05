<!-- codex-architecture -->
# Chromium Web Renderer Primitive Differential Architecture

## Status and decision

**Proposed, interface-frozen test capsule.** The one permitted Chromium link is
`libsimple_chromium_primitive_oracle` (platform suffix applies), a test-only
dynload plugin built from a pinned Chromium checkout. Production Simple web,
SimpleOS, Engine2D, and Vulkan packages do not import it, link it, probe for it,
or select it as a fallback.

Chromium component libraries are implementation components, not an ABI. The
plugin owns the Chromium API calls and reduces them to a stable C ABI. This
avoids direct loading of `libblink`, `viz`, or arbitrary Chrome libraries.

```text
HTML/CSS fixture + normalized input script
       |                                 |
Simple private DOM/style/layout ----> DrawIrComposition ---> Engine2D/Vulkan
       |                                 |                         |
       +--> SimplePrimitiveTraceConverter +--> NormalizedTrace <---+ GPU receipt
                                                     ^
fixture --> test-only dynload --> ChromiumPrimitiveOracleBridge --+
                         (pinned Chromium, out-of-process optional)
```

`common.spec.differential_trace` remains the only common trace schema;
`DrawIrComposition` remains the only shared display list. `web_layout` and
`web_paint` retain their existing layer IDs. This capsule adds only canonical
trace values `web_dom`, `web_style`, `web_input`, and `web_gpu`.

## Frozen public interface names and owners

| Owner path | Frozen exports / purpose |
|---|---|
| `src/lib/nogc_sync_mut/gpu/chromium_reference_oracle_sffi.spl` | `ChromiumOracleAbi`, `ChromiumOracleLoadRequest`, `ChromiumOracleLoadResult`, `ChromiumOracleHandle`, `ChromiumOracleCallResult`, `ChromiumOracleGpuReceipt`; `chromium_oracle_load`, `chromium_oracle_validate_library_probe`, `chromium_oracle_run_primitive_fixture`, `chromium_oracle_release`, `chromium_oracle_gpu_receipt_valid`. This is test-only and compiled-mode only. |
| `test/helpers/web_chromium_reference_oracle.spl` | `ChromiumOraclePrimitiveFixture`, `ChromiumOracleNormalizedObservation`, `ChromiumPrimitiveTraceConverter`, `SimplePrimitiveTraceConverter`; `make_chromium_primitive_fixture`, `run_chromium_primitive_reference`, `chromium_oracle_normalize_trace`, `normalize_chromium_primitive_trace`, `normalize_simple_primitive_trace`, `assert_chromium_primitive_trace`, `assert_chromium_gpu_readback`. |
| `tools/chromium-primitive-oracle/` | Pinned Chromium `BUILD.gn`, C ABI header, bridge source, package manifest, symbol manifest. It is excluded from Simple production packaging. |
| `test/02_integration/rendering/chromium_web_renderer_primitive_differential_spec.spl` | Real fixture, negative/mutation, CPU pixel oracle, and GPU receipt scenarios; missing plugin is an explicit blocked/unavailable result, never PASS. |

Do not create `WebIR`, `GuiIR`, `ChromeTrace`, a second DrawIR executor, or a
separate GUI event model. The named converters only project existing states
into `NormalizedTrace`.

### Frozen struct fields and test seam

The first implementation must use these exact fields/constructor order;
additive changes require ABI/schema version review:

```simple
struct ChromiumOracleAbi:
    version: i64
    bridge_id: text
    chromium_revision: text

struct ChromiumOracleLoadRequest:
    library_path: text
    manifest_sha256: text
    expected_abi_version: i64
    required_symbols: [text]
    max_request_bytes: i64
    max_response_bytes: i64
    test_only: bool

struct ChromiumOracleResolvedSymbols:
    abi_version: i64
    create: i64
    run_json_into: i64
    last_error_into: i64
    destroy: i64

struct ChromiumOracleLibraryProbe:
    library_handle: i64
    manifest_sha256: text
    abi: ChromiumOracleAbi
    symbols: ChromiumOracleResolvedSymbols

struct ChromiumOracleHandle:
    library_handle: i64
    session_handle: i64
    library_path: text
    abi_version: i64
    released: bool

struct ChromiumOracleLoadResult:
    ok: bool
    status: text
    library_path: text
    abi: ChromiumOracleAbi
    handle: ChromiumOracleHandle?
    error: text

struct ChromiumOracleCallResult:
    ok: bool
    status: text
    response_json: text
    response_bytes: i64
    error: text

struct ChromiumOracleGpuReceipt:
    requested_api: text
    executed_api: text
    device_identity: text
    fence_signaled: bool
    readback_source: text
    readback_digest: text
    fallback_used: bool

struct ChromiumOraclePrimitiveFixture:
    fixture_id: text
    viewport_width: i64
    viewport_height: i64
    device_scale_milli: i64
    font_identity: text
    font_digest: text
    image_digest: text
    image_width: i64
    image_height: i64
    html_css: text
    event_script: text
    requested_primitives: [text]
    requires_gpu_receipt: bool

struct ChromiumOracleNormalizedObservation:
    fixture_id: text
    trace: NormalizedTrace
    cpu_pixel_digest: text
    cpu_pixel_width: i64
    cpu_pixel_height: i64
    gpu_receipt: ChromiumOracleGpuReceipt?
    artifact_path: text
```

The function surface is exactly `chromium_oracle_load`,
`chromium_oracle_validate_library_probe`,
`chromium_oracle_run_primitive_fixture`, `chromium_oracle_release`, and
`chromium_oracle_gpu_receipt_valid`. The sole approved fake-library seam is
the pure `chromium_oracle_validate_library_probe(request, probe)` function:
unit tests construct `ChromiumOracleLibraryProbe` records to cover loader
classification. `chromium_oracle_load` exclusively creates actual `DynLib`
objects and an injected fixture/response/fake-dynload mode is forbidden.
Native addresses are confined to `ChromiumOracleResolvedSymbols` and
`ChromiumOracleHandle`; no converter may read them.

`ChromiumOraclePrimitiveFixture` has the exact constructor fields above.
`device_scale_milli` is `1000` in v1; another value is
`unsupported-primitive`. Empty `image_digest`/zero image dimensions mean no
image primitive and cannot fake one. `event_script` is canonical JSON ordered
input; `requested_primitives` is sorted unique and only contains `rect`,
`background`, `border`, `text`, `image`, `pointer`, `keyboard`, `scroll`,
`resize`, or `linear-path`. `html_css` is bounded inline fixture material and
never a URL. `artifact_path` is human evidence only, not comparator input.

Frozen helper signatures are:

```simple
fn make_chromium_primitive_fixture(
    fixture_id: text, viewport_width: i64, viewport_height: i64,
    html_css: text, event_script: text, requested_primitives: [text]
) -> ChromiumOraclePrimitiveFixture

fn run_chromium_primitive_reference(
    handle: ChromiumOracleHandle, fixture: ChromiumOraclePrimitiveFixture
) -> ChromiumOracleCallResult

fn chromium_oracle_normalize_trace(
    fixture: ChromiumOraclePrimitiveFixture, response_json: text,
    profile: GpuEnvironmentProfile
) -> ChromiumOracleNormalizedObservation?

fn normalize_chromium_primitive_trace(
    fixture: ChromiumOraclePrimitiveFixture, response_json: text,
    profile: GpuEnvironmentProfile
) -> ChromiumOracleNormalizedObservation?

fn normalize_simple_primitive_trace(
    fixture: ChromiumOraclePrimitiveFixture, trace: NormalizedTrace,
    cpu_pixel_digest: text, cpu_pixel_width: i64, cpu_pixel_height: i64,
    gpu_receipt: ChromiumOracleGpuReceipt?
) -> ChromiumOracleNormalizedObservation

fn assert_chromium_primitive_trace(
    chromium: ChromiumOracleNormalizedObservation,
    simple: ChromiumOracleNormalizedObservation
) -> TraceComparison

fn assert_chromium_gpu_readback(
    simple: ChromiumOracleNormalizedObservation,
    profile: GpuEnvironmentProfile
) -> TraceComparison
```

`normalize_chromium_primitive_trace` delegates to
`chromium_oracle_normalize_trace`; it is a readable test-helper alias rather
than a second converter. The fixture factory supplies v1 defaults
`device_scale_milli=1000`, no image, and `requires_gpu_receipt=false`.

## C ABI v1

The bridge uses fixed-width C ABI and no C++/Chromium object crosses the
boundary. Required symbols, all `extern "C"`:

```c
uint32_t simple_chromium_oracle_abi_version(void);
int64_t simple_chromium_oracle_create(const uint8_t* config, uint64_t config_len);
int32_t simple_chromium_oracle_run_json_into(int64_t handle,
    const uint8_t* request, uint64_t request_len, uint8_t* response,
    uint64_t response_capacity, uint64_t* response_len);
int32_t simple_chromium_oracle_last_error_into(int64_t handle,
    uint8_t* response, uint64_t response_capacity, uint64_t* response_len);
int32_t simple_chromium_oracle_destroy(int64_t handle);
```

`ChromiumOracleAbi.version == 1`; loader requires exactly this version and all
five symbols before it creates a handle. `create` returns a positive opaque
handle or `0`; handles are process-local and may not appear in traces. Request
and response memory are caller-owned, bounded (v1: request <= 1 MiB, response
<= 4 MiB), UTF-8 JSON, and copied before the call returns. `response_len` is
the required byte length excluding a terminal NUL; too-small output returns
`buffer-too-small` without partial JSON. The bridge never returns or owns an
output allocation. A successful create has exactly one `destroy`, including after a
failed call. `destroy(0)`/repeat destroy are rejected as `released-handle`.

Stable status/error classes are: `ok`, `library-not-found`, `symbol-missing`,
`abi-mismatch`, `invalid-request`, `unsupported-primitive`, `adapter-failure`,
`invalid-response`, `buffer-too-small`, `device-receipt-missing`,
`fallback-forbidden`, and `released-handle`. Native text is copied into a
bounded Simple error value; neither pointer values nor raw Chromium diagnostics
enter a trace.

## Canonical normalized input/output

`ChromiumOraclePrimitiveFixture` is canonical JSON v1, in UTF-8 and sorted
object-key order. It contains `fixture_id`, viewport `{width,height,dpr=1}`, a
font identity/digest, image digest and intrinsic size, HTML/CSS subset, and an
ordered event script. Geometry is integer CSS px after deterministic
round-half-away-from-zero; colors are non-premultiplied RGBA8; text facts are
UTF-8 digest, font digest, ascent/descent/advance in 1/64 CSS px; image facts
are placement/intrinsic-size/digest; rectangle/border/path facts are bounds,
stroke width and RGBA8. IDs are fixture-local deterministic IDs, never DOM
addresses or engine node IDs.

The event script has monotonic sequence, `pointer_move`, `pointer_down`,
`pointer_up`, `click`, `key_down`, `key_up`, `scroll`, and `resize`; key facts
include physical/key code and separate `ctrl_left`, `ctrl_right`, `alt_left`,
`alt_right` booleans. `web_input` records target ID, default-action class,
scroll/viewport result, and modifier facts. Event order, target, geometry, and
post-event focus/scroll facts compare exactly. Synthetic dispatcher success is
not enough.

The trace response root uses the existing `NormalizedTrace` key set exactly:
`schema_version`, `run_id`, `environment_profile_id`,
`ui_environment_profile_id`, `arch`, `transport`, `enabled_features`,
`venus_version`, `device_identity`, `oracle_identity`,
`device_origin_readback`, `fallback_used`, `dropped_events`, `complete`, and
`events`. Each event uses the existing `TraceEvent` key set exactly. Its
`scalar_fields` is sorted ASCII `key=value` pairs separated by `;`; values use
percent escaping for `%`, `;`, and `=` (`%25`, `%3B`, `%3D`). Required keys
are primitive-specific canonical bounds/RGBA/font/text/image/event/fence/
readback facts. Raw text, DOM/object addresses, native handles, and timestamps
other than the existing run-relative event `monotonic_ns` are invalid.

Each adapter produces a `NormalizedTrace` with event operation facts:

| Layer | Required primitive projection |
|---|---|
| `web_dom` | fixture tree identity/tag/text-resource digests only |
| `web_style` | background/border/text/image/path supported-state facts |
| `web_layout` | box bounds, baseline, image placement, scroll/viewport result |
| `web_paint` | ordered primitive op and canonical material/geometry digest |
| `web_input` | source event, target, modifiers, default action, post-state |
| `web_gpu` | requested/executed API, device identity, fence, readback source/digest, fallback class |

The final CPU oracle uses exact RGBA8 output from the existing Simple CPU
Engine2D route. A Chrome-vs-Simple semantic match does not replace final pixel
comparison. A Simple GPU match requires its own Vulkan fence, positive device
identity, `device_readback`, exact digest, and `fallback_used=false` under the
existing profile. Chrome GPU status is comparative metadata only.

## Packaging, isolation, and lifecycle

`tools/chromium-primitive-oracle/BUILD.gn` must expose one named bridge target
and generate `chromium_oracle_manifest.json` containing pinned revision,
platform/arch, ABI version, SHA-256, required symbol list, and bridge build
arguments. Test setup receives an explicit absolute library path and manifest;
there is no ambient library-name search or production environment variable.
The test process caches one validated library per `(path, SHA-256, ABI)` for a
test session and one live handle per fixture; it never loads per trace event.

The test plugin may run Chromium in a child process internally, but a crash,
timeout, sandbox denial, absent GPU, or malformed output becomes
`adapter-failure` and makes the scenario unavailable/failed according to its
assertion. It cannot fall back to a JS script, a screenshot, a synthetic record,
or the production Chrome wrapper.

## Performance and negative gates

Live acceptance records one cold library validation and 20 warm fixtures:
plugin-init p95 <= 2 s, normalizer p95 <= 5 ms for <= 512 events, trace <= 512
events and <= 1 MiB, peak bridge RSS <= 1 GiB, and Simple GPU submit-to-readback
p95 is profile-owned (not inferred from Chrome). These are gates only on a
named host/device/profile; absent hardware is blocked, not timed as zero.

Mutations independently change DOM parent/tag digest, style background/border,
layout box/baseline, paint operation/order, image digest, event target/modifier,
scroll/resize result, path geometry, pixel digest, fence/readback source,
fallback bit, ABI, symbol, ownership, response encoding, sequence/order and
event limit. Every altered field must reject; unknown primitive and absent
linear-path support must return `unsupported-primitive` before comparison.
