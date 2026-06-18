# Async Web Framework Dispatcher GPU Adoption

> These scenarios verify the production dispatcher adoption path for GPU web route accounting. Controller responses remain CPU-authoritative while configured coarse routes may record GPU dispatch evidence through the shared web/database offload facade.

<!-- sdn-diagram:id=dispatcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dispatcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dispatcher_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dispatcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Web Framework Dispatcher GPU Adoption

These scenarios verify the production dispatcher adoption path for GPU web route accounting. Controller responses remain CPU-authoritative while configured coarse routes may record GPU dispatch evidence through the shared web/database offload facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the production dispatcher adoption path for GPU web
route accounting. Controller responses remain CPU-authoritative while
configured coarse routes may record GPU dispatch evidence through the shared
web/database offload facade.

## Examples

Register normal controller actions, opt a route into `WebGpuRouteKind.Rank`,
and call `dispatch_with_gpu_adoption` to inspect the offload evidence.

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md
**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md
**Design:** doc/05_design/gpu_web_db_offload.md
**Research:** N/A

## Scenarios

### async web framework dispatcher GPU adoption

#### should execute matched GPU route adoption while preserving controller response

- Route a configured controller action through dispatcher offload adoption
- var router = WebRouter new
- router = router post
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher register gpu route
- dispatcher = dispatcher configure gpu offload
- dispatch request
- dispatch location
- dispatch request
- dispatch location
   - Expected: adoption.reason equals `matched-gpu-route-config`
   - Expected: adoption.execution.offload.submission.dispatch_target equals `gpu_web_rank_batch`
   - Expected: adoption.execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`
   - Expected: adoption.execution.response.body equals `{"ranked":true}`
   - Expected: response.body equals `{"ranked":true}`
   - Expected: response.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route a configured controller action through dispatcher offload adoption")
var router = WebRouter.new()
router = router.post("/rank", "rank", "create")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("rank", "create", rank_create)
dispatcher = dispatcher.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)
dispatcher = dispatcher.configure_gpu_offload("cuda", 1, ["gpu_web_rank_batch"], true)

val adoption = dispatcher.dispatch_with_gpu_adoption(
    dispatch_request("POST", "/rank", {}),
    dispatch_location()
)
val response = dispatcher.dispatch(
    dispatch_request("POST", "/rank", {}),
    dispatch_location()
)

expect(adoption.matched).to_be(true)
expect(adoption.reason).to_equal("matched-gpu-route-config")
expect(adoption.execution.offload.submission.dispatch_target).to_equal("gpu_web_rank_batch")
expect(adoption.execution.offload.gpu_dispatched).to_be(true)
expect(adoption.execution.offload.cpu_authoritative).to_be(true)
expect(adoption.execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(adoption.execution.response.body).to_equal("{\"ranked\":true}")
expect(response.body).to_equal("{\"ranked\":true}")
expect(response.status).to_equal(200)
```

</details>

#### should keep unconfigured dispatcher actions on CPU without fake GPU evidence

- Route an unconfigured controller action through CPU-owned fallback
- var router = WebRouter new
- router = router get
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher configure gpu offload
- dispatch request
- dispatch location
   - Expected: adoption.reason equals `no-gpu-route-config`
   - Expected: adoption.execution.offload.route_kind equals `WebGpuRouteKind.HttpControlPlane`
   - Expected: adoption.execution.offload.submission.dispatch_target equals `cpu_fallback`
   - Expected: adoption.execution.offload.submission.reason equals `control-plane-stays-on-cpu`
   - Expected: adoption.execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.CpuOnly`
   - Expected: adoption.execution.response.body equals `{"status":"ok"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route an unconfigured controller action through CPU-owned fallback")
var router = WebRouter.new()
router = router.get("/health", "health", "show")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("health", "show", health_show)
dispatcher = dispatcher.configure_gpu_offload("cuda", 1, ["gpu_web_rank_batch"], true)

val adoption = dispatcher.dispatch_with_gpu_adoption(
    dispatch_request("GET", "/health", {}),
    dispatch_location()
)

expect(adoption.matched).to_be(false)
expect(adoption.reason).to_equal("no-gpu-route-config")
expect(adoption.execution.offload.route_kind).to_equal(WebGpuRouteKind.HttpControlPlane)
expect(adoption.execution.offload.gpu_dispatched).to_be(false)
expect(adoption.execution.offload.submission.dispatch_target).to_equal("cpu_fallback")
expect(adoption.execution.offload.submission.reason).to_equal("control-plane-stays-on-cpu")
expect(adoption.execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.CpuOnly)
expect(adoption.execution.response.body).to_equal("{\"status\":\"ok\"}")
```

</details>

#### should configure dispatcher GPU adoption from a reusable web profile

- Use a named web GPU profile instead of raw target registration
- var router = WebRouter new
- router = router post
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher register gpu route
- dispatcher = dispatcher configure gpu profile
- dispatch request
- dispatch location
   - Expected: adoption.execution.offload.submission.dispatch_target equals `gpu_web_rank_batch`
   - Expected: adoption.execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use a named web GPU profile instead of raw target registration")
var router = WebRouter.new()
router = router.post("/rank", "rank", "create")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("rank", "create", rank_create)
dispatcher = dispatcher.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)
dispatcher = dispatcher.configure_gpu_profile(web_gpu_profile_rank("cuda", 7, 4))

val adoption = dispatcher.dispatch_with_gpu_adoption(
    dispatch_request("POST", "/rank", {}),
    dispatch_location()
)

expect(adoption.matched).to_be(true)
expect(adoption.execution.offload.submission.dispatch_target).to_equal("gpu_web_rank_batch")
expect(adoption.execution.offload.gpu_dispatched).to_be(true)
expect(adoption.execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
```

</details>

#### should configure GPU route adoption through the WebApp facade

- Use WebApp ergonomic methods and dispatch through the configured app dispatcher
- var app = WebApp simple
- app = app post
- app = app register action
- app = app register gpu route
- app = app configure gpu profile
- dispatch request
- dispatch location
   - Expected: adoption.reason equals `matched-gpu-route-config`
   - Expected: adoption.execution.offload.submission.dispatch_target equals `gpu_web_rank_batch`
   - Expected: adoption.execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`
   - Expected: adoption.execution.response.body equals `{"ranked":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use WebApp ergonomic methods and dispatch through the configured app dispatcher")
var app = WebApp.simple("127.0.0.1:0").unwrap()
app = app.post("/rank", "rank", "create")
app = app.register_action("rank", "create", rank_create)
app = app.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)
app = app.configure_gpu_profile(web_gpu_profile_rank("cuda", 7, 4))

val adoption = app.dispatcher.dispatch_with_gpu_adoption(
    dispatch_request("POST", "/rank", {}),
    dispatch_location()
)

expect(adoption.matched).to_be(true)
expect(adoption.reason).to_equal("matched-gpu-route-config")
expect(adoption.execution.offload.submission.dispatch_target).to_equal("gpu_web_rank_batch")
expect(adoption.execution.offload.gpu_dispatched).to_be(true)
expect(adoption.execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(adoption.execution.response.body).to_equal("{\"ranked\":true}")
```

</details>

#### should replace matched dispatcher responses after native candidates match

- Expose validated web profile replacement through dispatcher GPU adoption
- var router = WebRouter new
- router = router post
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher register gpu route
- dispatcher = dispatcher configure gpu profile
- dispatch request
- dispatch location
- gpu wdb device backend
- build json
   - Expected: adoption.reason equals `matched-gpu-route-config`
   - Expected: adoption.execution.validated.validation_reason equals `production-gpu-web-response-match`
   - Expected: adoption.execution.response.body equals `{"ranked":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose validated web profile replacement through dispatcher GPU adoption")
var router = WebRouter.new()
router = router.post("/rank", "rank", "create")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("rank", "create", rank_create)
dispatcher = dispatcher.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)
dispatcher = dispatcher.configure_gpu_profile(web_gpu_profile_rank("cuda", 7, 4))

val adoption: WebFrameworkGpuRouteValidatedAdoption = dispatcher.dispatch_with_gpu_validated_adoption(
    dispatch_request("POST", "/rank", {}),
    dispatch_location(),
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_rank_batch"], true, "cuda-device-0"),
    7,
    build_json("{\"ranked\":true}"),
    100,
    190,
    47,
    "cuda-event"
)

expect(adoption.matched).to_be(true)
expect(adoption.reason).to_equal("matched-gpu-route-config")
expect(adoption.execution.validated.gpu_candidate_validated).to_be(true)
expect(adoption.execution.validated.validation_reason).to_equal("production-gpu-web-response-match")
expect(adoption.execution.validated.execution.cpu_authoritative).to_be(false)
expect(adoption.execution.response.body).to_equal("{\"ranked\":true}")
```

</details>

#### should keep unconfigured validated dispatcher routes CPU owned

- Avoid production replacement for actions without GPU route config
- var router = WebRouter new
- router = router get
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher configure gpu profile
- dispatch request
- dispatch location
- gpu wdb device backend
- build json
   - Expected: adoption.reason equals `no-gpu-route-config`
   - Expected: adoption.execution.validated.validation_reason equals `production-device-not-measured`
   - Expected: adoption.execution.response.body equals `{"status":"ok"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid production replacement for actions without GPU route config")
var router = WebRouter.new()
router = router.get("/health", "health", "show")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("health", "show", health_show)
dispatcher = dispatcher.configure_gpu_profile(web_gpu_profile_rank("cuda", 7, 4))

val adoption = dispatcher.dispatch_with_gpu_validated_adoption(
    dispatch_request("GET", "/health", {}),
    dispatch_location(),
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_rank_batch"], true, "cuda-device-0"),
    7,
    build_json("{\"status\":\"ok\"}"),
    100,
    190,
    47,
    "cuda-event"
)

expect(adoption.matched).to_be(false)
expect(adoption.reason).to_equal("no-gpu-route-config")
expect(adoption.execution.validated.gpu_candidate_validated).to_be(false)
expect(adoption.execution.validated.execution.cpu_authoritative).to_be(true)
expect(adoption.execution.validated.validation_reason).to_equal("production-device-not-measured")
expect(adoption.execution.response.body).to_equal("{\"status\":\"ok\"}")
```

</details>

#### should advance dispatcher queue state after validated native replacements

- Carry production native queue state across validated dispatcher requests
- var router = WebRouter new
- router = router post
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher register gpu route
- dispatcher = dispatcher configure gpu profile
- dispatch request
- dispatch location
- build json
- dispatch request
- dispatch location
- build json
   - Expected: first.execution.validated.profile.queue_state.submitted_count equals `1`
   - Expected: first.execution.validated.profile.queue_state.completed_count equals `1`
   - Expected: first.execution.validated.profile.queue_state.gpu_hit_count equals `1`
   - Expected: second.execution.validated.profile.queue_state.submitted_count equals `2`
   - Expected: second.execution.validated.profile.queue_state.completed_count equals `2`
   - Expected: second.execution.validated.profile.queue_state.gpu_hit_count equals `2`
   - Expected: second.execution.response.body equals `{"ranked":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Carry production native queue state across validated dispatcher requests")
var router = WebRouter.new()
router = router.post("/rank", "rank", "create")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("rank", "create", rank_create)
dispatcher = dispatcher.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)
dispatcher = dispatcher.configure_gpu_profile(web_gpu_profile_rank("cuda", 7, 4))
val backend = gpu_wdb_device_backend("cuda", 7, ["gpu_web_rank_batch"], true, "cuda-device-0")

val first = dispatcher.dispatch_with_gpu_validated_adoption_advancing(
    dispatch_request("POST", "/rank", {}),
    dispatch_location(),
    backend,
    7,
    build_json("{\"ranked\":true}"),
    100,
    190,
    47,
    "cuda-event"
)
val second = dispatcher.dispatch_with_gpu_validated_adoption_advancing(
    dispatch_request("POST", "/rank", {}),
    dispatch_location(),
    backend,
    7,
    build_json("{\"ranked\":true}"),
    200,
    290,
    49,
    "cuda-event"
)

expect(first.execution.validated.profile.queue_state.submitted_count).to_equal(1)
expect(first.execution.validated.profile.queue_state.completed_count).to_equal(1)
expect(first.execution.validated.profile.queue_state.gpu_hit_count).to_equal(1)
expect(second.execution.validated.profile.queue_state.submitted_count).to_equal(2)
expect(second.execution.validated.profile.queue_state.completed_count).to_equal(2)
expect(second.execution.validated.profile.queue_state.gpu_hit_count).to_equal(2)
expect(second.execution.validated.gpu_candidate_validated).to_be(true)
expect(second.execution.response.body).to_equal("{\"ranked\":true}")
```

</details>

#### should preserve CPU fallback from a reusable CPU-only web profile

- Use a named CPU-only profile to disable GPU evidence
- var router = WebRouter new
- router = router post
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher register gpu route
- dispatcher = dispatcher configure gpu profile
- dispatch request
- dispatch location
   - Expected: adoption.execution.offload.submission.dispatch_target equals `cpu_fallback`
   - Expected: adoption.execution.offload.submission.reason equals `gpu-unavailable`
   - Expected: adoption.execution.response.body equals `{"ranked":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use a named CPU-only profile to disable GPU evidence")
var router = WebRouter.new()
router = router.post("/rank", "rank", "create")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("rank", "create", rank_create)
dispatcher = dispatcher.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)
dispatcher = dispatcher.configure_gpu_profile(web_gpu_profile_cpu_only("web-maintenance"))

val adoption = dispatcher.dispatch_with_gpu_adoption(
    dispatch_request("POST", "/rank", {}),
    dispatch_location()
)

expect(adoption.matched).to_be(true)
expect(adoption.execution.offload.gpu_dispatched).to_be(false)
expect(adoption.execution.offload.submission.dispatch_target).to_equal("cpu_fallback")
expect(adoption.execution.offload.submission.reason).to_equal("gpu-unavailable")
expect(adoption.execution.response.body).to_equal("{\"ranked\":true}")
```

</details>

#### should validate mixed non-inference WebApp routes through the all GPU profile

- Carry app-level transform and embedding routes through validated native adoption
- var app = WebApp simple
- app = app post
- app = app post
- app = app register action
- app = app register action
- app = app register gpu route
- app = app register gpu route
- app = app configure gpu profile
- dispatch request
- dispatch location
- build json
- dispatch request
- dispatch location
- build json
   - Expected: embedding.execution.validated.execution.submission.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: embedding.execution.response.body equals `{"embedding":[1,2,3]}`
   - Expected: transform.execution.validated.execution.submission.dispatch_target equals `gpu_web_transform_batch`
   - Expected: transform.execution.validated.profile.queue_state.submitted_count equals `2`
   - Expected: transform.execution.validated.profile.queue_state.completed_count equals `2`
   - Expected: transform.execution.validated.profile.queue_state.gpu_hit_count equals `2`
   - Expected: transform.execution.response.body equals `{"transformed":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Carry app-level transform and embedding routes through validated native adoption")
var app = WebApp.simple("127.0.0.1:0").unwrap()
app = app.post("/embed", "embed", "create")
app = app.post("/transform", "transform", "update")
app = app.register_action("embed", "create", embed_create)
app = app.register_action("transform", "update", transform_update)
app = app.register_gpu_route("embed", "create", WebGpuRouteKind.Embedding, 16, 512)
app = app.register_gpu_route("transform", "update", WebGpuRouteKind.Transform, 8, 1024)
app = app.configure_gpu_profile(web_gpu_profile_all("cuda", 7, 4))
val backend = gpu_wdb_device_backend(
    "cuda",
    7,
    ["gpu_web_embedding_batch", "gpu_web_transform_batch"],
    true,
    "cuda-device-0"
)

val embedding = app.dispatcher.dispatch_with_gpu_validated_adoption_advancing(
    dispatch_request("POST", "/embed", {}),
    dispatch_location(),
    backend,
    7,
    build_json("{\"embedding\":[1,2,3]}"),
    100,
    180,
    43,
    "cuda-event"
)
val transform = app.dispatcher.dispatch_with_gpu_validated_adoption_advancing(
    dispatch_request("POST", "/transform", {}),
    dispatch_location(),
    backend,
    7,
    build_json("{\"transformed\":true}"),
    200,
    290,
    51,
    "cuda-event"
)

expect(embedding.matched).to_be(true)
expect(embedding.execution.validated.gpu_candidate_validated).to_be(true)
expect(embedding.execution.validated.execution.submission.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(embedding.execution.response.body).to_equal("{\"embedding\":[1,2,3]}")
expect(transform.matched).to_be(true)
expect(transform.execution.validated.gpu_candidate_validated).to_be(true)
expect(transform.execution.validated.execution.submission.dispatch_target).to_equal("gpu_web_transform_batch")
expect(transform.execution.validated.profile.queue_state.submitted_count).to_equal(2)
expect(transform.execution.validated.profile.queue_state.completed_count).to_equal(2)
expect(transform.execution.validated.profile.queue_state.gpu_hit_count).to_equal(2)
expect(transform.execution.response.body).to_equal("{\"transformed\":true}")
```

</details>

#### should keep configured WebApp proxy forwarding CPU owned under the all GPU profile

- Prevent proxy control-plane routes from claiming GPU dispatch through product config
- var app = WebApp simple
- app = app post
- app = app register action
- app = app register gpu route
- app = app configure gpu profile
- dispatch request
- dispatch location
   - Expected: adoption.reason equals `matched-gpu-route-config`
   - Expected: adoption.execution.offload.route_kind equals `WebGpuRouteKind.ProxyForwarding`
   - Expected: adoption.execution.offload.submission.dispatch_target equals `cpu_fallback`
   - Expected: adoption.execution.offload.submission.reason equals `control-plane-stays-on-cpu`
   - Expected: adoption.execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.CpuOnly`
   - Expected: adoption.execution.response.body equals `{"proxied":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prevent proxy control-plane routes from claiming GPU dispatch through product config")
var app = WebApp.simple("127.0.0.1:0").unwrap()
app = app.post("/proxy", "proxy", "forward")
app = app.register_action("proxy", "forward", proxy_forward)
app = app.register_gpu_route("proxy", "forward", WebGpuRouteKind.ProxyForwarding, 1, 4096)
app = app.configure_gpu_profile(web_gpu_profile_all("cuda", 7, 4))

val adoption = app.dispatcher.dispatch_with_gpu_adoption(
    dispatch_request("POST", "/proxy", {}),
    dispatch_location()
)

expect(adoption.matched).to_be(true)
expect(adoption.reason).to_equal("matched-gpu-route-config")
expect(adoption.execution.offload.route_kind).to_equal(WebGpuRouteKind.ProxyForwarding)
expect(adoption.execution.offload.gpu_dispatched).to_be(false)
expect(adoption.execution.offload.submission.dispatch_target).to_equal("cpu_fallback")
expect(adoption.execution.offload.submission.reason).to_equal("control-plane-stays-on-cpu")
expect(adoption.execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.CpuOnly)
expect(adoption.execution.response.body).to_equal("{\"proxied\":true}")
```

</details>

#### should return normal dispatcher errors without GPU route side effects

- Reject missing routes before any configured GPU action can match
- var router = WebRouter new
- router = router post
- var dispatcher = AppDispatcher new
- dispatcher = dispatcher register action
- dispatcher = dispatcher register gpu route
- dispatch request
- dispatch location
   - Expected: response.status equals `404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject missing routes before any configured GPU action can match")
var router = WebRouter.new()
router = router.post("/rank", "rank", "create")
var dispatcher = AppDispatcher.new(router)
dispatcher = dispatcher.register_action("rank", "create", rank_create)
dispatcher = dispatcher.register_gpu_route("rank", "create", WebGpuRouteKind.Rank, 8, 512)

val response = dispatcher.dispatch(
    dispatch_request("GET", "/missing", {}),
    dispatch_location()
)

expect(response.status).to_equal(404)
expect(response.body).to_contain("No route matches")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
