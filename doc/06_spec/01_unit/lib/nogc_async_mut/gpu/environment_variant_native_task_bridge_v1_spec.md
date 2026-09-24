# Native GPU environment task authority bridge V1

This authored specification is for compiler/runtime owners integrating
environment-selected GPU work. It checks shape comparisons and fail-closed
entry into the typed provider, resource, image, and completion bridge APIs.

## Preconditions

- The hosted provider registry may expose provider/resource/completion tokens.
- No runtime-owned exact device-program image token exists yet.
- `FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE` remains false.

## Scenario: match facts without granting authority

Given provider and resource projections with the expected backend, session,
generation, device, artifact and capacity, the bridge can compare their typed
shape. This comparison is deliberately not a live-authority or execution
receipt; production consumption reprojects each runtime token.

Native backend identifiers larger than the registry's unsigned 32-bit width
are rejected before conversion. A runtime-owned resource one byte smaller than
the bounded task arena is rejected rather than rounded or widened.

The standalone admission boundary independently compares the task's resource
layout, required effects, numerical contract, and arena capacity against the
retained image, lease, and enabled-device limits. It does not rely on a caller
having passed through task preparation first.

## Scenario: reject invalid live handles

Given a zero provider/session handle, resource-lease projection returns
`ProviderAuthorityUnavailable` before attempting an FFI call or creating a
lease. Admission and completion consumption return the same failure before
touching image, resource, or completion handles. The retained task-owner path
is present in source but is not exercised by this focused spec.

## Scenario: require exact image ownership

The device-image authority and physical-execution gates are both false. A
zero image handle is rejected without FFI. A required GPU parser request
therefore returns `RequiredProviderUnavailable`; it never executes CPU
fallback and never labels routing as device execution.

## Evidence status and limitations

This is authored source/manual evidence, not a generated or executed SPipe
PASS. Physical qualification still requires a runtime-owned exact image lease,
a Vulkan parser kernel, correlated device readback and retirement, negative
controls, and an admitted self-hosted runner on a real device.
