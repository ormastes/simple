# Native GPU environment task authority bridge V1

This executable specification is for compiler/runtime owners integrating
environment-selected GPU work. It verifies that native provider, resource,
device-image and completion records remain distinct typed capabilities.

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

## Scenario: reject invalid live handles

Given a zero provider/session handle, resource-lease projection returns
`ProviderAuthorityUnavailable` before attempting an FFI call or creating a
lease.

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
