# Pure Simple Vulkan context admission

This device-free unit contract proves that Engine2D refuses to claim async
authority without a provider binding for the exact live Vulkan session,
framebuffer, and presenter target. The unavailable production path does not
serialize DrawIR; the canonical candidate codec is checked separately.

## Scenario: invalid capacity

1. Construct an Engine2D CPU surface.
2. Query `vulkan_async_admission` with capacity `2`.
3. Verify status `rejected`, reason `async-capacity-out-of-range`, and
   `async_claim=false`.

## Scenario: unavailable path avoids serialization

1. Construct an Engine2D CPU surface and a canonical DrawIR composition.
2. Query `vulkan_async_admission` with capacity `3`.
3. Verify status `unavailable`, zero packet bytes/checksum,
   `context_binding_supported=false`, and `async_claim=false`.

## Scenario: canonical candidate packet

1. Encode a real rectangle composition through the bounded canonical codec.
2. Verify one command and nonempty bytes.
3. Encode a malformed composition with no identity.
4. Verify explicit `missing-composition-id` rejection.

## Scenario: caller-populated handles

1. Populate positive session/device/framebuffer fields without provider
   binding authority.
2. Verify the unavailable result publishes zero identities and no async claim.

## Scenario: synchronous fallback

1. Render the real window-present consumer with a software backend.
2. Verify the rectangle still renders and presentation fails for the existing
   `vulkan-window-present-failed` reason.
3. Verify async status is unavailable, checksum is zero, and no claim is made.

## Scenario: evidence summary

1. Query the same gate.
2. Verify the summary exposes `packet_ok=false`,
   `context_binding=false`, and `async_claim=false`.

The window-present production route records status, reason, a zero packet
checksum, and `async_claim=false` in `Engine2dDrawIrAdvResult`, then preserves
synchronous rendering until a checked provider context-binding operation
exists.
