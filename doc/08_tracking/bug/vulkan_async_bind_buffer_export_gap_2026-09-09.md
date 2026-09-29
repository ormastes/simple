# Vulkan async managed buffer binding has no canonical implementation

Status: REPAIRED AT THE PURE-SIMPLE BOUNDARY; production capability remains
unsupported at
`e5e4b75cfa2b8d8f325d0fa4bdad647df62b03f9`.

`src/lib/gc_async_mut/gpu/engine2d/vulkan_async_submission.spl` imports and
calls `vulkan_sffi_async_session_bind_buffer`. Its GC async facade re-exports
the no-GC async facade, whose explicit export list also names the function.
However, the canonical owner
`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` defines neither that wrapper
nor an `rt_vulkan_async_session_bind_buffer` declaration. The current
`src/compiler_rust/runtime/src` provider sources also contain no such symbol.
The uncommitted background resource-admission evidence cannot establish that
this commit contains its implementation.

## Effect and safe repair

The called import had no canonical implementation. Import-only or syntax-only
success could not prove an executable managed resource path. The Pure Simple
boundary now resolves the import/export with a compatibility-preserving Pure
Simple wrapper and exposes `vulkan_async_session_bind_buffer_supported() ==
false`; valid binding calls return `VULKAN_ASYNC_BIND_UNSUPPORTED` without any
native invocation. This repairs the source/export gap but does not admit
managed resource binding or unblock the new device port's separate
context/presenter authority gaps.

The Pure Simple repair must preserve the documented unsupported result when
no checked native operation exists. It must not forward to legacy
`vulkan_sffi_bind_buffer`, invent a successful return, or advertise resource
admission merely because the older optional B/N2 symbols are present. If
adding the checked operation, land its actual backend implementation,
canonical SFFI owner, compatibility exports and required optional-loader
registration together. Keep backend absence distinct from malformed input.

## Acceptance

- Every exported/called name resolves through the canonical owner (PASS for
  the Pure Simple source boundary; no supported bind operation is advertised).
- Unsupported providers reject the call before descriptor/resource mutation.
- A supported provider validates the live context and exact recording token,
  resource ownership/generations, descriptor binding, range overflow and access
  conflicts, and retains dependencies until their actual consumers release.
- Real draw recording and post-submit retention are exercised through the
  Pure Simple production path before support is admitted. Source checks and
  background Rust tests alone do not satisfy this criterion.

This bug was found by source inspection; no compiler/test/runtime failure was
executed or inferred as a completed test. The remaining production dependency
and package order are in the
[Astra device-port review](../../09_report/gpu_async_device_port_v2_astra_review_2026-09-09.md).
