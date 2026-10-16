# CUDA core plugin: make it loadable (design intent for the proper fix)

Date: 2026-10-15
Raised by: user, during the release_phase3 full-bootstrap bring-up.
Related workaround: `241ad458791 fix(compositions): sync cuda_static
selected_cuda_backend to the live template` (bytes synced so the bootstrap
CUDA composition identity gate passes).

## Intent

The proper fix must not keep CUDA as a static, startup-identity-gated
composition. The CUDA core plugin should be **loadable**: selected and
loaded dynamically at use-time, the way `runtime_sdl2` already works
(dlopens SDL2 at first use instead of binding it at link time), so:

- the bootstrap does not hard-depend on a CUDA composition's byte identity
  to start (the current gate fails startup when the canonical composition
  drifts from the selected template — a recurring single-point failure);
- hosts without CUDA still build and run (selection becomes a no-op stub
  until a CUDA provider is demanded);
- composition regeneration does not invalidate admitted producers.

## Direction

Move `selected_cuda_backend` selection behind the existing
backend-plugin / dynload provider path (`runtime_backend_plugin`,
`SIMPLE_NATIVE_RUNTIME_BUNDLE`, the `runtime_dynload` lane) so the
identity gate validates only a small, stable loader shim, and the real
CUDA backend registers itself when loaded. Keep the static composition
files as build-time evidence, not as runtime authority.
