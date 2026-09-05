# Spec: svLLM Tensor-Pack Manifest Loader

Source: `test/01_unit/lib/gc_async_mut/svllm/model_loader_manifest_spec.spl`

## Behavior

- Canonical v0 manifest text parses into a `TensorPackManifest`.
- Malformed text and unsupported schema versions return typed errors.
- Already-read empty manifest text can load into an empty `TensorPack`.
- Canonical non-empty manifest text materializes tensor and chunk metadata into
  a `TensorPack`.
- Tensors referencing missing chunk ids are rejected.
- Non-empty chunks must carry a 64-character lowercase SHA-256 hex digest.
- Filesystem-backed pack loading reads `manifest.sdn` from the pack root and
  materializes the same metadata path.
- Pack-root loading verifies declared chunk files exist, match declared byte
  length, and match declared SHA-256 hex when one is provided.

## Covered Requirement

- svLLM manifest parsing and model-pack loading must be explicit, non-throwing,
  and must not masquerade as ready when live pack loading is still unavailable.

## Not Covered

- Tensor byte range extraction. Covered separately by
  `doc/06_spec/01_unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.md`.
- Runtime tensor streaming.
