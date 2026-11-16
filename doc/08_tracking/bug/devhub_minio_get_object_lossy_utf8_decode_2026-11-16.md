# devhub minio_get_object decoded non-UTF-8 bodies lossily

Status: verification-pending

`src/app/devhub/adapter_minio.spl` `_minio_get_checked` used `bytes_to_text`, so a binary
(non-UTF-8) object came back as `ok=true` with corrupted text. All callers (`itf minio get`,
`storage cat`, `llm_caret storage_get`) print/consume text, so the minimal correct fix is
fail-closed: strict `validated_utf8_bytes_to_text_linear`; on failure `minio_get_object` returns
`(false, empty, "object body is invalid UTF-8: ...; use minio_download for binary objects")`
without retrying. Binary callers use `minio_download`.

Evidence: `test/03_system/app/devhub/feature/devhub_minio_emulated_spec.spl` scenario
"refuses a non-UTF-8 object body instead of returning corrupted text" (emulator gained `hex:` raw bodies).
RED 24/25 -> GREEN 25/25 on the tip seed. Not covered: native-build run; `src/app/itf/adapter_minio.spl`
has a separate copy of the adapter (not changed here).
