# Native temporary text reaches `rt_len` as an invalid handle

## Reproduction

The admitted Stage2 LLVM no-stub binary built from `test/fixtures/bootstrap_builder/binary_object_action_receipt_main.spl` exited 12 before receipt staging. Runtime stderr reported `rejected invalid array handle before dereference; probable compiler/FFI ABI mismatch`. A fresh-root `strace` showed the binary CAS object published and verified, followed by the diagnostic before any `simple-object-action` staging path opened.

A GDB write-syscall backtrace placed the diagnostic in `rt_len` called by `lib.common.text_bytes.text_to_utf8_bytes`, then `lib.common.crypto.sha256.sha256_text`, then `compiler.driver.cache.binary_object_action.binary_object_action_digest_v1`. The prior expression was `sha256_text(binary_object_action_encode_v1(action))`; the encoded temporary text reached `rt_len` with a nonregistered handle. Repeated attempts had different pointer bits but the same stack and failure. Logs: `/tmp/simple-target6-action-receipt-build-20261012.log`, `/tmp/simple-target6-action-receipt-gdb.log`, `/tmp/simple-target6-action-receipt-fresh-trace`.

## Scoped repair and remaining bug

The action owner now binds its canonical encoded text and hashes `encoded.bytes()` with `sha256_u8_hex`. This keeps the SHA-256 byte stream and bypasses `text_to_utf8_bytes` for the action digest. A native receipt fixture verifies publication, readback, equal publisher, and shadow comparison. The general native return/argument lowering for temporary `text` passed into `sha256_text` remains a compiler/runtime defect; other call sites may require a codegen-level fix. The action unit spec asserts digest equality with `sha256_text` when the full interpreter test runtime is available.
