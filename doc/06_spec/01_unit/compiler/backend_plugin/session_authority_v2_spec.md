# Backend session generation and compile-use authority V2

The executable spec is [`session_authority_v2_spec.spl`](../../../../../test/01_unit/compiler/backend_plugin/session_authority_v2_spec.spl).

The owner loads an admitted backend, issues an owner-bound generation token, and retains the session through a compile use. Closing stops new uses, waits for existing uses to drain, and releases the provider only after successful teardown. The spec checks actual object emission, one-use execution, foreign and replayed tokens, failed loader admission, rejected unconfirmed CPU feature requests, and close ordering.

This covers the Stage 6A.1a lifetime boundary. It does not issue backend-accepted features, exact object-byte evidence, instruction inspection, or executed SIMD proof; the existing V1 driver route has not moved to this owner.
