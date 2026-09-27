# Backend session generation and compile-use authority V2

The executable spec is [`session_authority_v2_spec.spl`](../../../../../test/01_unit/compiler/backend_plugin/session_authority_v2_spec.spl).

The owner loads an admitted backend, issues an owner-bound generation token, and retains the session through a compile use. Closing stops new uses, waits for existing uses to drain, and releases the provider only after successful teardown. The spec checks actual object emission, one-use execution, foreign and replayed tokens, failed loader admission, rejected unconfirmed CPU feature requests, close ordering, and Cranelift AOT object-path emission through the driver facade.

The result-envelope scenarios compile a real MIR module, retain a private copy of its object bytes, and project the byte count, byte SHA-256, and framed envelope SHA-256 with provider build identity, request target/CPU/options, and explicit `Unknown` feature acceptance. They mutate a caller copy and project again to check byte isolation. A live result prevents compile-use release; substituted and replayed result tokens are rejected. The result must be released before the use and session can retire.

The in-memory Cranelift AOT scenario retains the prepared AOT producer's object bytes through the same owner. Its envelope binds the compile kind and the requested target CPU, optimization level, and release mode. These values describe requests, not provider-confirmed CPU features.

The original scenarios cover the Stage 6A.1a lifetime boundary, including the live driver route through the owner. The in-memory module and AOT result paths cover the Stage 6A.1b token and byte-retention boundary. The live Cranelift facade now projects the retained AOT result before publishing the object with its existing file writer, then releases the result before its compile use. LLVM and dynamic V1 retain their existing object-path routes. V1 providers do not confirm requested CPU features, and this manual makes no instruction-inspection or execution claim.
