# Recursive MirType payload native regression

Status: UNRUN. Fixture: `test/fixtures/compiler/mir_type_recursive_payload_native.spl`.

The fixture calls the six production MirType factories: ptr, result, promise, generator, actor_type and scalable_vec. It inspects the concrete enum tag and every supplied payload, with distinct primitive leaves to detect reordered slots. It also checks both pointer mutability flags, lane counts 1 and 4, and a nested Promise<Result<I16,U32>>. Nine factory calls execute; there is no copied constructor implementation.

Compile and link with the admitted pure-Simple native producer and paired runtime, then execute the actual resulting binary. Success requires exit zero and `mir_type_recursive_payload_native=PASS factories=6 calls=9`. Compile success alone is insufficient. A failure in any payload/tag check exits nonzero. This check does not certify layout across every target, memory/performance, or the complete Phase3 build.
