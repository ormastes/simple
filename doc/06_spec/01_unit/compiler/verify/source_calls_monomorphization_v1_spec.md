# Source monomorphization call identity scenarios

Manual source companion. Eight actual public API scenarios are authored and UNRUN: explicit generic call, inferred bool call, repeated specialization deduplication, distinct i64/bool signatures, nested worklist requests, a failed invocation between changed same-name bodies, nongeneric control and explicit aarch64 target retention.

Each success must pass the existing final call-manifest validator. Every retained binding is compared with the actual final MIR declaration signature/body hashes, and every inventory remains NOT_CHECKED. These assertions do not execute machine code or prove a program. The initial tests-first snapshot is preserved in the C1-SM packet. Broader default, ownership, G7 and limit checks have separate actual API specifications.
