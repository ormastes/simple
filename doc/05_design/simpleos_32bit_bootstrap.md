# SimpleOS 32-bit bootstrap detail design

The profile function maps each enum value to a complete record. Receipt validation is fail-fast and pure: version/profile, phases, hashes/lineage, then QEMU exit and four nonce-bound transcript markers. The marker sequence is `guest-entry`, filesystem execution, exact reap exit 37, and `TEST PASSED`.

Live producers must populate hashes from retained artifacts. They may not copy expected hashes from configuration or construct success text themselves. This change defines the consumer contract only.

All digest spellings pass `hash256_hex_valid`. The ARM linker emulation is the
canonical `armelf_linux_eabi`. A collector may inspect structural validity, but
only the authorization function can promote a receipt; it additionally checks
the caller's expected receipt ID/nonce and verifies Ed25519 over internally
constructed canonical signing bytes.
