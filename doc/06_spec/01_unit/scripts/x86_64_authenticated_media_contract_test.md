# x86_64 Authenticated Media Wiring Contract

Source: `test/01_unit/scripts/x86_64_authenticated_media_contract_test.shs`

Evidence class: `source-contract`.

## Checks

- The fixture execute-opens the path supplied by its canonical caller,
  authenticates it with the immutable trust pin, and binds the live file
  generation.
- Only the complete `/FSEXEC.ELF` + `AUTHHEL.*` and `/SERVERS.ELF` +
  `SERVER.*` platform-owned tuples are accepted. Arbitrary executable paths
  and cross-image sidecar substitution fail closed before opening a file.
- The scheduler consumes the authenticated result while the public path-only
  facade remains denied.
- The boot entry calls the authenticated media owner, and the builder retains
  a real LLVM hello payload without mutating the signed executable for nonce
  injection.
- The integration roundtrip oracle is wired while arbitrary executable paths
  remain denied.

This shell test performs static source-wiring checks only. It does not build an
ELF, create media, boot QEMU, authenticate bytes at runtime, or prove that the
hello payload executed. Those claims require the production build and live
guest acceptance gates.
