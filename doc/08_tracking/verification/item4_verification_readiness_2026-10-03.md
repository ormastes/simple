# Item 4 verification readiness review

**STATUS: FAIL — Phase 4 is not ready.**

Integration base: `94a16103a5baeefad8bc7688e70b43b75dcf2914`.
Source integration through `d2c7ef15a12`; subsequent report/manual edits do not
constitute execution evidence. The change adds 42 executable scenario declarations
and extends existing storage/reader/SCV scenarios. None have run in Simple.

## Source review

- Root and independent inherited-model agents reviewed the native pack transport,
  canonical loader ownership, generation pin/unload transitions, policy binding,
  and native command entry. Budget refusal now precedes provider side effects;
  policy SHA-256 covers the actual values. Provider-owned host ABI rejection and
  native prerequisite failure guards were added after review.
- Research independently reviewed hosted Mach-O eager binding, rebases, stubs,
  imported TLV and signature construction; requested bounds assertions and
  fail-closed section admission corrections were incorporated.
- Root reviewed RV64 local-exec TLS integration and the shared ELF STT_TLS offset
  correction. Real x64/AArch64 fixtures exercise local/hidden/global symbols.
  Independent research review covered attribute decoding, merging, metadata
  emission and TLS integration; its missing `char_from_code` import finding was
  corrected before landing. No additional P0/P1 was found in the reviewed subset.
- Root identified free-function value-owner loss in the streamed candidate.
  Research and runtime migrated retained/stream/spill/SCV consumers together;
  acceptance independently traced cursor/quota/close state through success and
  error paths. Failed unload/publication cleanup retains ownership.

The initial owner-loss finding is repaired in source, not proven at runtime.
The separate pre-existing streaming SHA defect is recorded at
`doc/08_tracking/bug/sha256_stream_value_owner_state_2026-10-03.md`; SCV hashing
is not accepted by this review. One-shot SHA used by the new pack/signature paths
is not the affected streaming API.

## Evidence and gaps

| Criterion | Result |
|---|---|
| Changed-source whitespace; working/staged environment guard | PASS, source checks only |
| Removed retained read/write/close free API references | Zero remaining references in owned src/test `.spl` |
| Executable `_spec.spl` under doc/06_spec | Zero |
| LLVM fixture generation/LLD comparisons and .NET SHA oracle | Independent byte-oracle setup only, not Simple execution |
| SSpec RED/GREEN, canonical zero-stub manuals, coverage | UNRUN |
| Compiler/lib/MCP checks and runtime/native smoke | UNRUN |
| Native provider linking, Darwin/FreeBSD/RISC-V execution | UNRUN |
| Whole-job RSS/no-swap, parity, product corpus, latency | UNRUN; implementation gaps remain |

Read-only reinspection still found no deployed release runtime; the known native
candidate reports `admission=UNADMITTED` despite child exit 0. The prior three
diagnostic attempts were not repeated and no Rust seed fallback was used.

See `doc/03_plan/compiler/linker/item4_verification_readiness.md` for the eight
work items and remaining positive behaviors. Named unsupported errors do not
complete those requirements. This source review does not authorize a release tag,
publication, a whole-item done mark or Phase 4 PASS.
