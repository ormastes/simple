# Mach-O provider closure verification

STATUS: FAIL — full item4/Phase 4, SDK and five-host qualification remain open.

This lane implements an explicit provider graph, direct-client checks and native
SDK dependency resolution. It must preserve direct library ordering and outward
alias names, avoid unrestricted export flattening, and retain binary validation.
Inline identity resolution precedes file lookup. Missing, ambiguous or malformed
selected providers must fail before publication without alternative-provider
fallback. Cyclic graphs require bounded lookup rather than arbitrary rejection.

Initial SDK-chain specification 865f0a73251 preceded native wiring. Further
graph/alias/access regressions accompany implementation and review. The deployed
runtime directories remain absent in both shared and integration worktrees at
this turn's check. Simple compilation, SSpec/docgen, coverage, core/lib/MCP,
native and performance tests are UNRUN. No Rust seed substitute is used.

The native loader searches explicit library paths before the configured SDK
root. Dependency candidates prefer a text interface over its corresponding
binary; direct named-library ordering remains unchanged. Requester-relative
and output-relative tokens use their actual paths. No host /usr/lib fallback
or signing-identifier substitution is permitted. Owner-specific @rpath lookup
remains an explicit unsupported gate; it is not silently replaced with the
executable's runtime paths.

Graph limits and pre/post file-size checks are logical bounds. Resident file
reads are not a race-free bounded-I/O or whole-job memory certificate. Managed
admission, weak coalescing, remaining SDK semantics and all actual host execution
remain separate open requirements.
