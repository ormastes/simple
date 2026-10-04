# ELF byte-source verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

Scope: a selected file-reader operation actually supplies bytes to freestanding
and hosted ELF linking, using the same sealed owner for subsequent image
operations. Pure array-input entrypoints retain their three-facet contract.
File adapters require the additional byte-source facet before any input I/O.

Hosted library probing previously classified a pathname through an independent
read and later loaded it again. Source-aware selection must retain the returned
bytes and classify/link that same data. This is a per-link byte snapshot, not
proof against mutation during the read, filesystem alias substitution or
untrusted callback behavior. Native image publication remains the existing
staging/rename path after successful input acquisition and linking.

The portable default uses the existing Result-returning file facade. The current
retained-handle helper is not a universal substitute: it lacks FreeBSD/macOS
support and rejects symlinks used by hosted libraries. No before/after pathname
hash or self-reported digest is treated as immutable identity or authentication.

Acceptance must use real files and independently inspect linked output to prove
selected source dispatch; error paths preserve a pre-existing destination.
Hosted acceptance requires real host CRT/DSO prerequisites and must not label a
freestanding result as hosted execution. Source-only test ordering is not an
observed RED/GREEN run.

Native Simple compilation/tests, canonical docgen, coverage, core/lib/MCP checks,
native smoke and NFR measurements remain UNRUN. No capped runtime build retry is
authorized by this source continuation; full readiness remains unproven.

Initial source integration: the freestanding adapter selects file operations for
ELF and preserves the legacy Mach-O path. Hosted ELF reads CRT, objects, runtime
archives and shared libraries through a mutable per-link lexical-path cache.
The same owner reaches the production ELF engine. Independent review of both
implementations found no P0/P1. The cache retains raw arrays alongside widened
ELF inputs during linking; avoiding repeat reads costs resident memory and is
not a bounded-working-set implementation.

Nine executable scenarios now cover one source/writer owner, missing source,
invalid inputs, alias precedence, real hosted archive snapshot reuse, canonical
parity, selected-source errors, seal admission mismatches and provider-order
binding receipts tied to real output bytes. The manual is authored and explicitly
UNRUN; it is not canonical docgen output. Test fixtures were independently
assembled and inspected. Independent source review of the final scenarios and
explicit required-facet field writeback found no P0/P1 findings.

Working/staged direct-env guards passed. The generated-manual tree contains zero
executable `_spec.spl` files. These structural checks do not establish behavioral
correctness. Selected CRT/DSO wire oracles, freestanding archive dispatch and
concurrent execution of fixed-path scenarios remain additional test gaps.

Final structural evidence: whitespace and numbered-artifact guard passed. The
eight patches rebased unchanged onto release base
`c74098886a9f5d59cb3f9b97b48abbe9e912b008` (range-diff all equal).
Test-tree delta PASS: 3151 inherited offenders, zero introduced. The exact
offender list is retained at
`C:/dev/simple/.git/item4-elf-byte-source-preexisting-offenders.txt`, SHA256
`52ac058b29cffa22e435ff81da0cfb5de6db910b102fa51759866e24fd1d4678`.
This matches the preceding ELF-operation wave's recorded list. The underlying
repository-wide divergence guard remains FAIL; the scoped delta is PASS.
PR: https://github.com/ormastes/simple/pull/2434 (source/test slice only).
