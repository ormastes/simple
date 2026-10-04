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

Core implementation 9876f149efa adds typed sources/search/client/limits, an
explicit graph and actual hosted lookup. Legacy byte/typed hosted entrypoints
retain their prior policy refusals; the new closure entry checks reachable
deployment versions and supplies direct roots only to image construction.
Native wiring and deterministic filesystem lookup are owned by this integration.
Actual output spelling is preserved for permission rules, with Windows separator
adaptation separate from filesystem normalization.

Independent exact-source review found no remaining P0/P1 after alias-cycle
continuation and accounting/performance fixes. Per-node export indexes and alias
ordinal sets avoid repeated export scans; validated metadata is cached with
explicit writeback. One mutable lookup owner retains cumulative work across all
imports. Parsed symbol counts include unselected interfaces; expanded symbols
are separately bounded. These are reviewed algorithms, not measured performance.

The mixed alias-cycle regression was added during review; only initial SDK-chain
intent is claimed to precede implementation. A real binary alias fixture was
created by documented export-trie mutation after ld64.lld reported aliasing to
imported symbols unsupported. Independent decoding is distinct from code-signing
or loader acceptance, and no fabricated text-provider VM addresses are used.

Final independent source review binds core 9876f149efa, tests through
c4b6d473ada (twelve scenarios), native lookup through 6fc4b83f77a and design
through 1d6798e9c88: no remaining P0/P1 findings. Coverage includes real
inline/external graphs on both formats/CPUs, alias and mixed-cycle behavior,
direct versus indirect permissions, deployment/budget/identity refusals,
actual relative-path file reads and preserved destinations. The final Windows
expected-path correction normalizes separators independently of production code.

Integration rebased onto 8287f9bc3a6b10fda5b8da505508ca459f6c11ce with all
15 existing patches unchanged; intervening release work had no owned-path
overlap. Final scope whitespace, direct-env working/staged and numbered-artifact
checks passed. The tracked manual tree has zero executable specs; this lane
adds only its Markdown manual there. These checks do not change runtime UNRUN.

Committed test-tree delta passed with 3152 inherited offenders and zero
introduced. Retained evidence:
`C:/dev/simple/.git/item4-macho-sdk-closure-preexisting-offenders.txt`, SHA256
`2fb68a47bab7953e058a449562ecba2df9f135b8d2e2d99c3e14f373b1c1d719`.
The subsequent b034535823f deployment variant adds a `.tbd` fixture and assertions
inside the same executable spec, changing no executable paths or mirror
membership. Its own whitespace/new-artifact guard and independent source review
passed. It specifically checks a reachable macOS 12 leaf under a macOS 11 request,
the minimum-OS diagnostic and unchanged destination for both root formats.
Twelve scenarios remain authored; full verification remains FAIL/UNRUN.
