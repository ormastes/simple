# Mach-O duplicate-definition policy verification

STATUS: FAIL — full item4/Phase 4 and five-host execution remain incomplete.

Ordinary native-build and request-projection configurations enable duplicate
definitions. The strict-only Mach-O adapter rejected that value before linking.
This change must implement real deterministic first-selected strong-definition
selection and propagate it through archive resolution and final layout binding,
while preserving false/default strict duplicate failures.

Acceptance uses real competing object/archive inputs and independently inspected
output bytes, with strict rejection preserving a destination sentinel. Resolver
weak/common precedence is distinct from hosted weak-coalescing support, which
remains unimplemented. No assertion alone proves loader/native execution.

Compilation, executable SSpec, docgen, coverage, compiler/lib/MCP/native smoke,
performance and all-host execution remain UNRUN without an admitted deployed
self-hosted runtime. Structural/source evidence will be recorded separately.

Source `c735f04f24b` implements the policy in three existing modules. Initial
executable intent `2a14aaf5d45` preceded that implementation. Final independent
review of source and acceptance/manual/fixtures through `b31aedc9d97` found no
P0/P1. Six scenarios cover ordinary configuration propagation, direct strict
defaults, x64/ARM64 reversed winners, strict sentinel preservation, repeated
archive extraction, unneeded archives in both modes, and resolver precedence.
The earlier adapter negative matrix and current guide/design were updated to
reflect the now-supported policy rather than retaining obsolete rejection tests.

Fixture assembly used LLVM 21.1.8; exact commands and archive member order are
recorded in `test/fixtures/linker/macho/RECIPE.md`. This is external fixture
generation evidence only. Common-layout checks exercise maximum size/alignment
on naturally aligned fixtures; they do not prove every misaligned combination.
Hosted weak coalescing, SDK providers, managed admission and actual host execution
remain open, and no full coverage or runtime PASS is claimed.

Integration rebased onto `01cde54601b8df6794029e618c6f973474f4fa1c`; all ten
reviewed patches compare equal. Final whitespace, direct-env working/staged,
numbered-artifact and manual-layout checks passed. Committed test-tree delta:
3151 inherited offenders, zero introduced. Retained list:
`C:/dev/simple/.git/item4-macho-duplicates-preexisting-offenders.txt`.
These structural results do not change the full verification FAIL/UNRUN status.
