# Native SSpec wrapper source review

Independent review against `b6e4922f1a318801a657c1e71ad5eb06666445f5`.
Worktree: `D:/dev/simple-smux-system-execution-20261025`.
Compilation, framework fixtures and structural specs: **NOT_RUN**.
Only the author's seven-file frozen manifest is in scope; concurrent compiler
transport/configuration changes are excluded and untouched.

## Findings closed in source

- **P2: native local imports lost scope.** Native mode now hoists only
  column-zero imports. Helper and sibling-closure imports retain their original
  scopes and aliases; legacy import behavior remains unchanged. A focused
  structural case checks both helper-local and conflicting sibling-local names.
- **P2: infix normalization split inside quoted matcher text.** The corrected
  native normalizer masks compiler-provided string byte ranges before locating
  the matcher, then slices the original operands. Quoted matcher phrases and
  UTF8 bytes remain data. Method-style assertions remain untouched.
- **P2: trailing comments swallowed the generated closing parenthesis.** The
  same canonical string mask distinguishes an unquoted comment marker from a
  quoted hash. The closing parenthesis now precedes the original comment
  suffix. The extended structural case covers plain comments and Unicode
  operands containing both a hash and matcher text.

No remaining concrete P0/P1/P2 was identified in the bounded corrected delta.
**Status: WARN / source review complete**, not runtime verification PASS.

## Reviewed invariants

The existing executor owns file reads/writes and computes compiler lexical
facts before passing text/arrays to the common helper. The added native-only
string ranges come from the actual `simple_string_byte_ranges` owner: per-line,
end-exclusive byte ranges including delimiters. That owner was inspected;
compressed character-column code text is not misused as raw UTF8 offsets.
The helper has no
imports, host access, compiler dependency or memory-family selection. Generated
framework imports remain generic `std.spec`; the physical executor directory
does not pin a configured family.

Explicit AOT and coverage AOT select complete-framework construction. Legacy
SMF defaults to the previous matcher rewrite, harness filtering and inline
helper path. Extracted partitioning retains the legacy branch rules; new struct
and public-declaration classification is native-only. Existing coverage markers
and generated-source cleanup remain owned by the executor.

The generated native main preserves actual describe/it/context/hook closures
and method matchers, then calls aliases of configured print_summary,
get_executed_test_count and get_exit_code. Zero executed examples returns2.
No rt_bdd assertion engine or replacement verdict/hook implementation is
synthesized. Alias selection is bounded and avoids prefixes present in source.

The real positive fixture checks before/after hook order across siblings, a
nested context, and an actual module-scope struct constructor/field assertion.
The negative fixture deliberately fails a real matcher, then
checks the failed case's after hook and later sibling bodies. Existing framework
source records matcher errors, runs after hooks, and continues to later cases;
the fixture neither relies on a crash nor converts failure into a passing
expectation. Neither fixture acquires native processes/files requiring teardown.

## Evidence boundary

Fifteen final structural cases are authored, not executed; they inspect
production-generated source and do not establish native case execution. The
separate real fixtures require positive3/pass3/exit0 and negative3/pass2/fail1/
exit1 through the actual admitted producer and production runner.

The existing execute owner remains over800 lines: author receipt reports a
reduction from1600 to1402. The initial274-line pure helper grew to318 lines with
the scoped review corrections.
This bounded extraction does not claim the old owner now satisfies a new
small-file limit. Scoped whitespace validation passed; no structural case was
executed and no generated source was compiled. Process cleanup receipts still
belong to future production-runner execution, not these source checks.

## Final frozen SHA256

| File | SHA256 |
|---|---|
| src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl | 1d05a5dfd9d5aaa65502c0742f9b9c6fe38386f2dcecac602c1235774b0206bf |
| src/lib/common/test_runner/native_framework_wrapper.spl | 5ff20e07f331c943930b652d31d8c745d86e1c3d410618b847721c1a9f77d3c6 |
| test/01_unit/lib/test_runner/native_framework_wrapper_spec.spl | fbf88682e040b9245537bad5fb0250a246ff5ff71cf6218f25b6133252b68443 |
| test/fixtures/test_runner/native_framework/hooks_and_siblings_spec.spl | 628793d87896faac6fd5ea79f534321d344726a72bd285ca874ed70653d1cd83 |
| test/fixtures/test_runner/native_framework/failure_continuation_spec.spl | 09709cdaefcbb400f7b581fcc8c5400d7862948a18358abe409585442707d6eb |
| doc/06_spec/01_unit/lib/test_runner/native_framework_wrapper_spec.md | 4b9342cb183f6b3c60acb27367ddaf861f2e6c4551d0bd59d5fba35b20b1db3c |
| doc/05_design/native_sspec_framework_wrapper.md | 60f05b4e6b9cbc61606826b735d89d3e38f8599164fc68f7ad0fc0d47ed0eac7 |
