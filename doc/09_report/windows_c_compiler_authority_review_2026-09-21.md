# Windows C compiler authority review

STATUS: HOLD for complete admission. A scoped continuation fixes the four lint P1 findings and the shell/native contract passes, while exact-head review and self-hosted verification remain pending.

## Current change

Isolated branch fix/windows-msvc-toolchain-review-20260921 in D:/wk-msvc-review-astra was reconstructed from c0860cf's five semantic file changes onto origin/main e0dd873da1b7828389db4eb60e82972cc8245313. The subsequent user-selected policy adds LLVM23.1.1 Windows defaults, removal of Windows GNU/GCC selection, bootstrap-environment delegation, and the canonical deny lint rule. No shared-tree dirty files were staged.

## Passing focused evidence

All local artifacts below are under build/native_probe/msvc-review in the isolated worktree.

- shell-before.log: the current executable contract failed on actual c0860cf parent source because it selected clang.exe, retained CXX, and lacked version authority. This is a real prior-source failure; the earlier author's oracle-construction failure was rejected.
- shell-after.log: five executable selection cases pass, including the generic/target CC binding, inherited CXX clearing, missing authority, legacy major, wrong version, and failed version-query paths.
- bootstrap-env.log: exact LLVM23.1.1 clang-cl generic/target CC; CXX and LLVM_SYS_180_PREFIX absent; LLVM_VERSIONS=23.
- native-probe.log and paired-c-probe.json: identical C source compiled/linked/executed with LLVM23.1.1 clang and clang-cl, three samples each, with C++ explicitly rejected by preprocessing.
- cmake-configure.log and cmake-build.log: CMake selected Clang23.1.1 MSVC-style C and produced the expected executable. cmake-forbidden-cl-exe.log rejects explicit cl.exe before compilation.
- cargo-probe.log and cargo-build.log: the copied production MSVC Cargo target section compiled a tiny Rust executable with rustc -C linker=link.exe and produced the expected output. The final Cargo probe is distinct from an earlier PowerShell stderr-wrapper failure.

The paired C probe uses the same source, C11 language, O2 optimization, and DLL CRT selection. Mean compile/link elapsed times were 670.195 ms for clang and 674.889 ms for clang-cl. Observed compiler peak working sets were 16982016 and 16314368 bytes respectively, sampled every 5 ms. Linker children are outside that memory sample. These are local side-effect bounds; no performance improvement or full compiler benchmark is claimed.

## Repaired lint authority P1

The lint provider's source-authority test now recognizes the official LLVM 23.1.x Windows MSVC distribution independently of its install root, including the PR1216 workspace cache. It requires a root-bound driver, an executed version query, an exact 23.1.x predicate, and fail-closed rejection. A bare `--version` token or untrusted compiler alias remains denied. PR1216 itself is unchanged by this lane.

The first exact-head follow-up review found that exported target-specific CC/CXX names bypassed assignment classification and that a valid-looking predicate could inspect unrelated text. The candidate repair recognizes exported and batch target-specific names and traces the queried compiler's captured output through one derived assignment before accepting the exact family expression, either directly or through the PR1216 clang-cl pattern mapping. Focused fixtures retain both failures as regressions, including an unused exact metadata pattern beside a weak predicate over the real output.

The final permitted exact-head review found four P1 defects:

- Canonical target alias denied: shell query assignments record `_simple_win_version` while references tokenize as `$_simple_win_version`, and `CC_x86_64_pc_windows_msvc="$CC"` is not traced through the validated `CC="$_simple_win_cc"` assignment.
- Metadata or diagnostic-only predicate binding: the one-step symbol trace accepts derived diagnostic text containing the queried output as if it were the compiler output itself.
- Quoted target GITHUB_ENV export bypass: a quoted `CC_x86_64_pc_windows_msvc=...` export is not classified like the generic quoted `CC=...` form.
- Regex wildcard and missing-boundary acceptance: removing escapes before validation loses the distinction between a literal dot and wildcard, while `[0-9]` alone admits patterns without the required family token boundary.

A fresh scoped correction must retain the production shell as a positive, then add negative regressions for a diagnostic/metadata derivative, quoted target GITHUB_ENV forbidden export, wildcard family pattern, and missing family boundary. It must also retain forbidden target-specific CC/CXX and forged unrelated metadata coverage. The production implementation is frozen at the three-cycle cap; no P0/P1-clear claim is made.

The scoped continuation canonicalizes shell and PowerShell symbol references,
traces target `CC` through a directly validated `CC` assignment, restricts
derived evidence to actual output transformations, recognizes quoted target
exports, and preserves regex escapes while requiring both patch digits and the
family token boundary. Its executable spec adds each requested negative plus
canonical shell and real transformation positives. The focused native shell
contract reports PASS for all five cases. The attempted SSpec invocation found
that the available `bin/release` executable identifies itself as the Rust seed
and then failed to spawn its test child; this is not admission evidence and the
self-hosted test remains pending until Stage 2 exists.

The first exact-head continuation review reported P0=0/P1=3: escape removal
before validation rejected legitimate predicates, the transform heuristic
trusted fabricated array joins, and an added regex alternative could broaden a
mapped pattern. Review receipt:
`build/review/astra_llvm_authority_exact_head.md`, SHA-256
`4D989115F8DEC729F965E62B2AC546FA3DB14FC6BBBFA937762FE567E77E2CCE`.
The second focused correction preserves and normalizes escapes, supports the
canonical sed capture and CMake boundary forms, admits only pure join/sed
transformations, and rejects regex alternatives outside the permitted boundary.

The second exact-head review retained two P1 findings: a fabricated interpolated
prefix could satisfy the join heuristic, and a canonical regex in throw text
could validate a weak active predicate. The final permitted cycle parses the
complete join right hand side, checks only the active predicate operand, and
keeps CMake escape decoding separate from raw PowerShell regex semantics. Its
focused native shell contract again passes all five executable cases. A fourth
fix cycle is prohibited; this candidate is frozen for final exact-head review.

The final exact-source review of `6434d0fb0e2e204cf8075e57e735b3f95524abba`
reports P0=0/P1=2. A predicate over unrelated metadata is still accepted when
the queried output symbol appears only in the later throw message, and a
canonical quoted regex operand can still be concatenated with an LLVM 18
alternative. The source and executable fixtures are frozen under the three
cycle cap. Complete admission remains HOLD. Final review receipt:
`build/review/astra_llvm_authority_exact_head.md`, SHA-256
`AAEA49F5F07A053D8D247DD48A41FCE2C1224DCBC64C9F696BE795B6689EF60C`.

This follow-up is a fresh scoped continuation of the prior review and retains the three-cycle guard. An independent exact-head review is required before the draft PR can claim the P1 is clear.

## Pending executable verification

The original SSpec green used a Rust seed and was rejected. No admitted self-hosted runner is available. Both added SSpecs, generated-doc verification, and compiler/core/MCP gates remain pending. The manuals label these gaps explicitly.

The bootstrap currently uses Cranelift. Rust llvm-sys180 feature pins and hardcoded prefixes elsewhere in bootstrap-from-scratch remain a separate LLVM backend migration issue; this change does not silently alter those Rust features or count LLVM18 execution as Windows compiler authority.
