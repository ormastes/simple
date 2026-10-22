# cmake_array_append_native_2026_10_16

Date: 2026-10-16. Database reconciliation pending: no qualified bug database updater is available. Status: source workaround prepared; native controls UNRUN.

The retained main Phase 3 attempt used producer `0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b` and source `c1f630e7a05d539852f53444231d4f90fd76d6a4`. Module `compiler.backend.cmake_gen` emitted 25 fatal diagnostic rows, starting with `unresolved method call: append`. These are diagnostics, not 25 failed modules. Remote base `67ba74d9acbaa998d5efcb3c162bf61a63f839d0` retains 25 `parts.append` sites and three untyped empty arrays in its three pure rendering functions.

The temporary source workaround uses explicit `[text]` storage and the supported native array `push` operation. All original arguments, strings, ordering, branches, joins and public function signatures remain unchanged. Each changed call carries an immediate workaround tag and the full intended-source recovery commit. Native array `.append` dispatch and element inference remain compiler bugs; this patch does not claim to fix them in the producer.

The shared actual-owner fixture calls all three real rendering functions with empty and nonempty inputs. Six complete-string controls cover ordering, child directories, literal CMake variables and trailing newlines, followed by input preservation checks. The native main and SSpec share that fixture. No copied renderer, substitute C object, lowered-provider context graft or hardcoded passing result qualifies the repair.

Native compilation, runtime controls, full compiler/library checks, MCP/LSP checks, whole Phase 3 linking and local deployment remain UNRUN. Maximum three repair/verification cycles apply to this feature. The first native command has not been prepared or launched. Recovery requires genuine producer dispatch support plus these output controls and actual module generation; fetching a remote fix alone does not authorize deleting the workaround.

## First native qualification

Applied workaround commit: [4442f60ded3fed388dcf09a4295150adf75ba87d](https://github.com/ormastes/simple/commit/4442f60ded3fed388dcf09a4295150adf75ba87d), draft PR3571. The paragraph above describes the initial source-only state and is superseded here for native compilation and the six renderer controls only.

The actual first build completed with seven genuine SPL COFF objects; the parse-stage selection of 986 modules is not an emitted-object count. The canonical candidate used `/FORCE:MULTIPLE` and was never executed. A strict link used the same seven unchanged SPL objects, a canonical entry shim with no actual module initializers, and 38 genuine D9 runtime C objects whose source bytes and complete 391-header closure match this checkout. Original donor paths, compiler flags, hashes and capsule receipts are retained; no smaller-context SPL object was grafted into the compiler.

Strict candidate SHA256 `2B7724792E25CDA9C1B8C4C2113D4E20423F76B696BB52F243C15252037194A4` linked without diagnostics or suppression flags. It executed once: exit0, exact `PASS cmake-native-parts 6 output controls and input preservation`, empty stderr, unchanged pre/post hash. The 58.07ms observation is not a benchmark. All three real renderer functions and the actual fixture/main are rooted in the retained link map.

The SSpec now explicitly imports the canonical `std.spec` prelude, matching neighboring backend specs. This affects only the unrun BDD path; the qualified native entry, shared fixture and production file are unchanged. BDD, broad compiler/library/MCP/LSP gates, the filesystem-writing generator path, whole Phase 3 and deployment remain UNRUN. Native PASS does not constitute release verification or permission to remove the workaround. Cache, scripts, preflight receipts, strict map, one-shot invocation ledger and stdout/stderr are retained under `phase3-validation-20261016/cmake-native-parts-native-cycle1`.
