# cmake_array_append_native_2026_10_16

Date: 2026-10-16. Database reconciliation pending: no qualified bug database updater is available. Status: source workaround prepared; native controls UNRUN.

The retained main Phase 3 attempt used producer `0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b` and source `c1f630e7a05d539852f53444231d4f90fd76d6a4`. Module `compiler.backend.cmake_gen` emitted 25 fatal diagnostic rows, starting with `unresolved method call: append`. These are diagnostics, not 25 failed modules. Remote base `67ba74d9acbaa998d5efcb3c162bf61a63f839d0` retains 25 `parts.append` sites and three untyped empty arrays in its three pure rendering functions.

The temporary source workaround uses explicit `[text]` storage and the supported native array `push` operation. All original arguments, strings, ordering, branches, joins and public function signatures remain unchanged. Each changed call carries an immediate workaround tag and the full intended-source recovery commit. Native array `.append` dispatch and element inference remain compiler bugs; this patch does not claim to fix them in the producer.

The shared actual-owner fixture calls all three real rendering functions with empty and nonempty inputs. Six complete-string controls cover ordering, child directories, literal CMake variables and trailing newlines, followed by input preservation checks. The native main and SSpec share that fixture. No copied renderer, substitute C object, lowered-provider context graft or hardcoded passing result qualifies the repair.

Native compilation, runtime controls, full compiler/library checks, MCP/LSP checks, whole Phase 3 linking and local deployment remain UNRUN. Maximum three repair/verification cycles apply to this feature. The first native command has not been prepared or launched. Recovery requires genuine producer dispatch support plus these output controls and actual module generation; fetching a remote fix alone does not authorize deleting the workaround.
