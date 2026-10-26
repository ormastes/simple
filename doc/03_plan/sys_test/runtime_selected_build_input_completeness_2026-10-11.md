# Runtime selected-build-input completeness regression plan

Bug: captured_rust_api_runtime_c_inputs_missing_2026-10-11.
Status: six actual selected-input helper behaviors observed PASS; full production/capture/process-closure acceptance remains incomplete.

The production target/feature selection determines required inputs. Existence
must validate that selection, not silently remove missing selected members.
Do not introduce a second hand-maintained source list for the guard. Capture
immutability and capture completeness are separate admission requirements.

1. Complete selected closure: invoke the actual production selection/check owner
   on a temporary real filesystem containing every selected source; all selected
   identities reach compilation unchanged. Confirm native source ordering and
   existing target/feature selection are preserved.
2. One selected source missing: actual checker rejects its exact source path
   with a stable missing-input diagnostic before archive publication. An archive
   produced from the remaining members must not count as success.
3. All selected sources missing: fail with the same structured admission error;
   no empty archive is created and no generic hard-link error hides the cause.
4. Missing unselected platform/feature input: target/feature selection remains
   authoritative; a file absent from the selected set must not become required
   merely because another platform uses it.
5. Directory or invalid required input: existence of a directory at a selected
   source path does not establish a readable source file. Define and check the
   actual supported regular-file/immutable-capture policy at its owning boundary.
6. Computed input capture: preflight catches the demonstrated Windows 27-source
   omission before expensive Cargo compilation. Include recursive local headers
   and generated inputs, with conditional/system inputs explicitly qualified.
7. Pure-Simple counterpart: audit its real bundle/bootstrap selection/check path;
   run equivalent criteria where it has the same skip behavior. If no matching
   defect exists, record actual owner evidence rather than invent a patch.

Use actual owner functions and temporary source files, not constants-only tests
or declaration-name oracles. Store source/tool fingerprints, terminal results,
peak RSS and measured startup cost with executed evidence. Do not add runtime
source scans/hashing to unrelated hot compiler paths. No perf or memory PASS is
claimed by this plan. Existing failed snapshots and the exhausted Rust API
execution cohort remain untouched; this plan does not authorize a fourth retry.

Merge owner: root. Private implementation/review lane: astra_exact_input_cache_review.
Final reviewer: root; broader pure-owner interfaces additionally reviewed by Astra.
## Executed helper evidence and remaining scope

Standalone actual helper source95aa4a...b86b compiled with installed Rust/MSVC.
All six test names in request3e8903a...d290 appear in authenticated final log
b90ae2cb...1f2, with6passed/0failed/0ignored/0filtered in0.03seconds.
This covers exact ordered paths, partial/all/one missing input, directory
rejection, and absent unselected optional input at the helper boundary.
Do not rerun these passing behaviors unchanged.

It does not execute production build.rs selection, cc/archive orchestration,
recursive header/generated capture, Pure-Simple equivalence or Phase3 admission.
The controller failed whole-request admission because its120second process
closure deadline expired; native stages were0, cleanup ended with Job active0,
no input drift. Result9d9281ed...daf4 preserves this qualification failure.
Criteria1-7 retain these broader outstanding gates; helper success does not
upgrade their entire scope to PASS. No0.1second compiler target is established.