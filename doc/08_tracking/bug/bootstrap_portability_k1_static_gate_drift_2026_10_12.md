# Bootstrap portability K1 gate drift

Status: OPEN (focused K1 gate repair qualified; full portability audit pending).

Linux LLVM run38161125487 on020e419f5 passed source snapshot and argument contracts, then rejected canonical K1 authority because its static grep expected the retired `selected_k1_policy=$(kernel_policy_value k1_policy)` assignment. Production now selects between canonical and explicit manifest-pinned alternate composition.

The gate now executes a source-derived isolated policy block. Fixtures verify unset/default canonical, explicit canonical, explicit alternate, unadmitted environment rejection, missing and duplicate both manifest keys, and missing manifest. The policy block ends before bootstrap wrappers; no compiler/bootstrap process is started.

Validation: focused behavioral test PASS on first cycle. Already-green prior portability behaviors were not rerun. The remaining gate was inventoried independently; prefix review identifies thirteen spelling/representation drifts, one incomplete fixture closure, and twenty-four unresolved contract findings. No guard was broadly disabled and full gate PASS is not claimed.

Evidence: /mnt/c/Temp/simple-bootstrap-k1-contract-fix-20261012/audit-prefix-reviewed.tsv and audit-collector.log. Broader gate findings require owner/requirements review before production admission.
