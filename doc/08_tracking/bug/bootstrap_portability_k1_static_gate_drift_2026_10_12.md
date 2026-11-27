# Bootstrap portability K1 gate drift

Status: OPEN (focused K1 gate repair qualified; full portability audit pending).

Linux LLVM run38161125487 on020e419f5 passed source snapshot and argument contracts, then rejected canonical K1 authority because its static grep expected the retired `selected_k1_policy=$(kernel_policy_value k1_policy)` assignment. Production now selects between canonical and explicit manifest-pinned alternate composition.

The gate now executes a source-derived isolated policy block. Fixtures verify unset/default canonical, explicit canonical, explicit alternate, unadmitted environment rejection, missing and duplicate both manifest keys, and missing manifest. The policy block ends before bootstrap wrappers; no compiler/bootstrap process is started.

Validation: focused behavioral test PASS on first cycle. Already-green prior portability behaviors were not rerun. The remaining gate was inventoried independently; prefix review identifies thirteen spelling/representation drifts, one incomplete fixture closure, and twenty-four unresolved contract findings. No guard was broadly disabled and full gate PASS is not claimed.

Evidence: /mnt/c/Temp/simple-bootstrap-k1-contract-fix-20261012/audit-prefix-reviewed.tsv and audit-collector.log. Broader gate findings require owner/requirements review before production admission.

## Linux x86_64 Verification (2026-11-26, Lane 1)

- `sh test/01_unit/scripts/bootstrap_k1_policy_selection_test.shs`: **PASS**
  (`PASS: source-derived K1 selection, alternate, drift, missing/duplicate keys, and missing manifest`).
- `sh scripts/check/check-bootstrap-portability.shs </dev/null` on Linux x86_64:
  passed the K1 policy selection block (line 123) and all earlier contracts
  (`portable_process_lock_test`, `bootstrap_prune_lru_dirs_test`,
  `bootstrap_from_scratch_rust_authority_contract_test`,
  `bootstrap_from_scratch_jobs_space_form_test`,
  `bootstrap_from_scratch_arg_contract_test`, `bootstrap_stage3_config_knobs_test`,
  `bootstrap_stage3_source_snapshot_test`, `bootstrap_stage3_jj_state_test`,
  `linux_phase23_llvm23_*`, `bootstrap_current_owner_contract_test`,
  `bootstrap_startup_jobs_memory_policy_test`, `check-dedicated-host-startup-wiring.shs`),
  then stopped later at line 246 (`FAIL: Rust authority fingerprint does not bind the selected platform`
  because `scripts/bootstrap/bootstrap-from-scratch.sh:3753` passes `"${seed_fingerprint_search_path}"`
  instead of `"${PATH}"` — one of the 6 unrelated representation drifts already
  inventoried for owner review).
- Status kept `fix-implemented-verification-pending` until the remaining
  unrelated drifts in `check-bootstrap-portability.shs` are resolved.
