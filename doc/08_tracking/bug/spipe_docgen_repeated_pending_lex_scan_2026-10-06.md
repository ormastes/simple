# SPipe docgen repeats whole-source lexing for every scenario

Status: source repaired; Phase1 doc-generation and focused ownership evidence available, pure-runtime qualification pending.

Trigger: generate the manual for the 509-line, 20-case backend_software_kernel_table_bucket_spec.spl. Preserved collector run reaches validation OK then times out after 90 seconds with no manual. Its seed JIT falls back to interpretation on unresolved cli_current_exe_path; that engine limitation remains separately visible.

Cause: generator count_test_items/extract_scenario_list calls scenario_at_is_unconditional_pending for each scenario. The helper rejoins and re-lexes the entire source on every call. Batch callers now compute canonical string-continuation facts once per pass and share them. The public two-argument helper remains available and validates invalid indexes before lexing.

Focused regression also exposed an existing correctness defect: the pending helper's independent triple-quote toggle reads a fixture closing delimiter as a docstring opener and misses a following unconditional placeholder. It now uses canonical continuation facts, preserving real placeholders after multiline fixtures.

Validation: no GPU assertions rerun. Original two focused ownership cases produce 1 PASS/1 FAIL; only the failed case is rerun after repair, producing 1 PASS. Full manual generation with the repaired counting owner exits 0 and reports one complete manual, zero stubs, twenty active cases. Final repository-relative/manual-path receipt is retained separately. This is bootstrap seed evidence, not Phase2 PASS.
