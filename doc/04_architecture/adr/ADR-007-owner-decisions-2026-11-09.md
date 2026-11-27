# ADR-007: Owner decisions of 2026-11-06 to 2026-11-09 (release/1.0.0)

- **Status:** accepted (owner decisions; implementation tracked per bug)
- **Rule:** treat these as settled; do not re-ask. Each governed bug carries a dated note row in `bug_db.sdn`.

## Language semantics
| Decision | Bugs governed |
|---|---|
| `if val` on a non-optional Result is a compile error | if_val_result_binds_whole_result_2026_11_07 |
| `{x}` interpolates; `{{` and `}}` are literal braces (seed and self-hosted parity) | interp_brace_literal_collides_with_string_interpolation_2026-07-03 |
| Implement the `s{...}` set literal in both parsers | set_literal_s_brace_unparsed_2026-09-06 |
| Implement `| Pat -> expr` match arms | readme_arrow_match_arm_syntax_does_not_parse_2026-09-19 |
| Seed treats `.? == true/false` None-safe, matching pure Simple | seed_optional_query_comparison_divergence_2026-08-16 |
| No `rt_enum_discriminant` exception; route via the owner module | value_access_ownership_spec_never_executes_2026-09-18 |
| Ambiguous co-compiled duplicates are a compile error (qualify), then rename real clashes | jit_co_compiled_definition_ambiguity_debt_2026-09-15 |

## Bootstrap and build policy
| Decision | Bugs governed |
|---|---|
| arm64 attested lane requires stage3 and never admits a Rust seed | arm64_attested_build_rejects_rust_seed_by_design_2026-09-01 |
| Build the macOS openat/fexecve-equivalent helper now | bootstrap_macos_blocked_seed_compile_and_linux_only_stage3_authority_2026-09-06 |
| Windows publish tries a native symlink, then a junction or copy pointer, with a clear log line | bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07 |
| AOT-producing gates fail closed when the seed build commit is older than the source | checked_in_seed_stale_vs_release_miscompiles_aot_2026-11-06 |
| Stage2 source-quiescence snapshot scoped to build-input paths; build from a pinned git-archive snapshot; first stage2 admission stays strict trust-root | stage2_admission_source_quiescence_unsatisfiable_in_shared_tree_2026-08-31, windows_phase3_blocked_planner_admission_producer_requires_in_repo_build_root_2026-09-02 |
| Shared cargo target for the x86 bootstrap tuples | x86_bootstrap_rust_authority_tuple_recompilation_cost_2026-08-22 |
| Census reads PE exports | windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02 |
| SFFI baseline: re-census on Linux CI, accept the measured value with a note | sffi_authority_baseline_stale_after_gpu_bootstrap_2026-08-24 |
| Defer diagnostic multi-file sweep and flat AST bridge throughput to post-1.0 | bootstrap_diagnostic_multifile_check_startup_blocker_2026-08-02, flat_ast_bridge_phase3_snapshot_throughput_2026-08-31 |
| VAR_ROOTS_CACHE fix is in source; awaits seed redeploy | deployed_seed_binary_missing_var_roots_cache_fix_2026-09-13 |

## Test policy
| Decision | Bugs governed |
|---|---|
| `test/01_unit` and `test/02_integration` are canonical; migrate unique specs, delete the old trees | test_tree_divergence_preexisting_red_stepover_2026-08-17 |
| Perf font spec uses `Engine2D.load_font_bytes` | perf_specs_blocked_no_self_hosted_binary_and_unregistered_font_fixture_2026-08-18 |
| Close the llm caret collision after a fresh-seed run | parse_claude_json_response_name_collision_2026-07-20 |

## Tracker closures
| Decision | Bugs governed |
|---|---|
| Close and split the CI multiplatform umbrella | ci_rust_bootstrap_multiplatform_all_lanes_red_2026-08-31 |
| Close the phase1 693-failure umbrella as a tracker | phase1_lib_scope_residual_failures_2026-11-05 |
| Close the superseded JIT coverage census | seed_jit_coverage_self_hosted_compiler_2026-08-21 |
| Close partial driver overhead; file the residue | native_build_per_file_driver_overhead_2026-08-21 |
| Keep step 5 open with a prerequisite bug | native_build_step5_serial_threads_ignored_2026-09-04 |
| Close per-call env rebuild as improved | seed_per_call_env_rebuild_o_globals_regression_2026-08-21 |
| Close the stage3 admission bug; runbook moved to the bootstrap guide | stage3_hard_blocked_on_stage2_admission_2026-08-31 |
| Delete the six orphan part files | orphaned_part_files_never_imported_2026-09-18 |

Earlier decisions (2026-11-06 items 1-6; 2026-11-08 items 7-8; 2026-11-09 items 9-12) concern return-type inference, TypeId, SMF header, private-name access, module initializers, `a.get(i)`, Windows publish and doctests, and are not repeated here. ADR-005 and ADR-006 remain authoritative.
