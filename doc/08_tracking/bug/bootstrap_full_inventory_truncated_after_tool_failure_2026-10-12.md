# Full inventory truncation after failed tool build

GitHub: [#3302](https://github.com/ormastes/simple/issues/3302), OPEN.

Full keep-going bootstrap verification silently bounds the module diagnostic inventory to eight entries whenever the full CLI or test runner fails to build.

Actual source: release_phase3 063e67384861fddfa4c84ad4b357c300916dd6fc. Canonical Stage2 terminal observation at /tmp/bootstrap-live-observer-063e-20261012/terminal-observation.json records 14,133 inventory modules, eight attempted (seven PASS, one FAIL), and 14,125 remaining. Overall remains FAIL; this is incomplete diagnostic coverage, not a false admission PASS.

Root cause: bootstrap-phase-verification.shs defaults BOOTSTRAP_VERIFY_FAILED_TOOL_MODULE_LIMIT to 8 and passes it to bootstrap_verification_select_modules without considering --strategy=full, --profile=full or keep-going. The existing selector already interprets 0 as all pending modules. Retained exact-lineage seals and all source/runtime authority checks must remain mandatory.

Proposed repair: resolve the effective limit to 0 for keep-going full-strategy or full-profile runs; explicit fail-fast and opt-in slim checkpoints retain configured bounds. Keep global campaign deadline, per-row limits, cancellation, immutable source/runtime admission and failed aggregate verdict unchanged. Deadline expiry may still leave honestly reported unfinished scope; all inventory selection does not imply all execution.

Changed-input synthetic regression passed once: full failed-tool selection includes all 14,133 entries; exact synthetic seals for seven PASS and one FAIL resume all 14,125 pending with retained-failure exit 3; the actual production scheduler runs all twelve fake queue commands after an initial failure while invalid authority/fail-fast run none. This is harness evidence only, not compiler/object/bootstrap qualification. Independent source review pending; bug remains OPEN.
