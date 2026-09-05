# `--no-verify` bypass evidence: lane stage3-memguard, 2026-08-19

Authorised explicitly by the user ("no verify push"). This file is the mandatory record.

## What was bypassed and why
The pre-push hook runs 63 guards. **35 of them execute the compiler** and every one fails
CLOSED in this worktree:

```
ERROR — nothing was checked: compiler not executable at 'bin/simple' (set SIMPLE_BIN to override)
FAIL: tail_pass expected GREEN, got exit 127
timeout: failed to run command 'bin/simple': No such file or directory
```

Cause: this lane worktree has **no deployed compiler** — `bin/simple` is a dangling symlink and
`bin/release/x86_64-unknown-linux-gnu/` does not exist. The blocks are an artefact of a missing
binary, not of anything in this change. A first push attempt on 2026-08-18 was rejected by all 35
(`HTTPS_EXIT=1`; confirmed nothing landed via `git ls-remote`, not via exit status).

Blocked guards (35, all same root cause): check-array-remove-returns-element,
check-class-identity-engine-matrix, check-class-identity-seed-matrix, check-engine-differential,
check-env-get-dead-fallback-guard, check-env-get-nil-abort-guard, check-for-loop-variable-scoping,
check-gpu-backend-layer-evidence, check-implicit-self-field-assignment,
check-jit-array-oob-nil-sentinel, check-lexer-radix-literal-suffix, check-lint-binary-staleness,
check-named-ctor-unknown-field-rejected, check-native-enum-match-payload,
check-native-extern-fabrication, check-native-inprocess-positional-nonvacuous,
check-native-object-cache-granularity, check-native-option-bool-eq-vs-literal,
check-native-option-eq-representation, check-native-trailing-default-param, check-native-utf8-slice,
check-no-jit-module-drop, check-no-sabotage-residue, check-predicate-parser-native-build,
check-pure-simple-pipe-lambda-parse, check-render-perf-milestone-gate,
check-spec-runner-tail-expression-verdict, check-spipe-docgen-regeneration-live,
check-sspec-evidence-regeneration, check-try-operator-error-propagation,
check-tuple-index-out-of-range, check-untyped-list-element-shift,
check-use-warning-oracle-deployed, check-utf8-slice-audit-live, check-wm-lane-boundary.

## Why the risk is bounded (stated, not assumed)
The pushed range changes **3 files, insert-only, 958 insertions, 0 deletions**: one 10-line
message-only branch in `scripts/bootstrap/bootstrap-from-scratch.sh` (classifying `exit >128` as a
signal death) plus two docs. No `.spl`, no runtime, no compiler source. None of the 35 blocked
probes tests a path this range touches. That is an argument for bounded risk — it is **not**
evidence the probes would pass, and it is not claimed as such.

## Guards that WERE run manually, on the exact pushed range
See the push report / commit for the verdict lines. All six mandatory range guards were run and
required to be green before pushing; the divergence FAIL is the pre-existing 854-entry backlog,
cleared through the documented scoped-delta escape (0 introduced by this range), recorded in
`test_tree_divergence_preexisting_stepover_2026-08-19.md`.

## Open, for whoever picks this lane up
This lane cannot satisfy its own pre-push hook until a compiler is deployed into it. Fix by
symlinking `bin/simple` at a deployed binary or by bootstrapping the lane — do not let
`--no-verify` become the routine path. This is the second such record in two days
(cf. `f0f5c5d1a70`), which is itself the signal worth acting on.
