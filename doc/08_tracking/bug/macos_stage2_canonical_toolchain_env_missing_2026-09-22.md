# macOS Stage 2 omits canonical pinned toolchain assignments

Status: source fixed; focused regression passes; full bootstrap verification pending.

On source `bd544ccef9e843b3f1b77296cbf29215d84a2057`, the enforced macOS
Cranelift bootstrap completed Rust authority builds and then refused Stage 2
before starting its compiler. The actual child environment omitted `CC`,
`CXX`, `AR`, `LD`, `LLVM_CONFIG`, and `SIMPLE_LLVM_REQUIRED_VERSION`, while
`bootstrap_stage3_stage2_canonical_env_names` required all six. Failure evidence:
`build/evidence/macos-enforced-bd544/stage2/console.log` in the isolated
`macos-bootstrap-restart-20260922` checkout.

The wrapper now forwards those six values on Darwin and includes them in both
the Stage 2 admission digest and Stage 3 transcript replay. Linux and Windows
vectors are unchanged. This adds six constant-size argv entries only; it does
not alter compiler passes, allocations, parallelism, or cache behavior.

Reproduction and regression:
`sh scripts/check/check-stage2-macos-toolchain-env.shs` extracts and executes
the production argument builder without compiling. Four Darwin/Linux by
Cranelift/LLVM cases check exact tool values (including spaces), execution
versus admission hash equality, and Stage 3 replay equality. The test fails
against the parent bootstrap script with all six missing names and passes
against the fixed script. `BOOTSTRAP_ENV_FIXTURE_SOURCE` selects a retained
parent script for the negative reproduction.

The failed live run lasted 789.03 seconds; its outer watchdog recorded
5,479,200 KiB peak versus the enforced 5,859,375 KiB limit, quiescent exit 1,
and no escaped sessions. This proves sampled process-tree enforcement, not a
kernel aggregate hard limit (`hard_memory_limit=0`). No Stage 2 artifact was
admitted by that run.
