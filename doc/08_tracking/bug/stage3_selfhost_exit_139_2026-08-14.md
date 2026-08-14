# Stage 3 self-host exits 139 after fresh Stage 2

Date: 2026-08-14
Status: OPEN
Owner: compiler bootstrap
Source authority: `f26936914d9833a000044757f6475bc7fd6e62cb`
Internal final reviewer: `/root/higher_model_review` (`gpt-5.6-sol`, 2026-08-14)

## Failure

The third and final bounded bootstrap cycle built Stage 2 and passed its sanity
gate. The fresh pure-Simple Stage 2 compiler then segfaulted while compiling
Stage 3. `stage3-native-build` was observed exiting 139 before writing
diagnostic output. The driver console containing that exit was not retained;
the progress log ends at an alive Stage-3 sample. Therefore exit 139 is an
unretained observation pending the next diagnostic reproduction, not a
hash-bound receipt.

Command:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --full-cli \
  --no-mcp --diagnostics=test \
  --diagnostic-child-compiler=/mnt/data/worktrees/restart12-infra/build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple \
  --output=build/restart12-bootstrap --jobs=full \
  --progress=build/restart12-bootstrap/progress-resume.log
```

Retained inputs/evidence:

- Stage 2: `build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
- Stage 2 SHA-256: `7617c924d6848928f3f7495e3d6691d908505fb677d19b9f07f9697ebf9aaec5`
- Progress log: `build/restart12-bootstrap/progress-cycle3.log`
- Progress SHA-256: `d59a1256be2afbe50476919803aca20993ca58e45e7e7a98ee3edd1e07707322`
- Empty child log: `build/restart12-bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`

## Unblock condition

In a fresh session, run the exact command above while retaining driver
stdout/stderr and exit status, obtain a symbolized
owner-path backtrace or the smallest pure-Simple reproducer, fix the
compiler/codegen owner, and complete Stage 3 plus Stage 4 and the bounded
essential-tools smoke gate. Do not use the Rust seed, stale release binary, or
Stage 2 as SPipe/release evidence. The prior session exhausted its three-cycle
cap and must not rerun unchanged commands.
