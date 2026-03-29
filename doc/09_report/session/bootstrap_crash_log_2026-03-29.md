# Bootstrap Repro Log 2026-03-29

## Command

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap-crash-repro
```

## Result

- Exit status: `1`
- First failing stage: `stage2-native-build`
- Stage log:
  - `build/bootstrap-crash-repro/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`

## Bootstrap Script Logging

Bootstrap scripts now write per-stage logs under:

```text
<output>/logs/<platform>/
  rust-seed-build.log
  stage1-native-build.log        # Windows only
  stage2-native-build.log
  stage3-native-build.log
  stage4-native-build.log
```

On failure the script reports the failing stage, exit code, and log path.

## First Repro Finding

This repro did **not** hit the later self-hosted segfault path first.
It stopped earlier in stage 2 on parser incompatibilities while compiling
`src/app/cli/bootstrap_main.spl` transitive dependencies.

Tail of the stage2 log reports:

- `src/compiler/80.driver/build/installer.spl`
  - parse: unexpected comma in grouped `use ... (...)`
- `src/compiler/90.tools/__init__.spl`
  - parse: unexpected comma in export list / `export use`
- `src/compiler/driver/build/installer.spl`
  - parse: unexpected comma
- `src/compiler/tools/__init__.spl`
  - parse: unexpected comma
- `src/lib/nogc_sync_mut/package/installer/backend_fpm.spl`
  - parse: unexpected newline
- `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
  - parse: unexpected assign token

The final stage2 error summary is:

```text
Build failed: native-build aborted: 4 critical file(s) failed to compile
```

## Likely Meaning

- The stage2 bootstrap compiler/parser does not yet accept some newer source forms
  that the repository currently uses.
- Candidate unsupported forms seen in the failing files:
  - grouped `use module (...)` imports
  - long export lists
  - `export use ...`
  - newer expression/assignment forms in `dom_backend.spl`

## Relevant Source Notes

- Existing repo note for later self-hosted runtime crash:
  - `doc/08_tracking/bug/engine_2d_limitations.md`
  - LIM-010 says `bin/simple_native` / `bin/simple_stage4` can still segfault
    in generic run/check/test flow.

## Next Suggested Debug Order

1. Make stage2 parser-compatible with the current source tree.
2. Re-run bootstrap until stage3/stage4 execute.
3. Only then investigate any remaining self-hosted runtime segfault, using the
   per-stage logs added in this session.

## Progress Update After First Fixes

Applied source compatibility fixes in:

- `src/compiler/80.driver/build/installer.spl`
- `src/compiler/driver/build/installer.spl`
- `src/lib/nogc_sync_mut/package/installer/backend_fpm.spl`
- `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
- `src/compiler/90.tools/__init__.spl`
- `src/compiler/tools/__init__.spl`

Re-run command:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap-crash-repro3
```

Observed behavior:

- The original stage2 parser abort no longer reproduces.
- Stage2 now progresses into a much longer codegen phase.
- Bootstrap logs were further tightened so stage2/stage3/stage4 inherit
  `RUST_LOG=error`, preventing multi-hundred-megabyte Cranelift info logs.
- The `build/bootstrap-crash-repro3` run captured so far was terminated by the
  session timeout rather than a deterministic compiler crash, so the next step
  is a longer unattended run or a narrower stage2 repro around the emitted
  `[CODEGEN-WARN]` incompatibility warnings.
