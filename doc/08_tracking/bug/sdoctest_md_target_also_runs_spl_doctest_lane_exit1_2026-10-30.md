# `simple test --sdoctest <file.md>` exits 1 on a passing md file

- Found by: `test/03_system/app/test_runner/test_runner_phase2_four_formats_spec.spl`
  (the md half of "reports a green example of each format as PASS").
- Repro (release bd170855af5, seed `src/compiler_rust/target/release/simple`):
  `simple test --no-db --sdoctest build/phase2_formats/green.md`
  (a md file with one fenced `simple` block, `expect(6 * 7).to_equal(42)`).
- Result: exit 1. The run first enters the SPL (comment) doctest lane with the
  `.md` as the explicit target, prints `error: test-runner: no doctest blocks
  found` / `SPL Doctest: 0 passed, 1 failed`
  (`src/lib/nogc_sync_mut/test_runner/test_runner_modes.spl:132`). It then runs the
  sdoctest lane, which reports `PASS ... 1 passed` / `All sdoctest blocks passed!`.
  The fail-closed "explicit target with no blocks" failure from the wrong lane
  sets the exit code.
- Expected: `--sdoctest <md>` runs only the md lane (or the comment lane skips
  non-`.spl` explicit targets), so a passing md file exits 0.
- Not caused by rt_tuple_len (#5340). With that fixed, the comment, sspec and spec
  formats are green and only md stays red.
- Spec marker: the md green check is a `skip(...)` linking here, and its body is
  kept in `check_md_green_passes()`. To unblock, restore it as
  `it "reports a green md example as PASS": check_md_green_passes()`.
