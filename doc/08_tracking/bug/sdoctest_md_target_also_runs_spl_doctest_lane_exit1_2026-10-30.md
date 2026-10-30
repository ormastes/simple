# `simple test --sdoctest <file.md>` exits 1 on a passing md file

- Found by: `test/03_system/app/test_runner/test_runner_phase2_four_formats_spec.spl`
  (the md half of "reports a green example of each format as PASS").
- Repro (release bd170855af5, seed `src/compiler_rust/target/release/simple`):
  `simple test --no-db --sdoctest build/phase2_formats/green.md`
  (a md file with one fenced `simple` block, `expect(6 * 7).to_equal(42)`).
- Result: exit 1. `config/simple.test.sdn:49` sets `run_spl_doctests: true`, and
  `src/app/test_runner_new/test_runner_main.spl:1424-1426` turns off the spec lane for a `.md`
  target but leaves `run_spl_doc` on. The comment lane gets the `.md` as its explicit target.
  `discover_spl_doctest_files` (`test_runner_modes.spl:60-61`) keeps only `.spl` files, so its
  fail-closed `files.len() == 0` branch (`:77-78`) prints `error: test-runner: no doctest blocks
  found` and adds a failure. The sdoctest lane then reports `PASS ... 1 passed`.
- Expected: `--sdoctest <md>` also clears `run_spl_doc` (or the comment lane skips
  non-`.spl` explicit targets), so a passing md file exits 0.
- Not caused by rt_tuple_len (#5340). With that fixed, the comment, sspec and spec
  formats are green and only md stays red.
- Spec marker: the md green check is a `skip(...)` linking here, and its body is
  kept in `check_md_green_passes()`. To unblock, restore it as
  `it "reports a green md example as PASS": check_md_green_passes()`.

## Status: FIXED (2026-10-30)

- Root cause: the comment-doctest lane was not restricted to `.spl` targets. The full
  runner (`test_runner_main.spl`) cleared only the spec lane for an `.md` target and
  kept `run_spl_doctests: true` from config; the single lane (`test_runner_single.spl`)
  and the client lane (`test_runner_client.spl`) sent any `--spl-doctest` run to the
  comment lane before checking for an `.md` target.
- Fix: an `.md` target, or `--sdoctest` without `--spl-doctest`, runs only the
  markdown lane in all three lanes; `--spl-doctest` applies only to non-`.md` targets.
- Specs: `test/02_integration/app/test_runner_sdoctest_md_lane_only_spec.spl`
  (reproducer: `--sdoctest green.md` exits 0 on both lanes; generalization: no `.md`
  target form prints the SPL Doctest lane; red on the old runner, green now). The md
  green example in `test_runner_phase2_four_formats_spec.spl` is unskipped (4/4 pass).
