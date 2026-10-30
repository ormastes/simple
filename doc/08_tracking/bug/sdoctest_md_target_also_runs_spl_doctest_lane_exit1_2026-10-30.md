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
