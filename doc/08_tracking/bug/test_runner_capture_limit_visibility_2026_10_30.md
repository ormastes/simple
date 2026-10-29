# Native test-runner capture limit has private declaration visibility

The source-matched native SSpec runner passes HIR/MIR for all 304 modules, but
Cranelift rejects nine importing modules because `TEST_OUTPUT_CAPTURE_BYTES`
is a non-public module static. The defining `test_runner_types.spl` declares
it with `val`, although the package facade explicitly exports it and runner,
doctest, process-tracker, and lifecycle modules import it directly.

Declare this existing shared constant `pub val` in its defining module. Keep
its 4 MiB value and the backend's private-static rejection unchanged. This
restores the intended cross-module API without making unrelated statics public.

Native failure evidence:
`/work/buildrunner-pair-6304-20261030/sspec-runner-9g/logs/build.log`.
The run completed below its 9.5 GiB process-tree limit: 295 native units passed,
nine failed, and link/publication was refused. No runner image was produced.
Producer SHA256:
`6304c166acbcac0a1ea78534fc9a5859507a87ad655eabf98618c798045ad6e8`.

Focused native regression:
`test/fixtures/test_runner/native_output_capture_limit.spl` imports the shared
scalar from another module and requires its exact value before printing a
success marker. Native red/green validation passed; the full runner rebuild
remains pending. This record does not claim native SSpec or HAL/SOSIX execution.

Actual native regression evidence:
- Red: build exit1 with the exact private-static diagnostic; log SHA256
  `a17096977122787cfda8f645835b63f58941648bede9fddb8aa04757ec8d0735`.
- Green: build exit0, no backend rejection, run exit0, exact stdout
  `PASS native test runner capture limit: 4194304` plus LF, empty stderr.
  Artifact SHA256 `a4bfdd366c00a488d1d15f81e427358e15b002e1b17bc1125dcdccd1a82a6073`.
  Build log SHA256 `f993a1b81c2ef739839421f2ceeca859f34c17b5a98162a7052328e1b02618df`.
- Evidence roots: `/work/native-capture-visibility-20261030/{red,green}`.
  Green source is b9c91 plus the reviewed source patch (commit
  `71cfe696ed9d6b80513a63da7039e1912e4231b6`); producer/runtime remained pinned.
  Both build receipts completed below their 6 GiB bound with quiescent trees.
