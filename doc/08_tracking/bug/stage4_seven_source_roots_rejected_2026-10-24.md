# Stage 4 native-build rejected: 7 --source roots vs 5-root cap (2026-10-24)

Symptom: sanctioned Stage 4 fails immediately with the Stage 2 compiler:
`Error: focused native-build accepts at most five --source roots`.

Cause: `bootstrap_native_build_main` in `scripts/bootstrap/bootstrap-from-scratch.sh`
passed 7 roots (cuda, src/compiler, src/app, src/lib, src/os, plugin policy,
examples/10_tooling). `bootstrap_main.spl:335` routes `--entry` + `SIMPLE_BOOTSTRAP_STAGE4=1`
to `run_exact_stage4_focused_capsule`, whose `focused_native_build_error`
(`src/app/cli/bootstrap_focused_native_build.spl:32`) caps roots at 5. The cap is
pinned by `test/01_unit/app/cli/bootstrap_focused_native_build_spec.spl`.
In exact-Stage4 mode `focused_native_build_effective_sources` returns `[]`, so roots are
only counted, never used (the driver seeds the entry and follows imports).

Fix: script passes five roots (dropped src/os and examples/10_tooling, both reachable
via entry closure). The compiler cap and its spec are unchanged, since a compiler-side
relaxation would not reach the prebuilt Stage 2 compiler.

Verification: `sh -n` only; no bootstrap was run.
