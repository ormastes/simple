# Task #35 — Default Output Escaping to Repo Root: Containment Plan

Status: plan (dispatch document; single lane). Triage performed 2026-08-05 —
this task no longer needs a triage lane; the mechanism is understood and the
bug sites are enumerated below. Note: the "#35" number is unresolvable in
tracking (`doc/TODO.md:59` item #35 is unrelated); the bug itself is real,
evidenced by the standing `.gitignore:8-9` workaround (`/a.out` with the
comment "Stray tool outputs dropped in CWD").

## Mechanism (established, not hypothesized)

- `bin/simple build` and `bin/simple build bootstrap` fall through to
  `cli_native_build` with no injected `-o`
  (`src/app/build/cli_entry.spl:68-77`), and the native-build pipeline
  defaults to `var output = "a.out"` at
  `src/app/io/_CliCompile/compile_targets.spl:772`.
- Parent-dir creation at `compile_targets.spl:1015-1017` only fires when the
  output contains `/` — a bare `a.out` writes to cwd, which the bootstrap
  scripts pin to the repo root (`scripts/bootstrap/bootstrap-from-scratch.sh:304`).
- Escaping artifacts beyond `a.out` itself (NOT covered by `.gitignore`):
  `a.out.simple-native-build-<pid>-<micros>.tmp` (`compile_targets.spl:1025`),
  `a.out.simple_launch.sdn` (`compile_targets.spl:1229` +
  `src/app/startup/launch_metadata.spl:151-152`),
  `a.out.s` (`src/compiler/70.backend/linker/mold.spl:177`).
- The same `"a.out"` default is repeated at:
  `src/app/cli/bootstrap_main.spl:20-22`,
  `src/app/io/_CliCompile/compile_opt_and_driver.spl:88`,
  `src/compiler/80.driver/driver_aot_pipeline.spl:86`,
  `src/compiler/80.driver/main.spl:590`,
  `src/compiler/80.driver/driver_types.spl:87`,
  `src/compiler/70.backend/linker/link.spl:62`, and in the seed at
  `src/compiler_rust/compiler/src/linker/native_binary_options.rs:116` and
  `.../native_binary/options.rs:93`.

## Decision (made here — the lane implements, it does not choose)

Default output becomes **`build/native/<entry-stem>`** (e.g.
`build/native/main` for `main.spl`) instead of `a.out`; sidecars follow the
binary. Explicit `-o` behavior is unchanged. Parent-dir creation becomes
unconditional. The literal `a.out` default is removed from ALL Simple-side
sites listed above (a sweep must enumerate the family — fixing only
`compile_targets.spl:772` leaves six siblings to resurface). The seed Rust
defaults are left as-is in this lane (seed is bootstrap-only; changing it
forces a slow rebuild for no user-visible gain) — but the lane must VERIFY the
seed default is unreachable from `bin/simple build` paths, and file a
follow-up if reachable.

## Lane D1 — implement containment

**Owns:** `src/app/io/_CliCompile/compile_targets.spl` (`:772`, `:1015-1017`,
`:1025`, `:1229`), `src/app/io/_CliCompile/compile_opt_and_driver.spl:88`,
`src/app/build/cli_entry.spl:68-77`, `src/app/cli/bootstrap_main.spl:20-22`,
`src/compiler/80.driver/driver_aot_pipeline.spl:86`,
`src/compiler/80.driver/main.spl:590`,
`src/compiler/80.driver/driver_types.spl:87`,
`src/compiler/70.backend/linker/link.spl:62`,
`src/compiler/70.backend/linker/mold.spl:177` (sidecar path only),
`src/app/startup/launch_metadata.spl:151-152` (sidecar path only),
`.gitignore` (drop the now-dead `/a.out` workaround ONLY after the gate is
green), `test/01_unit/app/cli/default_output_dir_spec.spl` (new).

**Pre-step (mandatory, before any edit):**
`/usr/bin/grep -rn '"a\.out"\|a\.out' scripts/check scripts/bootstrap test --include='*.shs' --include='*.spl' --include='*.sh'`
— any test/script relying on the literal `a.out` default gets updated in the
same change (they are inside the owns-list by this clause) or, if outside
scope, reported. The bootstrap shell scripts already pass explicit `-o`
everywhere (verified: `bootstrap-from-scratch.sh:823,1473,1496,1530,1639,
1813,1988,2030`) so they are expected to be unaffected — confirm, don't assume.

**Gate (engines: this is CLI/driver logic — the spec runs under the default
runner; additionally one real end-to-end compile is required):**
```
bin/simple test test/01_unit/app/cli/default_output_dir_spec.spl \
  --no-cache --no-cover-check > /tmp/d1.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/d1.log
```
Receipt: `failed=0 dropped=0 executed>=5`. Required assertions: (a) no `-o` →
resolved output path is `build/native/<stem>` (assert the exact string from
the resolver function); (b) explicit `-o custom/x` → unchanged; (c) sidecar
paths (`.simple_launch.sdn`, staging `.tmp`, `.s`) all derive from the
resolved output, never from cwd; (d) parent dir is created for a bare
filename. End-to-end: from a CLEAN temp worktree copy, run
`bin/simple build` (or compile one entry with no `-o`), then
`git status --porcelain` in that worktree must show NO new untracked entries
at the repo root (this is the receipt the `.gitignore` removal depends on).
Trap note: the compile CLI has a known fail-open shape (absolute-path invoke
exits 0 without compiling) — assert the output FILE EXISTS at the new path,
never exit status alone.

**Sabotage:** revert `compile_targets.spl:772` to `"a.out"` only → assertion
(a) RED AND the end-to-end `git status` check shows root pollution. Both must
fire; if the end-to-end check stays green while (a) is red, the end-to-end
harness is broken — fix it before proceeding.
**Size:** 1–2 agent-sessions. **Status: dispatchable now.**
