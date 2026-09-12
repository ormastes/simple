# `Native — macOS aarch64` red on `main`: `rust-bootstrap-multiplatform.yml` never installs freetype

- **Filed:** 2026-09-01
- **Status:** FIX LANDED, verification in progress (2026-09-12) — see "Re-verified" section below
- **Lane:** `.github/workflows/rust-bootstrap-multiplatform.yml`, job `native`, step `Test`
- **Severity:** blocks every macOS row of that workflow; every PR touching its trigger paths shows a red macOS check

## Verbatim failure

Step `Test` (`cargo test --workspace --lib`, working-directory `src/compiler_rust`):

```
error: linking with `cc` failed: exit status: 1
  = note: "cc" ".../deps/rustcrM1Uzy/symbols.o" "<31 object files omitted>" "-lfreetype" ... "-o" ".../deps/spl_fonts-625049d1b82706dd" "-Wl,-dead_strip" "-nodefaultlibs"
  = note: some arguments are omitted. use `--verbose` to show all linker arguments
  = note: ld: library 'freetype' not found
          clang: error: linker command failed with exit code 1 (use -v to see invocation)

error: could not compile `spl_fonts` (lib test) due to 1 previous error
warning: build failed, waiting for other jobs to finish...
##[error]Process completed with exit code 101.
```

## Evidence it is pre-existing, not PR-caused

| where | run / job | head | event | result |
|---|---|---|---|---|
| `main` | run `33483308796` / job `99777638951`..`99777639056` | `591aad1791e7353c43c5010e3ba867c3b6a252f5` | **push to `main`** | `Native — macOS aarch64` **failure**, byte-identical `ld: library 'freetype' not found` at log line 1686 |
| PR #252 | run `33488592769` / job `99794430881` | `477d446129e94c5635b3779713e20aa797845f2d` | pull_request | same failure, log line 1668 |

- main links: https://github.com/ormastes/simple/actions/runs/33483308796 (job 99777639056)
- PR #252 links: https://github.com/ormastes/simple/actions/runs/33488592769/job/99794430881

Second, independent argument: PR #252 changes **no Rust at all** — its file list is 7 `.spl` files under `src/lib/**` + 1 `.spl` spec + 1 doc. The failing crate `src/compiler_rust/spl_fonts` is untouched by it.

## Root cause (file:line)

`src/compiler_rust/spl_fonts/src/lib.rs:134` declares `#[link(name = "freetype")]`
**unconditionally** — no `cfg`, every target. So any link of `spl_fonts` (including
its `lib test` harness) needs a freetype import library on the linker search path.

`.github/workflows/rust-bootstrap-multiplatform.yml` job `native` (matrix at
`:100-118`, steps `:121-160`) installs **no** system dependencies at all. On
`macos-latest` / `macos-13` freetype is not in the default link path.

The sibling workflow already carries the working pattern —
`.github/workflows/rust-tests.yml:92-102`:

```yaml
    - name: Install SPIR-V Tools (Ubuntu)
      if: runner.os == 'Linux'
      run: |
        sudo apt-get update
        sudo apt-get install -y spirv-tools libfreetype6-dev

    - name: Install SPIR-V Tools (macOS)
      if: runner.os == 'macOS'
      run: |
        brew install spirv-tools freetype
        echo "LIBRARY_PATH=$(brew --prefix freetype)/lib:$LIBRARY_PATH" >> "$GITHUB_ENV"
        echo "CPATH=$(brew --prefix freetype)/include:$CPATH" >> "$GITHUB_ENV"
```

Note the `Build` step (`cargo build --profile bootstrap -p simple-driver`) PASSES —
only the workspace-wide `--lib` test pulls `spl_fonts` into a link.

## Proposed patch (not applied — CI-for-everyone, reserved for the owner)

Insert into `.github/workflows/rust-bootstrap-multiplatform.yml`, in job `native`,
**between** the `dtolnay/rust-toolchain@nightly` step and `Cache Cargo`:

```yaml
      - name: Install freetype (macOS)
        if: runner.os == 'macOS'
        run: |
          brew install freetype
          echo "LIBRARY_PATH=$(brew --prefix freetype)/lib:$LIBRARY_PATH" >> "$GITHUB_ENV"
          echo "CPATH=$(brew --prefix freetype)/include:$CPATH" >> "$GITHUB_ENV"
```

Cross-platform impact: **none outside macOS.** The step is gated
`if: runner.os == 'macOS'`; the Linux, Windows and FreeBSD rows are byte-unchanged
and continue to link as they do today. This is additive — it installs a dependency
that the crate has always required, and changes no compiler or runtime source.

Scope caveat, stated rather than presumed: the `#[link]` is unconditional, so the
defect is "any runner without a freetype dev library on the link path", not
"macOS-only" by construction. Empirically only the macOS rows have been observed
red; `Native — macOS x86_64` (macos-13) was still queued at filing time and is
expected to fail identically. If a Linux or Windows row is ever seen with this
error, add the corresponding install rather than reclassifying this record.

## Blast radius across open PRs (measured 2026-09-01)

| PR | macOS aarch64 check | shares this failure? |
|---|---|---|
| #252 | failure | YES (pre-existing, not caused by it) |
| #253 (`52f6af5b9a7`) | queued | expected YES — triggers the same workflow |
| #247 (`bee1f952460`) | no macOS check-run | no — workflow not triggered by its paths |
| #235 (`a2475e29cc2`) | no macOS check-run | no — workflow not triggered by its paths |

## Re-verified 2026-09-12 — fix present, `Test`-step verdict still pending

The proposed patch is already committed on `main` (`.github/workflows/rust-bootstrap-multiplatform.yml:150-155`,
introduced at `6dfbf2cae86` on 2026-09-01): a macOS-gated `Install freetype (macOS)` step runs
`brew install freetype` and exports `LIBRARY_PATH`/`CPATH` before the `Build`/`Test` steps.

Every recent scheduled/push run of this workflow on `main` is `cancelled` by its own
`concurrency: group: ${{ github.workflow }}-${{ github.ref }}` before completing (main advances too
fast for a full multi-hour matrix to finish uncancelled) — `gh run list --workflow=rust-bootstrap-multiplatform.yml --limit 100`
shows 0 runs with `conclusion` in `{success, failure}` in the last 100 pushes/PRs. This is why the
fix could not be confirmed passively, and it is also why a direct `gh workflow run ... --ref main`
dispatch does not help: it shares main's own concurrency group and gets cancelled by the next push
to main just like every other run.

First dispatch (on `main`, wrong ref for this reason): run
https://github.com/ormastes/simple/actions/runs/34678730839. `Native — macOS aarch64`'s
`Install freetype (macOS)` step completed **success** (not skipped) before the whole run was
cancelled by a later push to `main` — this confirms the step itself works, but does NOT confirm the
subsequent `Test` step (the one that actually failed with `ld: library 'freetype' not found` in the
original incident) completes green, since the run never reached a terminal `Test` conclusion.

**Correct verification path (not yet completed this session):** dispatch on an isolated ref instead
of `main` so the run cannot be cancelled by main's own churn:

```sh
gh workflow run rust-bootstrap-multiplatform.yml --ref work/macos-lane5-ci-docgen-2026-09-12
gh run list --workflow=rust-bootstrap-multiplatform.yml --limit 5   # get the run id
gh run view <id> --log-failed | grep -c "library 'freetype' not found"   # must be 0
```

Status: fix is landed and its `Install` step is confirmed to execute and succeed; the `Test`-step
verdict on macOS aarch64/x86_64 is NOT yet confirmed green in this session because every attempted
run was cancelled by unrelated main-branch concurrency before reaching that step. Do not mark
RESOLVED until a run dispatched on a non-`main` ref reaches a terminal `Test` conclusion with 0
occurrences of the original error text.
