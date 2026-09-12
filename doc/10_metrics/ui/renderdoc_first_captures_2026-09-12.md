# RenderDoc web-renderer differential — first capture attempt, 2026-09-12

Attempt to produce the FIRST real RenderDoc captures and diff of the Simple
Vulkan web renderer against Chrome (ANGLE/Vulkan on lavapipe) for the catalog
pages `overview` and `css-layout`.

## Route

**Route 2 (GitHub Actions).** Route 1 (local container) was rejected on
evidence, not preference — see "Route 1 blocked" below.

| | |
|---|---|
| Host | `ubuntu-latest` GitHub-hosted runner (x86_64), GPU-less |
| Driver model | Mesa lavapipe software Vulkan ICD |
| Workflow | `.github/workflows/renderdoc-web-diff.yml` |
| Lane | `scripts/check/check-renderdoc-web-capture-lane.shs --page overview --page css-layout` |
| Local host | macOS 15 (Darwin 25.5.0), arm64 — no RenderDoc, Docker daemon down |

## What was actually blocking: the lane had never provisioned RenderDoc

Run `34690832218` (the most recent lane run before this work) failed in
provisioning. `lavapipe_status=present`, `chrome_status=present`,
`renderdoc_status=missing` — the capture and diff steps never ran at all, so
no `.rdc` had ever been produced by this lane on any run:

```
E: Unable to locate package renderdoc
renderdoc_vulkan_only_src_status=missing
renderdoc_vulkan_only_build_status=missing
renderdoc_vulkan_only_renderdoccmd_status=missing
FAIL — 3 readiness key(s) checked, 1 missing
```

Two independent causes, both fixed in PR #644:

1. **`renderdoc` is not in the Ubuntu noble archive.** The apt install cannot
   supply it on `ubuntu-latest`. That call is already non-fatal; the repo's own
   source build is what is supposed to cover it.
2. **The source-build fallback never ran.**
   `scripts/setup/build-renderdoc-linux-vulkan-only.shs` defaults to
   `MODE=--check` (`MODE="${1:---check}"`), which only *records* prerequisites
   and the current output state, then exits 0.
   `build_renderdoc_if_needed` invoked it **bare**, so it printed the
   `*_status=missing` keys above and returned success. No
   `renderdoc_lavapipe_build=failed` was printed because nothing had failed —
   nothing had been attempted. A probe was being read as a build.

Two further defects were found by reading ahead rather than waiting an hour to
be told. The lane was on course to produce two valid `.rdc` files and then
report `renderdoc_diff_status=blocked` — captures without a diff.

3. **`renderdoccmd python` does not exist.** `renderdoc-export-events.shs`
   shells out to it on the non-`qrenderdoc` path. Checked against RenderDoc
   v1.44 source: `renderdoccmd.cpp` registers `vulkanlayer`, `version`, `help`,
   `capture`, `inject`, `thumb`, `remoteserver`, `replay`, `capaltbit`, `test`,
   `convert`, `embed`, `extract` — and nothing else. The `PYTHON_AVAILABLE`
   guards in that file gate `test functional`, **not** a python command. That
   branch could never have worked; every non-`qrenderdoc` export was
   `blocked:export-failed`.
4. **The pyrenderdoc module was neither built nor installed.** The supported
   headless path is the swig module (`qrenderdoc/Code/pyrenderdoc`: `_renderdoc`
   plus a generated `renderdoc.py`), gated by `ENABLE_PYRENDERDOC` — which the
   builder hardcoded OFF — and it has **no `install()` rule**, so even when
   built it stays in the build tree, outside both the install prefix and the CI
   cache.

## Fixes landed (PR #644)

| Fix | File |
|---|---|
| Invoke the builder with `--all`, install its `--print-deps` prerequisites, and re-assert `renderdoccmd` exists afterwards so a silent build failure cannot be laundered into a pass | `scripts/setup/setup-renderdoc-linux-lavapipe.shs` |
| `RENDERDOC_ENABLE_PYTHON=1` (set by the setup script; the builder's own default stays `0`) builds the Python bindings, **falling back** to a bindings-less build if that configure fails; resolved mode recorded as `renderdoc_vulkan_only_python_bindings=on\|off` | `scripts/setup/build-renderdoc-linux-vulkan-only.shs` |
| Stage the built pyrenderdoc module into `$RDOC_HOME/pymodules` at install time, so the prefix is self-contained and the CI cache carries it | `scripts/setup/build-renderdoc-linux-vulkan-only.shs` |
| Run the exporter as `python3 <exporter>` with `PYTHONPATH` pointing at that module instead of the nonexistent `renderdoccmd python`; fail closed with `blocked:pyrenderdoc-module-missing` when it is absent | `scripts/tool/renderdoc-export-events.shs` |
| Cache the RenderDoc build; `cache/restore` + `cache/save` split with `if: always()` because `actions/cache@v4` saves only on job success, which would discard the 10-20 min build on every red run; timeout 40 -> 90 min | `.github/workflows/renderdoc-web-diff.yml` |

Verification available at the time of writing: lane classifier selftest
`PASS — 9 fixture(s) checked, 0 failures`; `sh -n` clean on both scripts; push
guards conflict-markers / tree-size / guard-wiring all PASS.

## Capture results

**NOT OBTAINED IN THIS SESSION.** The lane run carrying all four fixes,
`34692788301` (tip `a1477d19`), sat `queued` for **42+ minutes without a runner
ever being assigned** — `started_at` was stamped at enqueue, no step ever
reached a conclusion, and the job status never left `queued`. That is past the
time budget allotted for this work, so the session stops here and reports
rather than holding the PR open indefinitely.
Earlier runs on intermediate commits were cancelled deliberately to free queue
capacity, and a `workflow_dispatch` run on `main` (`34692247209`) was cancelled
by the runner queue itself with zero steps executed. The blocker is runner-queue
capacity, not the lane.

Local coverage of these changes is partial and stated as such: the capture
lane's classifier selftest passes on macOS (9 fixtures), but
`check-renderdoc-web-diff.shs --selftest` correctly ERRORs `no-simple-binary`
here, so the diff-side and exporter changes have **no local test coverage** —
the CI run is their first execution.

No `.rdc` exists yet, so there is no event count, no `RENDERDOC DIFF:` verdict,
no first divergent event, and consequently **no classification of Simple-side
rendering defects vs Chrome compositor pipeline-shape differences**. Those rows
are deliberately left empty rather than estimated.

Note for whoever reads the first result: the seed build step is
`continue-on-error` and marked UNVERIFIED on Linux. If it fails the lane ERRORs
`simple-binary-unavailable` *before* the page loop, yielding zero captures on
**both** sides — that is a Rust-seed problem, not a renderer defect. Likewise a
valid Chrome `.rdc` carrying `chrome_vulkan_backing=vulkan-angle-unavailable`
is an environment/proof gap, not a Simple rendering defect.

## Route 1 blocked (local container), with reasons

- Docker Desktop is installed but the daemon was down and did not come up.
- The image is **arm64 Linux** on this host: `Dockerfile.renderdoc-web-diff`
  hardcodes the amd64 Google Chrome `.deb` and
  `VK_ICD_FILENAMES=.../lvp_icd.x86_64.json`, and Google publishes no Linux
  arm64 Chrome. The Ubuntu `chromium` package is a snap transitional stub that
  cannot run in a container.
- `--run` mounts the repo read-only with `--network=none` and passes no
  `RDOC_SIMPLE_BIN`, so the lane would ERROR `simple-binary-unavailable`
  regardless; supplying it needs a separate ~20 min network-enabled arm64
  cargo build plus a passthrough edit.

Route 1 needs its own change set and was not attempted.

## Resume command

```bash
gh run list --workflow=renderdoc-web-diff.yml -L 5 --json databaseId,status,conclusion
gh run watch 34692788301 --exit-status          # or the newest run id
gh run download 34692788301 -D build/renderdoc/ci
cat build/renderdoc/ci/receipt.env              # per-page *_status, *_diff_status
cat build/renderdoc/ci/*/diff.md                # RENDERDOC DIFF: verdict
```

The fixes are landed on `main`, so re-dispatch there:

```bash
gh workflow run renderdoc-web-diff.yml -r main -f pages="overview css-layout"
gh run list --workflow=renderdoc-web-diff.yml -L 1 --json databaseId,status
```

**Read the receipt, not just the verdict.** The lane's PASS/FAIL keys off
capture status and Chrome ANGLE backing; `renderdoc_diff_status` does not
affect it, so the lane can PASS with the diff still blocked. The keys that say
whether this work actually finished are:

- `renderdoc_vulkan_only_python_bindings=on` — the bindings built (in
  `build/tools/renderdoc-linux-vulkan-only-build/evidence.env`); `off` means
  the swig configure failed and the exporter will report
  `blocked:pyrenderdoc-module-missing`.
- `renderdoc_vulkan_only_pymodule_dir` — non-empty means the module was staged.
- `page_<name>_renderdoc_diff_status` — anything other than `blocked:*` means
  the diff finally ran.
