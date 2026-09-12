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

A third defect was found by reading ahead rather than waiting for it:
`scripts/tool/renderdoc-export-events.shs` shells out to `renderdoccmd python`,
which does not exist unless RenderDoc is built with the Python bindings, and
the builder hardcoded `-DENABLE_PYRENDERDOC=OFF`. The lane was on course to
produce two valid `.rdc` files and then report `renderdoc_diff_status=blocked`
— captures without a diff.

## Fixes landed (PR #644)

| Fix | File |
|---|---|
| Invoke the builder with `--all`, install its `--print-deps` prerequisites, and re-assert `renderdoccmd` exists afterwards so a silent build failure cannot be laundered into a pass | `scripts/setup/setup-renderdoc-linux-lavapipe.shs` |
| `RENDERDOC_ENABLE_PYTHON=1` builds the Python bindings, **falling back** to a bindings-less build if that configure fails; resolved mode recorded as `renderdoc_vulkan_only_python_bindings=on\|off` | `scripts/setup/build-renderdoc-linux-vulkan-only.shs` |
| Cache the RenderDoc build; `cache/restore` + `cache/save` split with `if: always()` because `actions/cache@v4` saves only on job success, which would discard the 10-20 min build on every red run; timeout 40 -> 90 min | `.github/workflows/renderdoc-web-diff.yml` |

Verification available at the time of writing: lane classifier selftest
`PASS — 9 fixture(s) checked, 0 failures`; `sh -n` clean on both scripts; push
guards conflict-markers / tree-size / guard-wiring all PASS.

## Capture results

**NOT OBTAINED IN THIS SESSION.** Both lane runs for PR #644
(`34692406802` on `fcbecf85`, `34692550694` on `ae604fd7`) were still `queued`
when the session ended; an earlier `workflow_dispatch` run on `main`
(`34692247209`) was cancelled by the runner queue with zero steps executed.
The blocker is runner-queue capacity, not the lane.

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
gh run watch 34692550694 --exit-status          # or the newest run id
gh run download 34692550694 -D build/renderdoc/ci
cat build/renderdoc/ci/receipt.env              # per-page *_status, *_diff_status
cat build/renderdoc/ci/*/diff.md                # RENDERDOC DIFF: verdict
```

If the queue cancels the run again, re-dispatch on the branch:

```bash
gh workflow run renderdoc-web-diff.yml -r work/renderdoc-first-captures-2026-09-12 \
  -f pages="overview css-layout"
```
