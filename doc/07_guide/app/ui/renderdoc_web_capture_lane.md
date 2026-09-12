# RenderDoc web capture lane (Linux, lavapipe)

Produces the two `.rdc` captures the web differential diffs: the pure-Simple
Vulkan web renderer and Chrome rendering the SAME catalog page ANGLE-on-Vulkan.
Folds into `renderdoc_web_diff.md` when that lands. RenderDoc captures Mesa's software Vulkan ICD (lavapipe/llvmpipe) fine, so the
lane runs on a GPU-less `ubuntu-latest` runner. A host without a Vulkan ICD,
RenderDoc or Chrome reports ERROR, never a pass.

```bash
sh scripts/setup/setup-renderdoc-linux-lavapipe.shs [--check]
sh scripts/check/check-renderdoc-web-capture-lane.shs --selftest
sh scripts/check/check-renderdoc-web-capture-lane.shs --page overview --page css-layout
```

Readiness keys `renderdoc_status=` / `lavapipe_status=` (from `vulkaninfo
--summary` showing llvmpipe) / `chrome_status=`, each `present|missing`.

## Triggers

`renderdoccmd capture` alone grabs nothing here: the Simple renderer is
offscreen (no present, no frame for F12) and Chrome's GPU work lives in a child
process. The lane reuses the repo's recipes: `rdoc_capture_simple_vulkan` around
`src/app/test/renderdoc_web_page_capture.spl` (brackets the page render with
`rt_renderdoc_*`), and `rdoc_capture_html` (GPU-child hooking + xvfb). Setup
also materialises `build/tools/renderdoc/etc/vulkan/implicit_layer.d/` — those
helpers override `VK_LAYER_PATH` and the distro ships that manifest elsewhere.

## Receipt

`build/renderdoc/receipt.env`, per page: `page_<name>_renderdoc_capture_simple_status`,
`..._chrome_status`, `..._chrome_vulkan_backing`, `..._renderdoc_diff_status`
(`blocked:diff-tool-missing` while `check-renderdoc-web-diff.shs` is absent).
Last stdout line: `PASS — <n> page(s) captured on both sides` / `FAIL — …` /
`ERROR — nothing was checked (<reason>)`, exit 0/1/2.

## The ANGLE rule (no log proof → not a pass)

`chrome_vulkan_backing=pass` needs a POSITIVE line proving ANGLE initialised on
Vulkan (`ANGLE (…Vulkan…)`), read from an explicit `--dump-dom chrome://gpu`
run with the same Vulkan flags plus the capture log. No log, no proof, or any
known failure marker ⇒ `vulkan-angle-unavailable`. Authority:
`src/app/ui/renderdoc_capture_lane_receipt.spl` (spec:
`test/01_unit/app/ui/renderdoc_capture_lane_receipt_spec.spl`), with a shell
twin in the lane so a runner needs no Simple binary to classify.

## CI and container

- `.github/workflows/renderdoc-web-diff.yml` — `workflow_dispatch` +
  path-filtered `pull_request`, 40-min timeout, **never required**. Dispatch:
  `gh workflow run renderdoc-web-diff.yml -f pages="overview css-layout"`;
  artifact `renderdoc-web-diff` (rdc, events.json, diff.md, receipt.env).
- `scripts/setup/prepare-renderdoc-web-diff-container.shs --build|--check|--run`
  — pinned Docker twin; repo bind-mounted read-only at `/repo`, never COPYed.
- Manifest row `renderdoc-web-capture-lane`, `tier=bootstrap`, advisory.

## Unverified without a Linux run

Lavapipe under RenderDoc's layer, Chrome issuing Vulkan work on lavapipe, `.rdc`
non-emptiness, and the seed building with `-p simple-driver --features vulkan`.
Only the classifiers, container contract and ERROR paths are proven on macOS.
