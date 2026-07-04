# GUI Web 2D Vulkan Setup Simple Binary Selection

## Overview

This system spec validates the Simple binary discovery contract for
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`.

Clean jj worktrees may not have a repo-local `bin/simple` or git metadata for
same-repo PATH detection. The setup helper therefore supports PATH discovery
only when explicitly enabled with `ALLOW_PATH_SIMPLE_BIN=1`, and records the
selection reason in evidence.

## Operator Flow

Run:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_vulkan_setup_simple_bin_spec.spl --mode=interpreter --clean --fail-fast
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

## Acceptance

- Same-repo PATH fallback remains available when git metadata can prove the
  binary belongs to the checkout.
- Generic PATH fallback requires `ALLOW_PATH_SIMPLE_BIN=1`.
- The opt-in fallback records
  `gui_web_2d_vulkan_simple_bin_selection_reason=default-missing-path-opt-in`.
- Evidence always emits `gui_web_2d_vulkan_simple_bin_selection_reason`.
