# Rendering Source Coupling Guard

## Overview

Validates the diff-scoped guard that prevents new GUI/web/2D rendering patches
from adding raw runtime calls or backend-proof pokes without routing through a
facade or documented compatibility helper.

## Operator Command

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/rendering_source_coupling_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Clean rendering-scoped diffs pass.
- New raw `rt_*` calls in rendering-scoped files fail.
- `rt_renderdoc_*` remains isolated to `scripts/tool/renderdoc-evidence.shs`.
- Obvious backend-proof assignment pokes fail.

## Production Guard

Run the source-coupling guard against a working diff:

```sh
sh scripts/check/check-rendering-source-coupling.shs
```

For a specific jj revision:

```sh
RENDERING_SOURCE_COUPLING_REVISION=<rev> sh scripts/check/check-rendering-source-coupling.shs
```
