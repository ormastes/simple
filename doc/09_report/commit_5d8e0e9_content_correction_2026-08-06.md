# Correction: commit `5d8e0e9` carried far more than its subject line says

**Subject as pushed:** `docs(bug): separate the MEASURED enum-unwrap cause from the UNVERIFIED structural one`

**What it actually contained:** 33 files, 784 insertions, 75 deletions — including
substantial source changes that the message never mentions.

## Why this is recorded rather than rewritten

The commit is already pushed and several sessions are pushing to `main`
continuously. Rewriting history here would be more dangerous than the mislabel.
So the record is corrected forward instead.

## What actually landed in `5d8e0e9`

Beyond the intended bug-doc correction:

- **Workstream C step-6 trait migration** — `poll_key`/`poll_mouse` removed from
  `trait InputBackend` and every implementor migrated onto the unified
  `poll_event`/`HostInputEvent` path: `input_backend.spl`,
  `hosted_input_sdl2.spl`, `hosted_input_backend.spl`, `uart_input_backend.spl`,
  `usb_hid_input_backend.spl`, `arm64_virtio_input_backend.spl`,
  `compositor.spl`, plus ~15 trait-implementing spec stubs.
- **`ShowcaseSurface` schema work** — `src/lib/common/ui/showcase_catalog.spl`,
  `src/os/apps/showcase_catalog/*`, and their specs.
- **A new `compositor_occlusion_spec.spl`** from the D6 backing-store work.

## Cause

The staging step globbed all changed paths rather than the specific files the
message described, and three agents had landed work into the tree between the
previous commit and this one. The exclusion list filtered other sessions' files
correctly — no foreign work was swept — but it did not constrain the commit to
the subject's scope.

## The rule this violated

`.claude/rules/` warns that bulk commits hide semantic changes behind their
label. This is the inverse of the usual failure: a `docs:`-prefixed commit
carrying a trait-signature migration across seven source files. A reviewer
scanning subject lines would not know to review it.

## Corrective practice

Stage an explicit file list matching the commit message, not a filtered glob of
everything currently dirty — especially while parallel agents are writing into
the same tree.
