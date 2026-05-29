# Script Layout Policy

This repo keeps command entrypoints in two different places on purpose:

- `scripts/` for source-controlled development and CI helpers
- `bin/` for generated launchers, release binaries, and user-facing wrappers

The policy checker is:

```bash
sh scripts/check_script_layout.shs
```

## Rules

### 1. Shell scripts under `scripts/` should use `.shs`

Use `.shs` for normal repo shell entrypoints:

- `scripts/os_gui.shs`
- `scripts/make_os_disk.shs`
- `scripts/check_release_payload.shs`

The checker rejects new `scripts/*.sh` or `scripts/*.bash` files unless they are
listed in the ignore file:

```text
scripts/script_layout_ignore.txt
```

That ignore list exists for compatibility-only exceptions such as bootstrap and
setup paths that are already referenced externally.

### 2. `bin/` must not contain source-style shell filenames

The checker rejects `*.sh`, `*.shs`, and `*.bash` files under `bin/`.

`bin/` is reserved for:

- generated symlinks such as `bin/simple`
- generated wrapper launchers
- native binaries and packaged artifacts
- platform-native command wrappers such as `.cmd`

This keeps `bin/` as an install/runtime surface instead of a second source tree.

## Ignore List

The ignore file is newline-delimited and uses repo-relative paths:

```text
scripts/script_layout_ignore.txt
```

Blank lines and `#` comments are ignored.

Current exceptions are bootstrap/setup compatibility scripts such as:

- `scripts/setup.sh`
- `scripts/install-dev-tools.sh`
- `scripts/platform-detect.sh`
- `scripts/bootstrap/*.sh`

Do not add product scripts here just to bypass the rule. If a new shell helper
is part of normal repo usage, prefer `.shs`.

## When It Runs

The checker is wired into:

- `scripts/setup.sh`
- `scripts/install-dev-tools.sh`

You can also run it directly in CI or locally:

```bash
sh scripts/check_script_layout.shs
```

## Typical Workflow

```bash
# Install local dev tools
bash scripts/install-dev-tools.sh

# Create/update bin/ symlinks and launchers
sh scripts/setup.sh

# Re-run the policy check directly
sh scripts/check_script_layout.shs
```

## Current Scope

This checker only enforces layout and naming policy. It does not replace:

- `shellcheck`
- syntax checks (`sh -n`, `bash -n`)
- the existing violation checker

Use it as a focused guardrail for repository structure.
