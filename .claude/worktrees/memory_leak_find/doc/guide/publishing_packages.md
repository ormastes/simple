# Publishing Packages

How to publish Simple packages to the GHCR-based registry.

---

## Quick Start

```bash
# 1. Authenticate
export SIMPLE_TOKEN=ghp_your_token

# 2. Create your package
simple init my-package
cd my-package

# 3. Write your code in src/

# 4. Publish
simple publish
```

---

## Package Manifest

Your `simple.sdn` must include `name` and `version`:

```sdn
package:
  name: my-package
  version: 1.0.0
  license: MIT
  description: A useful library
  homepage: https://github.com/you/my-package

dependencies:
  json: ^1.0
```

## Version Bumping

Update the `version` field in `simple.sdn` before each publish. The registry rejects duplicate versions.

## Pre-publish Checklist

- [ ] Tests pass: `simple test`
- [ ] Version bumped in `simple.sdn`
- [ ] No sensitive files (`.env`, credentials)
- [ ] README.md is up to date

## Dry Run

Preview what will be published without uploading:

```bash
simple publish --dry-run
```

## Publishing

```bash
simple publish
```

This will:
1. Read `simple.sdn` for name and version
2. Build a `.spk` tarball (excludes `.jj/`, `target/`, etc.)
3. Compute SHA-256 checksum
4. Push to `ghcr.io/simple-lang/<name>:<version>`
5. Print instructions for updating the registry index

## Yanking a Version

If you publish a broken version:

```bash
simple yank my-package 1.0.0
```

Yanked versions remain downloadable but are not selected by default. To undo:

```bash
simple yank my-package 1.0.0 --undo
```

## CI/CD Publishing

Use the provided GitHub Actions workflow (`.github/workflows/publish.yml`). Tag a release to trigger:

```bash
jj bookmark set v1.0.0 -r @
jj git push --bookmark v1.0.0
```
