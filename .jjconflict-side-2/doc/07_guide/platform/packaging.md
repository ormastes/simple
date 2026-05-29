# Packaging, Installation, and Deployment Guide

Covers building distribution packages, installing/publishing Simple packages, GitHub registry setup, and deployment.

---

## Package Types

| Type | Size | Contents | Use Case |
|------|------|----------|----------|
| **Bootstrap** | ~10MB | Runtime + stdlib + examples | End users |
| **Full** | ~50MB | Runtime + all Simple source + docs | Developers |
| **Source** | ~20MB | All source (including Rust) | Contributors |

Distribution packages contain **zero Rust files** -- only pre-compiled binaries and Simple source code.

---

## Building Distribution Packages

### Quick Start

```bash
# Build all package types for current platform
simple scripts/package-dist.spl

# Build bootstrap only, with compression
simple scripts/package-dist.spl --bootstrap-only --compress

# Build for specific platform
simple scripts/package-dist.spl --platform=linux-x86_64
```

### Build Options

```bash
simple scripts/package-dist.spl [OPTIONS]

Options:
  --version=VERSION        Package version (default: from simple.sdn)
  --platform=PLATFORM      Target platform (linux-x86_64, darwin-arm64, etc.)
  --bootstrap-only         Build only bootstrap packages
  --compress               Compress with UPX (~50% size reduction)
```

### Cross-Compilation

**Linux ARM64 (from x86_64):**

```bash
sudo apt-get install gcc-aarch64-linux-gnu g++-aarch64-linux-gnu
rustup target add aarch64-unknown-linux-gnu
simple scripts/package-dist.spl --platform=linux-aarch64
```

**Windows (from Linux/macOS):**

```bash
sudo apt-get install mingw-w64     # Linux
brew install mingw-w64              # macOS
rustup target add x86_64-pc-windows-gnu
simple scripts/package-dist.spl --platform=windows-x86_64
```

### Size Optimization

| Profile | Size | Techniques |
|---------|------|------------|
| Debug | 423 MB | No optimization |
| Release | 40 MB | Opt-level 3, strip |
| Bootstrap | 10 MB | Opt-level z, LTO, strip |
| Bootstrap + UPX | ~5 MB | + UPX compression |

### Package Contents

**Bootstrap package:**

```
simple-bootstrap-0.5.0-linux-x86_64.tar.gz
  bin/simple              # Pre-compiled runtime (stripped)
  lib/std/                # Standard library (.spl source)
  examples/               # Example programs
```

**Full package** additionally includes `src/` (compiler, apps, libraries) and `doc/`.

**Excluded from all packages:** `rust/`, `build/`, `target/`, `test/`, `.git/`.

---

## Installing Packages

### From the Registry

```bash
# Install a specific package
simple install http

# Install all dependencies from simple.sdn
simple install

# Install with version constraint
simple install http --version="^1.0"

# Add to project dependencies
simple install http --save
```

### How It Works

1. Fetches the package index entry
2. Resolves the latest non-yanked version
3. Pulls the `.spk` artifact from GHCR
4. Verifies the SHA-256 checksum
5. Extracts to `~/.simple/packages/<name>/<version>/`

### Installed Package Locations

```
~/.simple/packages/
  http/1.1.0/
    simple.sdn
    src/
  json/2.0.1/
    ...
```

### Cache Management

```bash
# Clear downloaded package cache
rm -rf ~/.simple/cache/registry
```

---

## Publishing Packages

### Quick Start

```bash
# 1. Authenticate
export SIMPLE_TOKEN=ghp_your_token

# 2. Create package
simple init my-package && cd my-package

# 3. Write code in src/

# 4. Preview and publish
simple publish --dry-run    # Preview
simple publish              # Publish to registry
```

### Package Manifest (simple.sdn)

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

### Pre-publish Checklist

- Tests pass: `simple test`
- Version bumped in `simple.sdn`
- No sensitive files (`.env`, credentials)
- README is up to date

### Publishing Process

`simple publish` will:

1. Read `simple.sdn` for name and version
2. Build a `.spk` tarball (excludes `.jj/`, `target/`, etc.)
3. Compute SHA-256 checksum
4. Push to `ghcr.io/simple-lang/<name>:<version>`

### Yanking a Version

```bash
simple yank my-package 1.0.0          # Mark as yanked
simple yank my-package 1.0.0 --undo   # Undo yank
```

Yanked versions remain downloadable but are not selected by default.

### CI/CD Publishing

Tag a release to trigger the publish workflow:

```bash
jj bookmark set v1.0.0 -r @
jj git push --bookmark v1.0.0
```

---

## GitHub Registry Setup

### 1. Create the Registry Index Repository

```bash
gh repo create simple-lang/registry --public --description "Simple package registry index"
git clone https://github.com/simple-lang/registry.git && cd registry
mkdir -p index
git add . && git commit -m "Initial registry structure" && git push
```

### 2. Configure GHCR Access

1. Enable GitHub Packages in Organization Settings
2. Create a Personal Access Token with scopes: `read:packages`, `write:packages`, `repo`
3. Configure credentials:

```bash
# Option 1: Environment variable
export SIMPLE_TOKEN=ghp_your_token_here

# Option 2: Credentials file
mkdir -p ~/.simple
cat > ~/.simple/credentials.sdn << EOF
registry:
  token: ghp_your_token_here
  type: github_pat
EOF
chmod 600 ~/.simple/credentials.sdn
```

### 3. Set Up Repository Secrets

For each package repository: add `REGISTRY_TOKEN` secret in Repository Settings > Secrets and variables > Actions.

### 4. Test the Setup

```bash
oras login ghcr.io --username YOUR_USERNAME --password $SIMPLE_TOKEN
simple init test-pkg && cd test-pkg
simple publish --dry-run && simple publish
simple install test-pkg
```

---

## CI/CD Release Workflow

The release workflow (`.github/workflows/release.yml`) builds packages for all platforms automatically.

**Trigger:** Tag push (`git tag v0.5.0 && git push --tags`) or manual dispatch.

**Build matrix:**

| Platform | Target | Runner |
|----------|--------|--------|
| linux-x86_64 | x86_64-unknown-linux-gnu | ubuntu-latest |
| linux-aarch64 | aarch64-unknown-linux-gnu | ubuntu-latest (cross) |
| darwin-arm64 | aarch64-apple-darwin | macos-latest |
| darwin-x86_64 | x86_64-apple-darwin | macos-15 |
| windows-x86_64 | x86_64-pc-windows-msvc | windows-latest |
| windows-aarch64 | aarch64-pc-windows-msvc | windows-latest (cross) |

**Release artifacts** include platform-specific `.tar.gz` packages plus `.sha256` checksums.

### Verification

```bash
# Verify download checksum
sha256sum -c simple-bootstrap-0.5.0-linux-x86_64.tar.gz.sha256

# Verify no Rust files in package
tar -tzf simple-bootstrap-0.5.0-linux-x86_64.tar.gz | grep -E '\.(rs|toml)$'
# Should return nothing
```

---

## Distribution Configuration (simple.sdn)

```sdn
distribution:
  include:
    - bin/simple
    - lib/std/**/*.spl
    - src/**/*.spl
    - examples/**/*.spl

  exclude:
    - rust/**
    - build/**
    - test/**

  binaries:
    simple_runtime:
      platforms: [linux-x86_64, darwin-arm64, windows-x86_64]
      strip: true
      compress: upx

  formats:
    bootstrap:
      type: tar.gz
      includes: [bin, lib, examples]
    full:
      type: tar.gz
      includes: [bin, lib, src, examples, doc]
```

---

## Troubleshooting

| Issue | Solution |
|-------|----------|
| `GLIBC_2.XX not found` | Build on older Linux or use MUSL target |
| Cross-compilation linker not found | Install cross-compiler (gcc-aarch64-linux-gnu, mingw-w64) |
| UPX compression fails | Skip with `--no-compress` or update UPX |
| `Permission denied` | `chmod +x bin/simple` |
| Package not found | Check spelling, run `simple search <name>` |
| Checksum mismatch | Clear cache (`rm -rf ~/.simple/cache/registry`) and retry |
| `401 Unauthorized` (GHCR) | Check token scopes and expiration |
| `oras: command not found` | Install oras CLI |

---

## Related Files

- Package script: `scripts/package-dist.spl`
- Distribution config: `simple.sdn`
- Release workflow: `.github/workflows/release.yml`
- Publish workflow: `.github/workflows/publish.yml`
