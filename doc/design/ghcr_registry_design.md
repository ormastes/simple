# GHCR-Based Package Registry - Design Document

**Date:** 2026-02-01
**Status:** Design Phase
**Category:** Package Management / Infrastructure

---

## Executive Summary

A free, zero-infrastructure package registry for the Simple language using GitHub Container Registry (GHCR) for artifact storage, a GitHub repository for the package index, and GitHub Actions for CI/CD automation.

**Key metrics:**
- Cost: $0 for public packages (GHCR free tier)
- Index format: SDN (sparse protocol)
- Artifact format: `.spk` tarballs as OCI artifacts
- Auth: GitHub PAT tokens

---

## 1. Design Principles

### 1.1 Core Values
- **Zero cost**: Leverage GitHub free tier (GHCR unlimited public, Actions 2000 min/month)
- **Simple tooling**: Use `oras` CLI for OCI operations (single Go binary)
- **SDN native**: All config and index files use SDN format per project rules
- **Sparse index**: Only fetch metadata for packages you need (like Cargo sparse)
- **Security first**: Checksums for all artifacts, signed manifests

### 1.2 Non-Goals (v1.0)
- User-scoped packages (`@user/pkg`) - reserved for future
- Private package hosting
- Mirror/proxy registries
- Package signing with GPG keys (checksums only for v1.0)

---

## 2. Architecture Overview

### 2.1 Component Diagram

```
                         GitHub Infrastructure
                    ┌─────────────────────────────────┐
                    │                                   │
  simple publish ──►│  GHCR (ghcr.io/simple-lang/*)   │
                    │  └── OCI artifacts (.spk)         │
                    │                                   │
  simple install ◄──│  Index Repo                      │
       ▲            │  (github.com/simple-lang/registry)│
       │            │  └── index/{aa}/{bb}/{name}.sdn   │
       │            │                                   │
       │            │  GitHub Actions                   │
       │            │  └── CI/CD for publish + validate │
       │            └─────────────────────────────────┘
       │
  ~/.simple/credentials.sdn (GitHub PAT)
  ~/.simple/cache/registry/   (local index cache)
```

### 2.2 Data Flow

**Publish:**
1. `simple publish` reads `simple.sdn` manifest
2. Builds `.spk` tarball (source + metadata)
3. Computes SHA-256 checksum
4. Pushes to GHCR via `oras push ghcr.io/simple-lang/<name>:<version>`
5. Submits PR to index repo with new version entry
6. GitHub Actions validates and merges

**Install:**
1. `simple install <pkg>` fetches `index/{first2}/{next2}/{name}.sdn` from index repo
2. Resolves version constraint, gets OCI reference
3. Pulls artifact via `oras pull ghcr.io/simple-lang/<name>:<version>`
4. Verifies checksum
5. Extracts to `~/.simple/packages/<name>/<version>/`

**Search:**
1. `simple search <query>` fetches index listing (cached locally)
2. Filters by name/description match
3. Displays results with version info

---

## 3. Index Schema

### 3.1 Sparse Protocol

Index is organized as a sparse directory structure in the registry repo:

```
index/
  ht/
    tp/
      http.sdn
  js/
    on/
      json.sdn
  co/
    ll/
      collections.sdn
  _listing.sdn          # Full package name list for search
```

Path formula: `index/{name[0:2]}/{name[2:4]}/{name}.sdn`

For short names (< 4 chars): `index/{name[0:1]}/{name[1:2]}/{name}.sdn`
For single char: `index/_/{name}/{name}.sdn`

### 3.2 Package Index Entry (SDN)

```sdn
package:
  name: http
  description: HTTP client library for Simple
  homepage: https://github.com/simple-lang/http
  license: MIT
  repository: https://github.com/simple-lang/http

versions |version, checksum, oci_ref, yanked, published_at|
  1.0.0, sha256:abc123def456, ghcr.io/simple-lang/http:1.0.0, false, 2026-01-15T10:00:00Z
  1.1.0, sha256:def456abc789, ghcr.io/simple-lang/http:1.1.0, false, 2026-02-01T12:00:00Z

dependencies |version, name, constraint|
  1.0.0, json, ^1.0
  1.1.0, json, ^1.2
  1.1.0, url, ^0.5
```

### 3.3 Listing File (SDN)

```sdn
# Package listing for search
packages |name, description, latest_version|
  http, HTTP client library, 1.1.0
  json, JSON parser and serializer, 2.0.1
  collections, Extended collection types, 0.3.0
```

---

## 4. Authentication

### 4.1 Token Storage

Credentials stored in `~/.simple/credentials.sdn`:

```sdn
registry:
  token: ghp_xxxxxxxxxxxxxxxxxxxx
  type: github_pat
  created_at: 2026-02-01T10:00:00Z
```

### 4.2 Token Resolution Order

1. `SIMPLE_TOKEN` environment variable (CI/CD friendly)
2. `~/.simple/credentials.sdn` file
3. Interactive prompt (login flow)

### 4.3 Required Scopes

- `read:packages` - Pull public packages
- `write:packages` - Push packages to GHCR
- `repo` - Submit PRs to index repo (for publish)

---

## 5. Package Format (.spk)

A `.spk` file is a gzipped tarball containing:

```
package-name-1.0.0.spk
├── simple.sdn          # Package manifest
├── src/                # Source files
│   ├── main.spl
│   └── lib/
├── test/               # Test files (optional)
├── doc/                # Documentation (optional)
├── LICENSE
└── README.md
```

### 5.1 Exclusions

The following are excluded from `.spk` files:
- `.jj/`, `.git/` directories
- `target/`, `build/` directories
- `*.o`, `*.so`, `*.dylib` compiled artifacts
- `.env`, `credentials.sdn` sensitive files

---

## 6. CLI Commands

### 6.1 `simple publish`

```
Usage: simple publish [options]

Publish current package to the Simple registry.

Options:
  --dry-run         Show what would be published without uploading
  --token=TOKEN     Override auth token
  --registry=URL    Override registry URL (default: ghcr.io/simple-lang)
  --allow-dirty     Publish with uncommitted changes

Steps:
  1. Validate simple.sdn manifest
  2. Build .spk tarball
  3. Compute checksum
  4. Push to GHCR
  5. Update registry index
```

### 6.2 `simple search <query>`

```
Usage: simple search <query> [options]

Search the package registry.

Options:
  --limit=N         Max results (default: 20)
  --sort=FIELD      Sort by: name, downloads, updated (default: name)
```

### 6.3 `simple info <pkg>`

```
Usage: simple info <package> [options]

Show package metadata and available versions.

Options:
  --versions        Show all versions
  --json            Output as JSON
```

### 6.4 `simple yank <pkg> <version>`

```
Usage: simple yank <package> <version> [options]

Mark a version as yanked (not recommended for new installs).

Options:
  --undo            Undo a yank
  --token=TOKEN     Override auth token
```

### 6.5 Enhanced `simple install`

```
Usage: simple install [package] [options]

Install packages from registry or local manifest.

Without arguments: install all dependencies from simple.sdn
With package name: install specific package from registry

Options:
  --version=VER     Specific version constraint
  --save            Add to simple.sdn dependencies
  --registry=URL    Override registry URL
```

---

## 7. Security Model

### 7.1 Package Integrity
- SHA-256 checksums stored in index, verified on install
- OCI content-addressable storage provides additional integrity

### 7.2 Name Squatting Prevention
- Index repo PRs reviewed by maintainers (initially manual)
- Future: automated validation via GitHub Actions

### 7.3 Yank vs Delete
- Yanked versions remain downloadable but are not recommended
- True deletion requires manual intervention (GHCR admin)

---

## 8. Local Cache Structure

```
~/.simple/
├── credentials.sdn           # Auth tokens
├── cache/
│   └── registry/
│       ├── index/             # Cached index entries
│       │   └── ht/tp/http.sdn
│       └── packages/          # Downloaded .spk cache
│           └── http-1.1.0.spk
└── packages/                  # Installed packages
    └── http/
        └── 1.1.0/
            ├── simple.sdn
            └── src/
```

---

## 9. Error Handling

| Error | Message | Recovery |
|-------|---------|----------|
| No token | `error: not authenticated. Run 'simple login' or set SIMPLE_TOKEN` | Login or set env |
| Package exists | `error: version 1.0.0 already published for 'http'` | Bump version |
| Checksum mismatch | `error: checksum mismatch for 'http@1.0.0' (expected sha256:abc, got sha256:def)` | Re-download |
| Network error | `error: failed to reach registry (ghcr.io)` | Retry |
| Yanked version | `warning: 'http@1.0.0' is yanked, consider upgrading` | Use newer version |

---

## 10. Future Enhancements

- `@user/pkg` scoped packages
- Package signing (cosign/sigstore)
- Download statistics
- Automated security scanning
- Mirror support for air-gapped environments
- Private registry support
