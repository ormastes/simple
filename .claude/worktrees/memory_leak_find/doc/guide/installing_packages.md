# Installing Packages

How to install Simple packages from the GHCR-based registry.

---

## Quick Start

```bash
# Install a specific package
simple install http

# Install all dependencies from simple.sdn
simple install
```

---

## Installing a Package

```bash
simple install <package-name>
```

This will:
1. Fetch the package index entry
2. Resolve the latest non-yanked version
3. Pull the `.spk` artifact from GHCR
4. Verify the SHA-256 checksum
5. Extract to `~/.simple/packages/<name>/<version>/`

## Version Constraints

```bash
simple install http --version="^1.0"    # Compatible with 1.x
simple install http --version="=1.2.3"  # Exact version
```

## Adding to Dependencies

To also add the package to your `simple.sdn`:

```bash
simple install http --save
```

## Authentication

Public packages don't require authentication. For private packages (future):

```bash
export SIMPLE_TOKEN=ghp_your_token
simple install private-pkg
```

## Cache

Downloaded packages are cached in `~/.simple/cache/registry/packages/`. To clear:

```bash
rm -rf ~/.simple/cache/registry
```

## Installed Package Locations

```
~/.simple/packages/
  http/
    1.1.0/
      simple.sdn
      src/
      ...
  json/
    2.0.1/
      ...
```

## Troubleshooting

| Issue | Solution |
|-------|----------|
| Package not found | Check spelling, run `simple search <name>` |
| Checksum mismatch | Clear cache and retry |
| Network error | Check internet, verify `ghcr.io` is reachable |
| Version yanked | Use `--version` to pick a specific non-yanked version |
