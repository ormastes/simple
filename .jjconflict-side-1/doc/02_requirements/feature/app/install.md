# Registry Install Specification
*Source:* `test/feature/app/install_spec.spl`

## Overview


**Difficulty:** 3/5

## Overview
Tests for installing packages from the GHCR-based registry.

## Key Concepts
- Index lookup and version resolution
- OCI artifact pull
- Checksum verification
- Local package extraction

## Behavior

### Install from Registry

## Package Installation
    Tests for downloading and installing packages from GHCR.

### When when package exists

### Scenario: Package found in index

- resolves latest non-yanked version
- pulls artifact from GHCR
- verifies checksum after download
- extracts to packages directory

### When when package not found

### Scenario: Package not in index

- shows error message

### When when version is yanked

### Scenario: Requested version is yanked

- shows warning for yanked version
- selects next available version

### When when using --save flag

- adds package to simple.sdn dependencies

### Version Resolution

## Version Constraint Resolution

- selects latest version when no constraint
- respects caret constraint
- respects exact version constraint


