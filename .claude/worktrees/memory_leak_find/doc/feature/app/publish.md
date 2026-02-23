# Registry Publish Specification
*Source:* `test/feature/app/publish_spec.spl`

## Overview



**Difficulty:** 3/5

## Overview
Tests for the `simple publish` command that builds .spk tarballs
and pushes them to GHCR.

## Key Concepts
- Package manifest validation
- .spk tarball creation
- Checksum computation
- GHCR push via oras

## Behavior

### Publish Command

## Package Publishing
    Tests for building and publishing packages to the GHCR registry.

### When when manifest is valid

### Scenario: Valid simple.sdn manifest

- parses package name from manifest
- parses package version from manifest

### When when manifest is missing

### Scenario: No manifest file

- returns error when no simple.sdn exists

### When when using --dry-run

### Scenario: Dry run mode

- does not push to GHCR in dry-run mode

### SPK Tarball

## Package Tarball Creation
    Tests for .spk file format and contents.

### When when building tarball

- excludes .jj directory
- excludes target directory
- excludes .env files
- includes simple.sdn manifest
- includes src directory

### Checksum

## SHA-256 Checksum
    Tests for package integrity verification.

- computes sha256 checksum with prefix


