# Registry Index Specification
*Source:* `test/feature/usage/index_spec.spl`
**Feature IDs:** #956-958  |  **Category:** Tooling  |  **Status:** In Progress

## Overview




## Overview
Tests for the sparse package index: parsing SDN entries,
computing index paths, and searching.

## Key Concepts
- SDN index entry parsing
- Sparse directory path computation
- Package listing and search

## Feature: Index Path Computation

## Sparse Index Paths
    Tests for computing the file path for a package in the sparse index.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | computes path for 4+ char names | pass |
| 2 | computes path for long names | pass |
| 3 | computes path for 3 char names | pass |
| 4 | computes path for 2 char names | pass |
| 5 | computes path for 1 char names | pass |

**Example:** computes path for 4+ char names
    Given val path = index_path_for("http")
    Then  expect(path).to_equal("ht/tp/http.sdn")

**Example:** computes path for long names
    Given val path = index_path_for("collections")
    Then  expect(path).to_equal("co/ll/collections.sdn")

**Example:** computes path for 3 char names
    Given val path = index_path_for("url")
    Then  expect(path).to_equal("ur/l/url.sdn")

**Example:** computes path for 2 char names
    Given val path = index_path_for("io")
    Then  expect(path).to_equal("i/o/io.sdn")

**Example:** computes path for 1 char names
    Given val path = index_path_for("x")
    Then  expect(path).to_equal("_/x/x.sdn")

## Feature: Index Entry Parsing

## SDN Index Entry Parser
    Tests for parsing package index entries from SDN format.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses package name | pass |
| 2 | parses package description | pass |
| 3 | parses version entries | pass |
| 4 | parses version checksum | pass |
| 5 | parses yanked flag | pass |
| 6 | parses dependencies | pass |
| 7 | parses dependency constraint | pass |

**Example:** parses package name
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.package.name).to_equal("http")

**Example:** parses package description
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.package.description).to_equal("HTTP client library")

**Example:** parses version entries
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.versions.len()).to_equal(2)

**Example:** parses version checksum
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.versions[0].checksum).to_equal("sha256:abc123")

**Example:** parses yanked flag
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.versions[0].yanked).to_equal(false)

**Example:** parses dependencies
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.dependencies.len()).to_equal(2)

**Example:** parses dependency constraint
    Given val entry = parse_index_entry(sample_entry())
    Then  expect(entry.dependencies[0].constraint).to_equal("^1.0")

## Feature: Index Queries

## Index Query Functions

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | finds latest non-yanked version | pass |
| 2 | finds dependencies for a version | pass |
| 3 | finds specific version entry | pass |
| 4 | returns empty for missing version | pass |

**Example:** finds latest non-yanked version
    Given val entry = parse_index_entry(sample_entry())
    Given val latest = latest_version(entry)
    Then  expect(latest).to_equal("1.1.0")

**Example:** finds dependencies for a version
    Given val entry = parse_index_entry(sample_entry())
    Given val deps = deps_for_version(entry, "1.1.0")
    Then  expect(deps.len()).to_equal(1)

**Example:** finds specific version entry
    Given val entry = parse_index_entry(sample_entry())
    Given val ver = find_version(entry, "1.0.0")
    Then  expect(ver.version).to_equal("1.0.0")

**Example:** returns empty for missing version
    Given val entry = parse_index_entry(sample_entry())
    Given val ver = find_version(entry, "9.9.9")
    Then  expect(ver.version).to_equal("")
    Given val len = name.len()
    Given val lines = content.split("{NL}")
    Given var name = ""
    Given var description = ""
    Given var homepage = ""
    Given var license = ""
    Given var repository = ""
    Given var versions = []
    Given var deps = []
    Given var section = ""
    Given val trimmed = line.trim()
    Given val parts = trimmed.split(",")
    Given val parts = trimmed.split(",")
    Given var latest = ""
    Given var result = []


