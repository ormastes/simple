# Registry Search Specification
*Source:* `test/feature/app/search_spec.spl`

## Overview



**Difficulty:** 2/5

## Overview
Tests for the `simple search` command that queries the package listing.

## Key Concepts
- Package listing parsing
- Name and description matching
- Result limiting

## Behavior

## Package Search
    Tests for searching the registry by name or description.

### When when packages match

- finds packages by name
- finds packages by description
- is case insensitive

### When when no packages match

- returns empty list

### When when limit is applied

- respects result limit


