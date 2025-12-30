# Testing Framework Features (#180-#192)

BDD-style testing framework for Simple language.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #180 | [Describe Blocks](0180_describe_blocks.md) | 2 | Complete | Simple |
| #181 | [Context Blocks](0181_context_blocks.md) | 2 | Complete | Simple |
| #182 | [It Examples](0182_it_examples.md) | 2 | Complete | Simple |
| #183 | [Before Each](0183_before_each.md) | 2 | Complete | Simple |
| #184 | [After Each](0184_after_each.md) | 2 | Complete | Simple |
| #187 | [Expect Matchers](0187_expect_matchers.md) | 3 | Complete | Simple |
| #192 | [Doctest](0192_doctest.md) | 3 | Complete | Simple |

## Summary

**Status:** 7/7 Complete (100%)

## Test Locations

- **Simple Tests:** `simple/std_lib/test/features/testing_framework/`
- **Framework:** `simple/std_lib/src/spec/`

## Overview

The testing framework provides:
- **BDD DSL**: describe/context/it blocks
- **Hooks**: before_each/after_each for setup/teardown
- **Matchers**: Fluent expect().to assertions
- **Doctest**: Documentation testing from docstrings

Written in Simple, self-hosted testing framework.
