# vhdl golden
*Source:* `test/feature/usage/vhdl_golden_spec.spl`

## Overview

## Golden File Regression

    Compares builder output against reference .vhd files.
    If these fail, either the builder changed (update golden) or a regression.

## Feature: VHDL Golden File Tests

## Golden File Regression

    Compares builder output against reference .vhd files.
    If these fail, either the builder changed (update golden) or a regression.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | counter matches golden reference | pass |
| 2 | ALU matches golden reference | pass |
| 3 | golden files exist on disk | pass |

**Example:** counter matches golden reference
    Given val generated = normalize(build_counter())
    Given val golden_file = golden_path("counter")
    Given val golden_content = vhdl_read_file(golden_file)
    Given val expected = normalize(golden_content.unwrap())
    Then  expect(generated).to_equal(expected)

**Example:** ALU matches golden reference
    Given val generated = normalize(build_alu())
    Given val golden_file = golden_path("alu")
    Given val golden_content = vhdl_read_file(golden_file)
    Given val expected = normalize(golden_content.unwrap())
    Then  expect(generated).to_equal(expected)

## Feature: VHDL Golden Output Sanity

## Output Sanity Checks

    Verify generated VHDL has correct structural elements.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | counter output has required VHDL structure | pass |
| 2 | ALU output has required VHDL structure | pass |

**Example:** counter output has required VHDL structure
    Given val vhdl = build_counter()

**Example:** ALU output has required VHDL structure
    Given val vhdl = build_alu()


