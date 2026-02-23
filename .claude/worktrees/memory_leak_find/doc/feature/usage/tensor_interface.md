# Tensor Interface Consistency Specification
*Source:* `test/feature/usage/tensor_interface_spec.spl`
**Feature IDs:** #1920, #1930  |  **Category:** ML, Collections, API  |  **Status:** Complete

## Overview




Tests that tensor interfaces are consistent between core and torch.
Verifies that basic tensor operations work the same way regardless
of the underlying implementation.

## Feature: Tensor Interface Consistency

Tests that tensor operations have consistent interfaces
    across different implementations.

### Scenario: tensor creation

### Scenario: Creating Tensors

        Tests various tensor creation methods with consistent syntax.

| # | Example | Status |
|---|---------|--------|
| 1 | creates tensor from array | pass |
| 2 | creates tensor with explicit shape | pass |
| 3 | creates zero tensor | pass |
| 4 | creates ones tensor | pass |

**Example:** creates tensor from array
    Given val data = [1.0, 2.0, 3.0, 4.0]
    Given val t = torch.tensor(data)
    Then  expect t.shape() == [4]

**Example:** creates tensor with explicit shape
    Given val data = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
    Given val t = torch.tensor(data).reshape([2, 3])
    Then  expect t.shape() == [2, 3]

**Example:** creates zero tensor
    Given val t = torch.zeros([3, 4])
    Then  expect t.shape() == [3, 4]

**Example:** creates ones tensor
    Given val t = torch.ones([2, 5])
    Then  expect t.shape() == [2, 5]

### Scenario: tensor indexing

### Scenario: Tensor Indexing

        Tests that indexing works consistently (including negative indices).

| # | Example | Status |
|---|---------|--------|
| 1 | accesses elements by index | pass |
| 2 | supports negative indexing | pass |
| 3 | slices tensors | pass |

**Example:** accesses elements by index
    Given val data = [10.0, 20.0, 30.0, 40.0, 50.0]
    Given val t = torch.tensor(data)
    Then  expect t[0] == 10.0
    Then  expect t[2] == 30.0

**Example:** supports negative indexing
    Given val data = [10.0, 20.0, 30.0, 40.0, 50.0]
    Given val t = torch.tensor(data)
    Then  expect t[-1] == 50.0
    Then  expect t[-2] == 40.0

**Example:** slices tensors
    Given val data = [1.0, 2.0, 3.0, 4.0, 5.0]
    Given val t = torch.tensor(data)
    Given val sliced = t[1:4]
    Then  expect sliced.shape() == [3]

### Scenario: tensor operations

### Scenario: Tensor Operations

        Tests mathematical operations on tensors.

| # | Example | Status |
|---|---------|--------|
| 1 | performs element-wise addition | pass |
| 2 | performs element-wise multiplication | pass |
| 3 | performs matrix multiplication with @ | pass |

**Example:** performs element-wise addition
    Given val a = torch.tensor([1.0, 2.0, 3.0])
    Given val b = torch.tensor([4.0, 5.0, 6.0])
    Given val c = a + b
    Then  expect c.shape() == [3]

**Example:** performs element-wise multiplication
    Given val a = torch.tensor([2.0, 3.0, 4.0])
    Given val b = torch.tensor([5.0, 6.0, 7.0])
    Given val c = a * b
    Then  expect c.shape() == [3]

**Example:** performs matrix multiplication with @
    Given val a = torch.tensor([[1.0, 2.0], [3.0, 4.0]])
    Given val b = torch.tensor([[5.0, 6.0], [7.0, 8.0]])
    Given val c = a @ b
    Then  expect c.shape() == [2, 2]

### Scenario: tensor properties

### Scenario: Tensor Properties

        Tests accessing tensor metadata and properties.

| # | Example | Status |
|---|---------|--------|
| 1 | gets tensor shape | pass |
| 2 | gets tensor dimension count | pass |
| 3 | gets tensor element count | pass |
| 4 | gets tensor dtype | pass |
| 5 | gets tensor device | pass |

**Example:** gets tensor shape
    Given val t = torch.zeros([3, 4, 5])
    Then  expect t.shape() == [3, 4, 5]

**Example:** gets tensor dimension count
    Given val t = torch.zeros([2, 3, 4])
    Then  expect t.ndim() == 3

**Example:** gets tensor element count
    Given val t = torch.zeros([2, 3, 4])
    Then  expect t.numel() == 24

**Example:** gets tensor dtype
    Given val t = torch.zeros([2, 3])
    Then  expect t.dtype() == DType.Float32

**Example:** gets tensor device
    Given val t = torch.zeros([2, 3])
    Then  expect t.device() == Device.CPU

### Scenario: tensor reshaping

### Scenario: Tensor Reshaping

        Tests shape manipulation operations.

| # | Example | Status |
|---|---------|--------|
| 1 | reshapes tensor | pass |
| 2 | flattens tensor | pass |
| 3 | transposes 2D tensor | pass |

**Example:** reshapes tensor
    Given val t = torch.zeros([6])
    Given val reshaped = t.reshape([2, 3])
    Then  expect reshaped.shape() == [2, 3]

**Example:** flattens tensor
    Given val t = torch.zeros([2, 3, 4])
    Given val flattened = t.flatten()
    Then  expect flattened.shape() == [24]

**Example:** transposes 2D tensor
    Given val t = torch.zeros([3, 4])
    Given val transposed = t.t()
    Then  expect transposed.shape() == [4, 3]

### Scenario: tensor with dict config

### Scenario: Creating Tensors with Dict Config

        Tests that dict syntax works for tensor configuration.

| # | Example | Status |
|---|---------|--------|
| 1 | creates tensor with device config | pass |
| 2 | creates tensor metadata dict | pass |
| 3 | stores tensor info in dict | pass |

**Example:** creates tensor with device config
    Given val config = {
    Then  expect config["device"] == "cpu"

**Example:** creates tensor metadata dict
    Given val metadata = {
    Then  expect metadata["name"] == "input_tensor"
    Then  expect metadata["channels"] == 3

**Example:** stores tensor info in dict
    Given val t = torch.zeros([2, 3])
    Given val info = {
    Then  expect info["numel"] == 6


