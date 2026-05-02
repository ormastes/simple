# tensor bridge
*Source:* `test/feature/usage/tensor_bridge_spec.spl`

## Feature: Tensor Bridge Batch Conversion

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | arrtens Vec3 list to array | pass |
| 2 | unarrtens array to Vec3 list | pass |
| 3 | round-trips Vec3 list | pass |

**Example:** arrtens Vec3 list to array
    Given val vecs = [
    Given val arr = math.vecs_to_tensor(vecs)
    Then  expect arr.len() == 6
    Then  expect arr[0] == 1.0
    Then  expect arr[1] == 2.0
    Then  expect arr[2] == 3.0
    Then  expect arr[3] == 4.0
    Then  expect arr[4] == 5.0
    Then  expect arr[5] == 6.0

**Example:** unarrtens array to Vec3 list
    Given val arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
    Given val vecs = math.tensor_to_vecs(arr)
    Then  expect vecs.len() == 2
    Then  expect vecs[0].x == 1.0
    Then  expect vecs[0].y == 2.0
    Then  expect vecs[0].z == 3.0
    Then  expect vecs[1].x == 4.0

**Example:** round-trips Vec3 list
    Given val original = [
    Given val arr = math.vecs_to_tensor(original)
    Given val restored = math.tensor_to_vecs(arr)
    Then  expect restored.len() == 2
    Then  expect restored[0].x == 10.0
    Then  expect restored[1].z == 60.0

## Feature: Tensor Bridge Vec3d Batch Conversion

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | arrtens Vec3d list to f64 array | pass |
| 2 | unarrtens f64 array to Vec3d list | pass |

**Example:** arrtens Vec3d list to f64 array
    Given val vecs = [
    Given val arr = math.vecs3d_to_tensor(vecs)
    Then  expect arr.len() == 6
    Then  expect arr[0] == 1.0

**Example:** unarrtens f64 array to Vec3d list
    Given val arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
    Given val vecs = math.tensor_to_vecs3d(arr)
    Then  expect vecs.len() == 2
    Then  expect vecs[0].x == 1.0


