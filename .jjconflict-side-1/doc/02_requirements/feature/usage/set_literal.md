# set literal
*Source:* `test/feature/usage/set_literal_spec.spl`

## Feature: Set Literals

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates empty set | pass |
| 2 | creates set from integer elements | pass |
| 3 | removes duplicates automatically | pass |
| 4 | creates set from string elements | pass |
| 5 | handles trailing comma | pass |
| 6 | supports single element | pass |
| 7 | creates set with mixed operations | pass |
| 8 | supports intersection | pass |
| 9 | supports difference | pass |
| 10 | converts to list | pass |
| 11 | supports filter | pass |
| 12 | supports map | pass |
| 13 | checks subset | pass |
| 14 | checks disjoint | pass |
| 15 | clones set | pass |

**Example:** creates empty set
    Given val empty = []  # Placeholder - use empty array for now

**Example:** creates set from integer elements
    Given val nums = [1, 2, 3]  # Placeholder - use array for now

**Example:** removes duplicates automatically
    Given val nums = [1, 2, 3]  # Placeholder - use array for now

**Example:** creates set from string elements
    Given val words = ["hello", "world"]  # Placeholder - use array for now

**Example:** handles trailing comma
    Given val nums = [1, 2, 3]  # Placeholder - use array for now

**Example:** supports single element
    Given val single = [42]  # Placeholder - use array for now

**Example:** creates set with mixed operations
    Given val a = [1, 2, 3]  # Placeholder - use array for now
    Given val b = [2, 3, 4]
    Given val union_set = a.union(b)

**Example:** supports intersection
    Given val a = [1, 2, 3]  # Placeholder - use array for now
    Given val b = [2, 3, 4]
    Given val common = a.intersect(b)

**Example:** supports difference
    Given val a = [1, 2, 3]  # Placeholder - use array for now
    Given val b = [2, 3, 4]
    Given val diff = a.diff(b)

**Example:** converts to list
    Given val nums = [3, 1, 2]  # Placeholder - use array for now
    Given val list = nums.to_list()

**Example:** supports filter
    Given val nums = [1, 2, 3, 4, 5]  # Placeholder - use array for now
    Given val evens = nums.filter(\x: x % 2 == 0)

**Example:** supports map
    Given val nums = [1, 2, 3]  # Placeholder - use array for now
    Given val doubled = nums.map(\x: x * 2)

**Example:** checks subset
    Given val small = [1, 2]  # Placeholder - use array for now
    Given val large = [1, 2, 3, 4]

**Example:** checks disjoint
    Given val a = [1, 2, 3]  # Placeholder - use array for now
    Given val b = [4, 5, 6]
    Given val c = [3, 4, 5]

**Example:** clones set
    Given val original = [1, 2, 3]  # Placeholder - use array for now
    Given val copy = original.clone()


