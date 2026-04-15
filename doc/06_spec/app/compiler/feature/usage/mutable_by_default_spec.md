# Mutable Collections by Default

Simple follows the design decision that collections (arrays and dicts) are mutable by default, consistent with Python, JavaScript, and Java. Variables declared with `var` can freely `push`, `pop`, `insert`, `remove`, `clear`, and use index assignment on arrays and dicts without any special annotation. Even `val` bindings to collections allow mutation of the collection contents (the binding is immutable, not the data). This spec comprehensively validates all mutation operations on arrays and dicts, sequential borrow patterns (read after write), and edge cases like empty collections.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-024 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/mutable_by_default_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Simple follows the design decision that collections (arrays and dicts) are mutable by
default, consistent with Python, JavaScript, and Java. Variables declared with `var`
can freely `push`, `pop`, `insert`, `remove`, `clear`, and use index assignment on
arrays and dicts without any special annotation. Even `val` bindings to collections
allow mutation of the collection contents (the binding is immutable, not the data).
This spec comprehensively validates all mutation operations on arrays and dicts,
sequential borrow patterns (read after write), and edge cases like empty collections.

## Syntax

```simple
var arr = [1, 2, 3]
arr.push(4)                # append element
arr.pop()                  # remove and return last
arr.insert(1, 2)           # insert at index
arr.remove(0)              # remove at index
arr[1] = 10                # index assignment
arr.clear()                # remove all elements

var dict = {"a": 1}
dict["b"] = 2              # add new key
dict["a"] = 10             # update existing key
dict.remove("a")           # remove key
dict.clear()               # remove all entries
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Mutable by default | Arrays and dicts support mutation without explicit mutability annotations |
| `var` vs `val` binding | `var` allows rebinding; `val` prevents rebinding but both allow collection mutation |
| Array mutations | `push`, `pop`, `insert`, `remove`, `clear`, and index assignment |
| Dict mutations | Key assignment (`dict[k] = v`), `remove`, and `clear` |
| Sequential borrows | Reading after writing (e.g., `arr.push(4)` then `arr[3]`) works correctly |
| Empty collection edge cases | Pushing to `[]`, popping from `[1]`, inserting into `{}` all behave correctly |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/mutable_by_default/result.json` |

## Scenarios

- allows push on default arrays
- allows pop on default arrays
- allows multiple pops
- allows insert on default arrays
- allows insert at beginning
- allows insert at end
- allows remove on default arrays
- allows remove first element
- allows remove last element
- allows clear on default arrays
- allows indexing assignment
- allows indexing assignment at boundaries
- allows insert on default dicts
- allows update existing key
- allows remove on default dicts
- allows clear on default dicts
- allows mutation with var binding
- allows pop with var binding
- works with dict and val binding
- handles sequential borrows
- allows read after write
- allows push to empty array
- handles pop from singleton
- allows insert into empty dict
