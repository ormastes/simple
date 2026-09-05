# Visibility Model Reference

## Recommendation

Use tree-private as the base rule.

Use extracted common nodes and documented facades for sibling access.

Do not add new grammar for sibling-private unless the language later needs compile-time enforcement stronger than module manifests and re-export control.

## Reasoning

- Tree-private is simple and matches common module systems.
- Sibling-private usually becomes a friend model.
- Friend models are useful, but they increase rule complexity and are easy to abuse.
- This repo already prefers one shared frontend contract and narrow shared abstractions in `common`.

## Practical Rule Set

- Private subtree: visible only inside the subtree.
- Parent-public: visible to the parent facade.
- Next-layer-public: visible through an explicit facade for the immediately consuming layer.
- Common node: moved to shared layer when two siblings need it.

## External Design References

- Rust official visibility model is tree/module based, not sibling-friend by default.
- Ada private child packages show a stricter friend-like extension mechanism.
- C# `InternalsVisibleTo` shows friend access can exist, but should be explicit and narrow.

## Decision For Simple

- Grammar change needed now: no.
- Documentation change needed now: yes.
- Refactor needed now: yes, extract duplicated shared nodes into `common`.
