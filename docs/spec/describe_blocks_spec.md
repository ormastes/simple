# describe_blocks_spec

*Source: `simple/std_lib/test/features/testing_framework/describe_blocks_spec.spl`*

---

Describe Blocks - Feature #180

Overview:
    BDD describe blocks for grouping related test examples. Creates example
    groups with descriptions that organize tests hierarchically. Supports
    nesting with context blocks and registers with global test registry.

Syntax:
    describe "Calculator":
        it "adds numbers":
            expect(1 + 1).to eq(2)

        it "subtracts numbers":
            expect(5 - 3).to eq(2)

Implementation:
    - describe creates test group with description
    - Executes definition block to collect examples
    - Supports nested context blocks for sub-grouping
    - Maintains hierarchical structure (Parent > Child)
    - Registers groups with global test registry
    - Preserves example execution order

Notes:
    - Top-level grouping construct
    - Supports nested context blocks
    - Registers with global test registry
    - Provides descriptive organization for tests
