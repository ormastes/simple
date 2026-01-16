# it_examples_spec

*Source: `simple/std_lib/test/features/testing_framework/it_examples_spec.spl`*

---

It Examples - Feature #182

Overview:
    BDD it blocks for defining individual test examples. Each it block represents
    a single test case with description and assertion block. Test examples are
    collected during definition phase and executed during run phase.

Syntax:
    it "adds two numbers":
        val result = 1 + 2
        expect(result).to eq(3)

    skip "not implemented yet":
        pass

Implementation:
    - it creates test case with description
    - Executes test body with assertion block
    - Supports descriptive names for clarity
    - skip marks tests as pending
    - Tracks test results (pass/fail/skip)
    - Multiple assertions per test allowed

Notes:
    - Test examples are collected during definition phase
    - Executed during run phase with proper hook execution
    - Supports pending/skipped tests
