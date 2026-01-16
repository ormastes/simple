# expect_matchers_spec

*Source: `simple/std_lib/test/features/testing_framework/expect_matchers_spec.spl`*

---

Expect Matchers - Feature #187

Overview:
    BDD expect/to assertion DSL with composable matchers. Provides readable
    assertions with clear failure messages. Supports equality, comparison,
    string, collection matchers, and negation.

Syntax:
    expect(result).to eq(42)                # Equality
    expect(name).to start_with("Hello")     # String matcher
    expect(list).to have_length(3)          # Collection matcher
    expect(value).not_to be_nil             # Negation

Implementation:
    - expect() creates expectation wrapper
    - to applies positive matcher
    - not_to applies negated matcher
    - Matchers:
      - Equality: eq, be
      - Comparison: be_gt, be_lt, be_gte, be_lte
      - String: include, start_with, end_with
      - Collection: have_length, be_empty
    - Clear failure messages with context

Notes:
    - Supports eq, be, be_gt, be_lt, include, start_with, end_with,
      have_length, and negation with not_to
    - Composable matcher system
    - Clear error messages on failure
