# generators_spec

*Source: `simple/std_lib/test/features/concurrency/generators_spec.spl`*

---

Generators - Feature #42

Overview:
    Generators for lazy value production using yield. Supports single and multiple
    yields, state preservation across yields, captured variables, and collection
    of all values. Uses state machine lowering in MIR for efficient execution.

Syntax:
    val gen = generator(\: yield 42)            # Create generator
    val value = next(gen)                       # Get next value
    val gen = generator(\: [yield 1, yield 2])  # Multiple yields
    val arr = collect(gen)                      # Collect all values

Implementation:
    - generator() creates generator from lambda with yield
    - yield produces single value and suspends
    - next() resumes generator and returns next value
    - Returns nil when exhausted
    - State machine lowering in MIR
    - Preserves state across yields
    - Captures variables from outer scope
    - collect() drains generator into array

Notes:
    - Generators use state machine lowering in MIR
    - Yield has low precedence - use parentheses for expressions
    - State is preserved across yields
    - Can capture variables from outer scope
