# suspension_operator_spec

*Source: `simple/std_lib/test/features/concurrency/suspension_operator_spec.spl`*

---

Suspension Operator (~) - Feature #45

Overview:
    The ~ operator marks explicit suspension points in async code. Includes ~=
    for suspending assignment, if~/while~/for~ for suspending guards, and
    ~+= for compound operations. Makes async control flow visible at the syntax level.

Syntax:
    val user ~= fetch_user(id)          # Suspending assignment
    _ ~= timer.sleep(100_ms)            # Discard result
    if~ is_ready():                     # Suspending guard
        proceed()
    while~ not done():                  # Suspending loop
        _ ~= timer.sleep(100_ms)
    counter ~+= fetch_increment()       # Compound suspension

Implementation:
    - Lexer/parser support for ~ operators
    - ~= awaits and assigns result
    - if~/while~/for~ allow suspending conditions
    - and~/or~ for suspending boolean operators
    - ~+=, ~-=, ~*=, ~/= for compound operations
    - Composes with ? operator for error propagation
    - Type inference handles awaited values

Notes:
    - Suspension operator makes async control flow visible at the syntax level
    - Composes with ? error propagation (e.g., val data ~= fetch()?)
    - Planned feature - not yet implemented
