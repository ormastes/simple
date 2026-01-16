# integer_iteration_spec

*Source: `simple/std_lib/test/features/stdlib/integer_iteration_spec.spl`*

---

Integer Iteration Methods - Feature #1004

Overview:
    Ruby-style integer iteration methods: times(), upto(), and downto().
    These methods provide convenient ways to iterate over ranges of integers
    with a more expressive alternative to traditional for loops.

Syntax:
    5.times(|i| print(i))           # 0, 1, 2, 3, 4
    1.upto(5, |i| print(i))         # 1, 2, 3, 4, 5
    5.downto(1, |i| print(i))       # 5, 4, 3, 2, 1

Implementation:
    - times(n): executes closure n times with index 0 to n-1
    - upto(end): iterates from start to end inclusive
    - downto(end): iterates from start down to end inclusive
    - All methods provide index to closure
    - Handle edge cases: zero, negative, start==end, start>end
    - Support negative ranges
    - No-op when conditions not met

Notes:
    - These methods are inspired by Ruby's Integer class
    - They provide a more expressive alternative to traditional for loops
    - times() starts at 0, upto/downto are inclusive of both ends
