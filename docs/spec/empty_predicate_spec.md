# empty_predicate_spec

*Source: `simple/std_lib/test/features/stdlib/empty_predicate_spec.spl`*

---

Empty Predicate - Feature #1001

Overview:
    Ruby-style empty? predicate method for collections and strings. Provides
    a convenient way to check if a collection has no elements. The empty?()
    method is a Ruby-style alias for is_empty() with both methods available.

Syntax:
    val empty_list: List<i64> = []
    empty_list.empty?()  # true

    "".empty?()          # true
    "hello".empty?()     # false

Implementation:
    - empty?() method on List, String, and Slice types
    - Returns true for empty collections
    - Returns false for non-empty collections
    - Equivalent to is_empty() method
    - Works after clear() or pop() operations
    - String whitespace is not considered empty (has bytes)

Notes:
    - The empty?() method is a Ruby-style alias for is_empty()
    - Both methods are available for compatibility
    - Provides more expressive code than len() == 0
