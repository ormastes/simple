# each_method_spec

*Source: `simple/std_lib/test/features/stdlib/each_method_spec.spl`*

---

Each Method - Feature #1005

Overview:
    Ruby-style each() method for collections and strings. Provides a convenient
    way to iterate over elements with a closure, replacing the deprecated iter()
    method. The preferred way to iterate over collections in Simple.

Syntax:
    val list = [1, 2, 3, 4, 5]
    list.each(|x| print(x))

    "hello".each(|c| print(c))

    list.each_with_index(|i, x| print("{i}: {x}"))

Implementation:
    - each() method on List, String, and Slice
    - Iterates over all elements in order
    - each_with_index() provides 0-based index
    - Handles empty collections (no-op)
    - Handles single element collections
    - Can modify external state via closure
    - String iteration over characters
    - chars() method deprecated in favor of each()

Notes:
    - The each() method is the preferred way to iterate over collections
    - iter() is deprecated and will be removed in a future version
    - More expressive than traditional for loops
