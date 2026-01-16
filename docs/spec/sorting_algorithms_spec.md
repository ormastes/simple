# sorting_algorithms_spec

*Source: `simple/std_lib/test/features/stdlib/sorting_algorithms_spec.spl`*

---

Configurable Sorting Algorithms - Feature #1002

Overview:
    Configurable sorting algorithms allowing users to choose between
    InsertionSort, PDQSort, TimSort, and HeapSort based on their specific
    needs. PDQSort is the default for general-purpose sorting.

Syntax:
    list.sort()                              # Default (PDQSort)
    list.sort_with(SortAlgorithm::TimSort)   # Specific algorithm
    SortAlgorithm::TimSort.is_stable()       # Check stability

Implementation:
    - SortAlgorithm enum with 4 variants:
      - InsertionSort: stable, for small arrays
      - PDQSort: unstable, fast general-purpose (default)
      - TimSort: stable, for nearly-sorted data
      - HeapSort: unstable, guaranteed O(n log n)
    - is_stable() method to check stability
    - sort() uses PDQSort by default
    - sort_with() accepts algorithm parameter
    - Handles all edge cases: empty, single, sorted, reverse

Notes:
    - PDQSort is the default algorithm
    - TimSort is recommended for nearly-sorted data
    - InsertionSort is used internally for small arrays
    - All algorithms handle duplicates correctly
