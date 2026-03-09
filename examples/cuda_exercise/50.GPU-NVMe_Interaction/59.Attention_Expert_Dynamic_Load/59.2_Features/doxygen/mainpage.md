# Module 59.2 Feature Matrix

This documentation captures the feature capabilities of Module 59, grouped by
the architectural layers defined in Module 59.1. Each feature entry references
the originating layer and describes the support level.

Key APIs:
- `feature_matrix.h` — core data structures
- `feature_matrix.cpp` — builds the global matrix by querying 59.1
- `feature_formatter.cpp` — textual rendering helpers
- `feature_kernel.cu` — GPU bridge for metadata consumers
