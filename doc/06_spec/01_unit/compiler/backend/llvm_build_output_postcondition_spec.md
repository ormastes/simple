# LLVM build output postcondition

Authored, unexecuted adapter tests; no compiler or build is invoked.

The production result adapter rejects injected driver success without the
requested output, retains path and elapsed time for an existing output, and
preserves driver failure even when that path exists. The existing path is the
tracked spec itself; the missing path is a child beneath that regular file.
These fixtures establish filesystem preconditions explicitly. They do not
represent executable artifacts, successful compilation, fresh output provenance,
or linker admission evidence.
