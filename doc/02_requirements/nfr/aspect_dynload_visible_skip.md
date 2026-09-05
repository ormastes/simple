# Aspect dynload visible partial-success NFR

- **NFR-ASPECT-DYNLOAD-VISIBLE-001:** Decision cost is O(1), with no source-tree
  scan, file read, cache lookup, or additional artifact copy.
- The zero-notice paths allocate no diagnostic text. An incomplete successful
  dynload build performs at most one diagnostic construction and one stderr
  write.
- The warning must execute only after output publication and launch-metadata
  success, so it never describes a failed or unpublished artifact as usable.
