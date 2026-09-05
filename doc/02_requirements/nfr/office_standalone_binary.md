# Standalone Office Binary NFRs

- NFR-001: The deployed host executable shall contain only the selected entry's
  import closure and exclude Office GUI/GPU/browser modules.
- NFR-002: The terminal frame shall be exactly 124 columns by 37 lines and expose
  columns A–T and rows 1–30.
- NFR-003: Application startup shall use a cached native artifact; bootstrap is
  a build/release concern only.
- NFR-004: Terminal mode shall be restored on normal exit and failure shall be
  reported rather than silently accepted.
- NFR-005: Cross-target builds shall fail closed on missing runtime ABI symbols;
  a host artifact shall never be relabeled as a SimpleOS artifact.
