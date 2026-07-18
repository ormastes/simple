# Low Dependency UI dynSMF NFR Requirements TLDR

- Selected: NFR-A+B.
- Static dependency gates must be deterministic and ignore external/vendor code.
- dynSMF runtime evidence must cover load, skip, unload, stale lookup, and reload.
- Tests must avoid process-global env mutation.
- Existing dynlib close/refcount behavior must stay compatible.

```sdn
nfr {
  static_dependency_gate
  runtime_dynsmf_evidence
  clean_doc06_layout
}
```
