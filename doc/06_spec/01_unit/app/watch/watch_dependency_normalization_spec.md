# Watch Dependency Normalization Specification

The executable specification at
`test/01_unit/app/watch/watch_dependency_normalization_spec.spl` pins the
allocation-hoist contract for the watch dependency lookup:

- slash and backslash paths normalize identically;
- `std`, `lib`, `app`, and `compiler` prefix handling is unchanged;
- repeated imports and multiple changed files retain graph order without
  duplicate dependents;
- the existing order-sensitive `dominated` behavior remains explicit.

Production `find_dependents` builds one normalized changed-path array before
the dependency/import loops. Matching still uses the exact historical prefix
and `contains` expressions. This reduces worst-case normalization work while
retaining the nested matcher and dependent-list dedupe; it does not claim an
end-to-end asymptotic improvement. Empty/no-import graphs may eagerly normalize
paths that the former lazy route never compared.

No test, build, benchmark, SPipe, or optimizer command was run for this tranche.
