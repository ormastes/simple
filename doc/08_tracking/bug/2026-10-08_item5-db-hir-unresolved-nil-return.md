# Item 5 DB HIR failure: invalid unit return annotation

The retained DB application build failed during HIR lowering because
`_select_cache_store_v1` declared `-> nil`. `nil` is a value, not the unit
return type; nearby project declarations spell unit as `-> ()`. The helper
only updates the SELECT cache and its call sites ignore a return value, so the
source annotation is corrected to `-> ()`.

Evidence is from
`D:/dev/simple/build/item5-scalar-apps-20261008/source-fixed-db/build.log`
(compiler/source snapshot under
`/var/tmp/simple-item5-db-signature-fix-20261008`). Its HIR diagnostics are:

```text
[hir-fatal] source_idx=4 .../_PureDatabase/pure_database.spl error_idx=0 ...: unresolved type: nil
[hir-fatal-count] source_idx=4 .../_PureDatabase/pure_database.spl count=2 shown=2
[hir-fatal] source_idx=1 .../pure_sql/database.spl error_idx=0 ...: unresolved type: nil
[hir-fatal] source_idx=0 .../pure_database_scalar_query.spl error_idx=0 ...: unresolved type: nil
```

The facade and fixture diagnostics are downstream of the library module's
failed HIR registration. This source-only correction has not been compiled or
run. The full DB build was not repeated; three attempts for this fixture lane
have already been consumed.
