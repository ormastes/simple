# Provider default factory native regression

Source: test/fixtures/compiler/provider_default_factory_native.spl.

Authored, UNEXECUTED. Seven fail-fast checks cover fresh empty warning/request defaults, independent instances, warning mutation isolation, defaults after mutation, and production MonomorphizationPass initial defaults. Required success marker: provider-default-factory: PASS 7 fail-fast cases. Exit zero alone is insufficient. This fixture does not claim the old producer workaround effective until the affected native build also completes.
