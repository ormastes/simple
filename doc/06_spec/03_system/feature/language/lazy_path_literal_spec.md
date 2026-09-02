# Lazy path literal language surface

Executable source: `test/03_system/feature/language/lazy_path_literal_spec.spl`.

The acceptance scenarios require a newly built pure-Simple compiler. They prove
that `_path` lowers to an inert `LazyPathTemplate`, that environment access is
deferred until resolution, and that a parameter or declaration expecting the
strong path-template type accepts the suffixed literal. Unsuffixed `text` stays
`text`; callers must apply `_path` rather than receiving a silent runtime cast.
