# Low Dependency UI dynSMF Domain Research TLDR

- Qt plugin loading supports metadata, load, and unload with shared-library
  lifetime constraints.
- Qt Quick Loader and web lazy loading show component-level delayed loading.
- GTK CSS providers show styling as an attachable provider, not a base widget
  dependency.
- POSIX/Windows dynamic loading models require handle validity rules after
  unload.

```sdn
domain_patterns {
  metadata_before_load
  lazy_component_load
  scoped_css_provider
  handle_scoped_unload
}
```
