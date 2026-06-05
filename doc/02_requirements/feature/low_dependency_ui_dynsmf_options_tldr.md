# Low Dependency UI dynSMF Feature Options TLDR

- Option A: boundary-first UI refactor, medium effort.
- Option B: dynSMF loader first, medium-high effort.
- Option C: thin vertical slice, high effort, recommended.
- Option D: full parallel migration, very high effort.
- Final requirements are pending user selection.

```sdn
options {
  A -> ui_boundaries
  B -> dynsmf_loader
  C -> vertical_slice recommended
  D -> full_migration
}
```
