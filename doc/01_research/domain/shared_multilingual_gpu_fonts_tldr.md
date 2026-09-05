# Shared Multilingual GPU Fonts — Domain Research TLDR

> Historical pre-selection snapshot. Current selected state and evidence limits
> are authoritative in `doc/02_requirements/feature/shared_multilingual_gpu_fonts.md`
> and `doc/07_guide/lib/shared_multilingual_gpu_fonts.md`.

- L2 is the only currently verified reproducible ranking: pin CLDR 48.2 and
  deterministically derive “CLDR literate-functional reach.”
- Noto OFL script families are the safest multilingual base.
- A pinned 16-file Google Fonts candidate catalog exists, but no binary is
  accepted until selection and checksum/table/coverage verification.
- The proposed ten kinds are product coverage categories, not a popularity ranking; they cannot honestly form a complete 10×10 language matrix.
- CPU shaping should feed one atlas contract shared by 2D and 3D; F1 is alpha
  only, while color requires an explicitly selected supported font format.
- Noto Color Emoji uses CBDT/CBLC, so it is not an F1 outline-alpha witness.
- F1 can reuse unchanged variable `glyf` default instances; non-default axes
  fail closed, avoiding a subsetting/instantiation pipeline.
- Alpha atlas is the smallest path; hybrid MSDF and direct outline GPU raster remain larger options.
- Emitted GPU source is not device execution; compiled entry, submit, sync, readback, and present are separate gates.
