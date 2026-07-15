# Font Asset Manifest Specification

> Manually synchronized on 2026-07-12 because executable Simple/docgen attempts
> were already exhausted for this session.

Eight scenarios cover the pinned CLDR ranking, sixteen immutable free-font
assets, all ten categories, the complete 10×10 sparse policy matrix, and exact
policy lookup. The resolver returns `en/sans` as `native`, `zh/display` as
`not-designed-for-script`, and `nil` for unknown language or category axes.
No scenario promotes a cell or treats witness metadata as a loadable face.

Source: `test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl`
