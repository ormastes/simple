# Font Render Configuration Contract

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/lib/common/text_layout/font_render_config_spec.spl`
**Requirement:** REQ-015

Five module-level unit scenarios cover the canonical `FontRenderConfig`
contract:

1. Build a length-delimited identity from every field, including the
   `pixel/bitmap` category alias.
2. Order `Suggested`, `Preferred`, and `Required` backend attempts exactly.
3. Canonicalize the `hip` target alias to the `rocm` execution identity.
4. Reject unsupported targets, policies, and rendering modes.
5. Stamp configured text, advance, selected-run, and shaped-run batches while
   invalid or unavailable calls leave renderer cache state unchanged.

The executable assertions are authoritative. This unit scope proves
configuration, selection, and mutation guards; it makes no native-device or
device-origin pixel claim. Regenerate this manual with SPipe docgen when the
pure-Simple runner is available and require zero stubs.
