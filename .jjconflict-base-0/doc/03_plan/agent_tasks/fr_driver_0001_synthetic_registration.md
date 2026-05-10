# FR-DRIVER-0001 Synthetic Static Registration

Status: partial.

Completed:
- Compiler metadata path exists through attribute parsing, HIR, MIR, and AOT SMF `.drv_manifest` bytes.
- Added `plan_synthetic_driver_registration` to classify whether static registration synthesis can be emitted.
- Added unit coverage for handwritten registration detection and the two precise blocked cases.

Remaining acceptance box:
- Emit executable synthetic logic equivalent to:
  `register_static_driver(DriverManifest.for_driver(...), ops)`.

Blocker:
- `@driver(...)` and `@native_lib(...)` currently provide only manifest fields. They do not identify the `DriverOps` value, the driver entry-point functions, or the native-lib adapter functions needed to build `DriverOps`.

Lowest-risk next design:
- Extend the attribute contract with an explicit ops binding, for example `ops = my_driver_ops`, or an impl-derived rule that maps a `Driver` implementation to `DriverOps`.
- Lower after HIR resolution, where the ops symbol and `register_static_driver` symbol can be validated before MIR construction.
- Keep AOT SMF manifest emission unchanged; it already consumes the same manifest metadata.
