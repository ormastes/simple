# Stage4 selected archive projection

Mirror of `test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl`.

The executable SSpec checks requested closure roots, localization of other definitions, Mach-O raw-name preservation, exact projected ABI admission, rejection of invalid roots/formats/dependencies/globals, and cycle-safe one-member capsule wiring before strict linking.

This provides static archive-projection contract evidence, not cross-platform execution evidence.
