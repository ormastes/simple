# Stage4 contract provider

Mirror of `test/01_unit/compiler/backend/stage4_contracts_provider_spec.spl`.

The executable SSpec verifies the exact cross-platform contract ABI, selection of its dedicated owner and runtime-native dependencies, and the inventory, projection, and cleanup flow for the sole contract object.

It checks build/provider contracts statically and does not execute the resulting provider on every host.
