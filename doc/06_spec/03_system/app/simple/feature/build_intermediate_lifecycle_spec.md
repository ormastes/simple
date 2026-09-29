# Build Intermediate Lifecycle Specification

The native build removes old private staging files before work begins and removes failed-build scratch by default. A user can retain diagnostics with `--keep-intermediates`, or retain and print exact paths with `--print-intermediates`. Reusable caches and requested outputs are never cleaned by this policy.
