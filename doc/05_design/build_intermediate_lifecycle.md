# Build Intermediate Lifecycle Detailed Design

`build_intermediate_policy.spl` defines deterministic naming, classification, 24-hour stale selection, deletion, and retention reporting. `compile_targets.spl` runs stale cleanup after resolving/creating the output parent and before compiler setup. `--print-intermediates` implies retention. The two environment values are projected only around the driver invocation and restored afterward. Bootstrap LLVM cleanup treats the general keep switch as an alias of the older IR-specific switch.

Errors deleting stale managed scratch stop the build because continuing can hide storage/permission faults. Deleting an absent current staging file is idempotent. Requested `--emit-object`, `--emit-archive`, `--emit-shared`, and `--emit-smf` products remain durable outputs.
