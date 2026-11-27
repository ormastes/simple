# Host alias repair evidence

PR [9261](https://github.com/ormastes/simple/pull/9261/checks) merged while checks were pending; its later Code Idiom gate failed `local-rt-dual-implementation` for the new symbol. The retained original log records that failure. The gate actually counts C and Rust definitions; its earlier diagnostic wording did not describe the separate Simple alias layer.

The runtime crate already includes `runtime_process_tree.c` in build.rs. A public Rust module now provides a genuinely callable, ordinarily mangled host forwarding function through a private link-name binding to the same C ABI leaf. No second exported C symbol, independent waitid policy, baseline exception, or allowlist update was added. The existing Simple process SFFI owner provides the signature-identical alias registered in rt_alias_map.sdn.

Commands below ran with `systemd-run --user --scope --quiet -p MemoryMax=512M -p MemorySwapMax=0 timeout --signal=KILL 30s` prepended; PRIVATE was `/tmp/process-owner-alias-native-20261115`.

```
cc -Wall -Wextra -Werror -I src/runtime -c src/runtime/runtime_process_tree.c -o PRIVATE/process-tree.o
rustc --edition=2024 src/runtime/test/process_owned_child_rust_alias_selfcheck.rs -C link-arg=PRIVATE/process-tree.o -o PRIVATE/rust-alias-check
PRIVATE/rust-alias-check
nm --defined-only PRIVATE/rust-alias-check
```

The actual Rust module and actual C object are linked together. Six real-child/nonchild observations compare both call surfaces and preserve exit7 for exactly one reap. Symbol inspection proves one `rt_process_owned_child_state` C ABI definition plus the distinct Rust-mangled wrapper. This is delegation and linkage evidence, not independent algorithm parity or a full Cargo build. The Simple alias was source-reviewed, not executed.

The committed-source dual-lane gate uses the same memory/swap scope and a60-second deadline:

```
sh scripts/check/check-rt-dual-implementation-ratchet.shs --rev 6e040f230a7c2cca002d226a4210274da23def28 --baseline-rev f7e30f9e751d1b6f125a1930d8dd8533bbbaf620
```

Native macOS/FreeBSD, full runtime/bootstrap and grouped scheduling remain unqualified. Original green physical primitive checks were not repeated.
