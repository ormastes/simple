# C-only Darwin runtime retained the Rust packing hook

Native six-root proof attempt 3 compiled 1,310 source files, then failed linking
`runtime_thread.o` from its freshly built core-C archive. The missing symbol was
`simple_note_user_threads_started`, an undefined Mach-O weak reference. The Rust
runtime defines it to stop lazy in-place array packing before user concurrency;
a C-only runtime has no such packing. Darwin's classic linker rejected the
provider-free weak reference. This was not a missing Simple source root.

The repair selects `SIMPLE_RUNTIME_NO_RUST_ARRAY_PACKING=1` only for the final
C-only composition. Mixed-runtime supplements preserve the callback by default.
`SIMPLE_CORE_C_STANDALONE` cannot select this behavior because mixed supplements
also use it. Rust and Simple runtime archive/object cache identities distinguish
the new composition. Stage 4 compiler and hosted supplements retain the hook.

Native probes on arm64 Darwin passed: a C-only header consumer linked and ran
without a provider; a mixed consumer with a real callback observed exactly one
notification; compiled production `runtime_thread.c` had no callback reference
in the C-only mode and retained it in mixed mode. The durable regression owner
is `scripts/check/check-core-c-thread-packing-hook.shs` (syntax checked; equivalent
native probes ran before it was written). Full seed rebuild, native focused
six-root controls and compiler qualification remain pending.

Failed proof evidence is retained under
`build/verify/six-root-native-proof-20261024-03/` and the adjacent
`six-root-native-proof-03.{log,rss.env,status.env}`. The failed producer source was
`874891fd59fdb0b9b59ad3f7c7fcf5f0d8758541`. Its watchdog completed with exit 1,
verified quiescence, and peak RSS 4,822,288 KiB under the 8 GiB enforced cap.
