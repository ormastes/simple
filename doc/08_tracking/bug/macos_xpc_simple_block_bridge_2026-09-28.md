# Native Simple XPC entrypoints need a verified Apple Block bridge

Status: OPEN. Source and SDK review only; no native callback or container launch
has been demonstrated by this report.

## Exact boundary

The installed Apple SDK declares `xpc_connection_handler_t` as a C function
pointer and `xpc_main` accepts that type. Simple documents `@export("C")` in
`doc/07_guide/platform/ffi/sffi.md`, so a missing generic C callback facility is
not an established blocker.

However, each accepted peer needs `xpc_connection_set_event_handler`, whose
`xpc_handler_t` is an Apple Block. A Simple function pointer or ordinary closure
cannot be passed as that value. The local SDK has no corresponding public
`xpc_connection_set_event_handler_f` declaration.

Search of owned Simple sources found no Apple Block construction/lifetime
adapter (`NSConcrete*`, `Block_copy`, or block literal support). Existing raw
allocation/write operations and exported functions could support such an
adapter, but their existence does not prove the required callback ABI or
lifetime. Do not describe this as an inherently impossible pure-Simple task.

The missing reusable component is a verified no-GC Apple Block adapter with:

- Correct native `isa`, flags, reserved, invoke, and descriptor layout.
- A C-callable invoke entry receiving the block pointer before the XPC event.
- Descriptor size/signature matching the target architecture and ABI flags.
- Explicit lifetime for descriptor, callback code, and captured state through
  XPC's asynchronous use and block copying/releasing.
- A defined policy for callbacks on dispatch threads and Simple runtime entry.

The initial adapter can use a noncapturing block and avoid capture copy/dispose
helpers, provided code and descriptor remain alive for every pending callback.
Do not mark dynamically allocated storage as global merely to bypass ownership.

## Resume and acceptance

1. Implement the adapter in the canonical no-GC sync SFFI owner, using existing
   pointer primitives; retain a narrow, documented unsafe boundary.
2. Build a native Simple callback fixture and prove actual Apple Block copying,
   invocation, and release on the target Mac. Exercise callback execution after
   the creating function returns and verify lifetime under repeated use.
3. Build host/service Simple entrypoints. `xpc_main` accepts each peer by
   installing its event handler and resuming, or rejects it by cancellation.
   Event objects are borrowed; explicitly retain any that outlive the callback.
4. Prove a request/reply through the signed embedded service, error delivery,
   disconnect handling, and cancellation. A packaging/signing pass is separate.
5. Prove actual sandbox denial and owned-workload cleanup before claiming a
   working Mac container. XPC connection lifetime alone does not establish
   process-tree ownership or cleanup.

Simple tests/checks were deliberately not rerun in the logical session because
the session verification cap was already reached. No speculative host/service
entrypoint or unverified pointer fabrication was added.

## Sources

- Local Apple SDK: `usr/include/xpc/xpc.h` lines 101, 126, 2678–2698;
  `usr/include/xpc/connection.h` lines 310–341, under
  `/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk`.
- [Apple: xpc_main](https://developer.apple.com/documentation/xpc/xpc_main(_:)?language=objc).
- [Apple: xpc_connection_set_event_handler](https://developer.apple.com/documentation/xpc/xpc_connection_set_event_handler(_:_:)?language=objc).
- [Clang: Apple Block ABI](https://clang.llvm.org/docs/Block-ABI-Apple.html).
- Existing primitives: `src/lib/nogc_sync_mut/ptr/raw.spl`,
  `src/lib/nogc_sync_mut/sffi/dynamic.spl`.
