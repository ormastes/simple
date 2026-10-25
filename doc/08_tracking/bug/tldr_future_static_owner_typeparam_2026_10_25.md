# TLDR future factory owner reaches MIR with generic T

Status: OPEN underlying static generic inference issue; explicitly typed source workaround.

The fixed P2 producer `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28` reports `E-MIR-TYPE-TypeParam: unsubstituted generic type parameter 'T' reached MIR lowering` for `compiler.driver.cache.reader.tldr_table_v1`, module699, at +1388207ms in the full P3 object build. Log: `/Users/ormastes/wt/release-phase2-review/build/verify/provisional-p3-generic-len-object-20261025-03/logs/p3-build.log`. The module trace finishes seven concrete methods and skips its generic `R: SourceReader` function; the collector reports the error at module scope, without identifying which expression produced it. Earlier function_lowering and cranelift probes did not reproduce this failure.

The table's only `T`-generic owner is `Future<T>` in `deref`. Its declared result is `Future<text?>`, but both static factory receivers omit their owner arguments: `Future.from_value(Some(...))` and `Future.pending()`. Bind both receivers explicitly as `Future<text?>`. The ready branch still stores `Poll.Ready(Some(text))`; the missing branch stays `Poll.Pending`. No queue, publication, runtime representation, or generic compiler error policy changes.

The regression exercises actual table methods: pending snapshots, one fill request across aliases and after draining, empty publication refusal, ready optional text, identical/conflicting republish, original pending snapshot preservation, and independent-module requests. It compares scalar payloads and queue elements rather than aggregate array handles. Native fixed-P2 verification remains pending; diagnostic interpreter evidence alone does not prove native MIR repair.

Remove the `@workaround` and explicit receivers only after the unqualified factories pass the same semantic regression and fixed native compilation with concrete `text?` type binding. Keep this issue open until inference itself is repaired. No P2, Rust, or runtime rebuild is part of this change.

Validation cycle 1: the existing gen13 diagnostic interpreter executed all 6 TLDR SSpec cases (6 passed, 0 failed/skipped/dropped), raw exit 0. Guard: 3 GiB enforced, 602,800 KiB peak, quiescent, zero observer errors. Source/spec/fixture/seed hashes matched before and after. Evidence: `/Users/ormastes/wt/release-phase2-review/build/verify/tldr-future-interpreter-20261025-01/`. No native compiler or P3 pass is claimed.
