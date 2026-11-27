# P3 WA: unresolved method on generic/trait receiver (`WA-P3-generic-recv`)

Stage3 per-file MIR reports "unresolved method call: is_err/unwrap/unwrap_err/then/len" and
"E-MIR-TYPE-TypeParam: unsubstituted generic type parameter 'T'" when the receiver comes from a
method-returned `Result<..>`, a trait-typed field (`inner: AsyncRead` -> `Future<T>`), or a var assigned
from untyped-param (implicitly generic) functions. The runtime-fallback path also lowers such calls to a
const-0 placeholder (method_calls_literals.spl, Task #145) — must become a hard error.

Real fix: substitute receiver type arguments in 30.types inference / 40.mono for field, trait-method and
generic-fn returns before method lookup.

WA sites:
- src/compiler/70.backend/linker/obj_taker.spl — 4 is_err/unwrap -> typed match
- src/compiler/40.mono/instantiation.spl — is_err removed, single typed match
- src/lib/nogc_async_mut/io/buffer.spl — 6 typed Future bindings before `.then`
- src/lib/nogc_sync_mut/compression/gzip/compress.spl — 2 `.len()` index loops -> for-in
Note: the macro_registry / macro_reference_projector / macro_source_from_parse_v1 `insert` sites are
already rewritten upstream (push + shift); no WA needed.
