# Bug: pure-Simple async HTTP server crashes on the first event-loop poll

- **ID:** httpserver_static_serve_zeroed_cache_segfault_2026-06-17
- **Severity:** P1 (the `nogc_async_mut` HTTP server could not serve a single request)
- **Area:** compiler interpreter extern (`rt_event_loop_*`) + lib/nogc_async_mut io/driver
- **Status:** INTERPRETER crash **FIXED + verified**. NATIVE crash **FIXED +
  verified 2026-06-17** (runtime root-cause fix, option A — see "Real fix landed"
  below).

## Live evidence
Recurring kernel segfaults Jun 16→17 in the natively-built perf fixtures
(`httpserver_live_static_fixture`, `proxy_live_httpserver_proxy`,
`simple_static_server`): `segfault at 8 ip 0x46fb4f` etc. The owning checks
(`check-httpserver-live-static.shs`, `check-proxy-live-httpserver*.shs`) report
`STATUS: PASS` while the binary segfaults — worker crashes don't fail the harness.

## Root cause (interpreter) — FIXED
The server dies on the **first event-loop poll, before any request is accepted**.
Located by print-bisecting the live worker flow: the crash is in
`IoDriver.poll_count` (`src/lib/nogc_async_mut/io/driver.spl`) at the event-loop
poll, NOT in the static/cache path (the gdb symbol `StaticCompressionCache.get`
is an unreliable-AOT-symbol misattribution; the hot path is
`inline_static_handler`, which never touches the cache).

`rt_event_loop_poll` has a **count + indexed-get contract** (matching the native
runtime `runtime_native.c`):
- `rt_event_loop_poll(loop, max, timeout) -> i64` returns the COUNT of ready fds
  and stashes them; `rt_event_loop_poll_get_fd(index) -> i64` returns each fd.
The driver uses exactly this: `raw_count = rt_event_loop_poll(...)`, then
`while ri < raw_count: rt_event_loop_poll_get_fd(ri)`.

But the **interpreter impl violated the contract**:
`rt_event_loop_poll_interp` returned `Value::array(platform::poll(...))` (the fd
array) instead of the count, and there was **no `rt_event_loop_poll_get_fd_interp`
registered at all**. So `while ri < raw_count` compared an int to an array →
`error: semantic: type mismatch: cannot convert array to int`, killing the server
on poll #1. (Confirmed: `accept_res` was a proper `-1`; the crash was the next
poll branch, not the accept compare.)

### Fix (landed in source + bootstrap seed)
- `src/compiler_rust/compiler/src/interpreter_event_loop.rs`:
  `rt_event_loop_poll_interp` now stashes the ready-fd `Vec<Value>` in a
  thread-local and returns `Value::Int(count)`; added
  `rt_event_loop_poll_get_fd_interp(index) -> Value::Int(fd)` (mirrors the native
  `poll_results[]` contract).
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`: registered
  `rt_event_loop_poll_get_fd`.
- `src/lib/nogc_async_mut/io/driver.spl`: `cancel`, `close`, `poll_recv_bytes`
  changed `fn(self)` → `me` (they mutate self; the compiler rejected them for JIT
  with "use `me` instead of `fn`", forcing a degraded fallback).

### Verification
Rebuilt the seed (`cargo build --profile bootstrap -p simple-driver`) and ran the
fixture under the interpreter + a real client:
```
listening: 1
RESPONSE_HEAD: HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 10\r\n...
HAS_BODY: True        # served the "static-ok" file body
RESULT: SERVER ALIVE  # no crash, no "cannot convert array to int"
```
(Deployment to `bin/release/<triple>/simple` is a separate `--deploy` step.)

## Remaining: NATIVE crash — RE-DIAGNOSED 2026-06-17, it is a RUNTIME GAP (not a dispatch bug)
With the interpreter fix, the IDENTICAL source serves correctly end-to-end —
proving the Simple logic is sound. The natively-built fixture still SIGSEGVs
(`rsi=nil`, `mov 0x8(%rsi)`), backtrace `Worker.run → handle_completion →
worker_sendfile_open_path_for_pending → StaticCompressionCache.get`.

### Faithful minimal reproducer (settles the root cause)
`sendfile_pending: Dict<i64,(text,i64,i64)>` (worker.spl:270) is populated via
**index-assign** `self.sendfile_pending[fd] = (...)` (worker.spl:2378) and read
via `.get(fd)` (worker.spl:1087). A faithful repro:
```
var d: Dict<i64,(text,i64,i64)> = {}
d[3] = ("file_a.txt", 10, 20)
print(d[3].0)         # interp: file_a.txt   | native: <empty/nil>
print(read_via_get(d, 3))  # interp: file_a.txt | native: SIGSEGV
```
- **Interp:** correct end-to-end.
- **Native:** `d[3]` already prints **nil** — the clean MIR `IndexGet` path with
  NO method-collision *still* fails — and `.get(fd)` then SIGSEGVs.

### Root cause: the native C runtime has NO working dict index path
The earlier write-up's premise — that `rt_index_get` is a tag-dispatched
"array/dict/string" get — is **WRONG**. Primary source (`runtime_native.c`):
- `rt_index_get(coll, idx)` (1945): `rt_core_as_array(coll); if (a) …; return 3;`
  — **array-only**, returns `3` (nil) for any dict.
- `rt_index_set(coll, idx, val)` (1951): `rt_core_as_array; if (!a) return 0;`
  — **array-only**, so `d[fd] = …` **silently no-ops on a dict** (the dict is
  never populated — that is why `d[3]` reads nil).
- `rt_dict_get(SplDict*, const char* key)` (1966) and `rt_dict_insert` (1978,
  `rt_core_as_string(key)`) are **C-string-keyed only** — there is no int-key
  dict path in the native runtime at all.

So an int-keyed `Dict` cannot be written or read in a native build. Two distinct
defects stack:
1. **Runtime gap (primary):** `rt_index_get`/`rt_index_set` are array-only; the
   native dict accessors are string-keyed. `Dict<i64,V>` has no native get/set.
2. **Dispatch crash (secondary):** because `Dict<K,V>` erases to `TypeId::ANY`
   (type_resolver.rs:421), bare `.get` falls through to name-suffix binding and
   resolves to `StaticCompressionCache.get` (`func_ids` last-write-wins) →
   reads the dict as that struct (`self.entries` @0x10 → nil) → NULL+8 deref.
   Disasm: `worker_sendfile_open_path_for_pending+12: lea StaticCompressionCache.get; call`.

### Why a codegen `.get` guard CANNOT fix this
A bare-`get` guard routing to `rt_index_get` only stops the SIGSEGV by returning
`3`/nil — the dict was never populated and `rt_index_get` is array-only anyway.
That is a cover-up (forbidden by `feedback_no_coverups`) and exactly reproduces
the prior "served req#1, crashed req#2" failure (the bogus nil propagates).

### Real fix landed (option A — runtime root cause)
The native AOT runtime had **no working dict at all**: it linked
`runtime_legacy_core.c` (whose `spl_dict_*` are no-op stubs) and `runtime.c`'s
real `SplDict` was never compiled in; `rt_index_get`/`rt_index_set` were
array-only. Fix:

1. **`src/runtime/runtime_native.c`** — added a self-contained `RtCoreDict`: an
   open-addressing hash table (linear probe + tombstones + resize) over the
   tagged-int64 value representation, with a `kind` first byte
   (`RT_VALUE_HEAP_DICT 0x06`) and an `rt_core_as_dict()` detector mirroring
   `rt_core_as_array`. Keys are **canonicalized** (`rt_core_dict_canon_key`) so
   the unboxed key from `d[k]=v` (IndexSet) and the boxed key from `d.get(k)`
   (method, `rt_box_int`) collapse to one representation via
   `rt_core_numeric_arg` — the same normalizer `rt_array_get` already uses, so no
   codegen key-boxing change was needed (and no array-index regression). Hash is
   tag-aware (int by value, string by content via FNV-1a); equality uses the
   existing `rt_native_eq`, so **string-keyed** native dicts (also previously
   stubbed) now work too. Rewrote `rt_dict_new/get/set/insert/contains/len/
   clear/keys/values` + new `rt_dict_remove` to the tagged ABI, and added the
   dict branch to `rt_index_get`, `rt_index_set`, and `rt_contains`.
2. **`src/compiler_rust/.../codegen/instr/closures_structs.rs`** — added a bare
   `.get(key)` guard in `compile_method_call_static` (mirrors the existing
   `has`/`len` guards) routing the type-erased `Dict<K,V>`→`ANY` receiver to the
   tag-dispatched `rt_index_get` instead of name-suffix-binding it to a wrong
   user `Type.get` (the SIGSEGV).

3. **Key-representation unification (completion).** `d[k] = v` (IndexSet) stores
   the key TAGGED (rt_value_int), but bare `d.get(k)`/`d.remove(k)` received it
   UNBOXED (raw native int). canon_key cannot reconcile those (raw 8 is
   bit-identical to tagged 1), so ~1/4 of int keys (k ≡ 0,1 mod 8) silently
   missed even though the crash was gone. Fix: tag the int key INLINE in the bare
   get/remove guard (`rt_value_int(v) == v<<3`, INT tag 0 → a left shift;
   inline, NOT via rt_box_int which is unlinked in native AOT and would
   `call 0x0`). canon_key hardened so small ints with heap-tag-colliding low
   bits canonicalize as integers (heap branch gated on `>= 4096`).
4. **`.remove` wired** (`rt_dict_remove` + runtime_sffi spec + try_compile
   mapping + bare guard). Previously a "function not found" no-op, so
   `sendfile_pending`/`sendfile_open_files` never cleared (reused fd → stale
   read). Now removes correctly.

### Verification (by returned value, not "no crash")
- Native residue sweep matches the interpreter oracle EXACTLY for
  k in {1,7,8,9,16,17,4096}: `d.get(k) == d[k] == k*10` for every key (the
  previously-broken k=1/8/9/16 included); `.remove(9)` clears (d[9]→nil) leaving
  others intact.
- `.get`/`.remove` on a **known-type user method** (`Box.get`) is NOT hijacked
  (returns 42 via the user method) — guard only fires on type-erased receivers.
- **Array indexing unaffected** (`a[1]=60`→60, `a[2]`→7).
- Native server's exact pattern (`.get(fd)` → `if not pending.?:` →
  `pending.0/.1/.2`): present→value, absent→nil-branch, fields correct.
- Real natively-built `httpserver_live_static_fixture`: serves correct bodies
  across repeated requests, server stays alive — the prior "req#1 ok, req#2
  crash" is gone. (Small files use `inline_static_handler` and skip
  `sendfile_pending`; the sendfile path's get/remove logic is covered by the unit
  sweep + server-pattern test above.)

### Orthogonal native bug — FIXED 2026-06-17 (separate commit)
`for k in <array>` SIGSEGV'd in native (`call 0x0`) while working in the
interpreter. Root cause: for-in lowers to a `rt_for_iterable(collection)` call
(normalize iterable: dict→array of (k,v) tuples, pass-through otherwise), which
was implemented only in the Rust/JIT runtime and **absent from the C runtime**
that native AOT links — the call hit a NULL GOT slot (`nm` showed
`U rt_for_iterable`). Fixed by defining `rt_for_iterable` + `rt_dict_entries` in
`runtime_native.c`. Verified: `for k in [1,7,8]`→`1 7 8`, `for (k,v) in dict`
yields correct keys/values, all matching the interpreter. (Note: using an
iterated dict KEY in arithmetic still sees its tagged form — a pre-existing
tagged-value quirk present in the interpreter too, independent of this fix.)

### Out of scope / separate pre-existing bug (NOT this fix)
`if val x = <optional>` and `opt.?` payload extraction are broken in the
**interpreter** (returns the enum / wrong payload) after parallel-agent churn in
the Option/pattern lowering (commits `c443a66` scope-elif-pattern-bindings,
`04d72f7` lane-Option-unwrap). This is independent of dicts (reproduces on a
plain `i64?` from a normal function) and of this native dict fix, which is
native-codegen + C-runtime only. Track separately.

Also note the AOT build is degraded (fails to compile `h2_hpack.spl` /
`context_propagation.spl` — "cannot infer field type: struct 'ANY'" — and stubs
33 symbols); cleaning those would aid further native debugging.

## Ruled out
- Private-symbol collision (no `warn_duplicate_private_signatures` warning).
- Stale binary (fresh rebuilds reproduce).
- Bare→Option payload loss in `set_static_handler` (no effect; reverted).
- Threading (fixture `worker_count=1` runs inline, no thread spawn).

## Secondary bug (separate) - FIXED 2026-06-22
`static_file.spl` `_static_text_to_bytes` and `compression.spl`
`_compression_text_to_bytes` called `s.byte_at(i)` on `text`, but `byte_at` is
not a `text` method. The broken path is reached by `StaticFileHandler.handle`
when `Accept-Encoding` makes the server try to compress a text response.

The same session also found the compression cache was effectively non-persistent:
array `push` results in `StaticCompressionCache.put`, `get`, and `evict_oldest`
were not assigned back, and the free `serve_compressed_or_plain(..., cache)`
received the cache by value. `StaticFileHandler.handle` now mutates its owned
cache through `StaticCompressionCache.serve_compressed_or_plain(...)`.

Fix landed in `81a59b953177` (`fix: persist static compression cache hits`):
- replaced the bad text loops with `std.crypto.types.text_to_bytes`;
- assigned rebuilt cache arrays back after `push`;
- added the mutating cache method and routed the handler through it;
- refreshed static compression and content-encoding specs/docs.

Verified with focused `bin/simple check`, the static compression cache spec, the
static handler compression spec, the HTTP content-encoding integration spec, the
optimizer pass on touched files, direct-env runtime guard (`--working` and
`--staged`), and `doc/06_spec` layout guard (`0` executable specs).
