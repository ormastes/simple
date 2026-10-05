# Simple Browser at 4K runs entirely in the tree-walk interpreter (whole-module de-JIT from bare-name collisions)

- Date: 2026-10-04
- Status: **OPEN.**
  - Seven collisions were fixed by renaming.
  - The h1_client blocker was fixed in the seed (single-argument `Result<T>`).
  - The remaining blockers are the JS engine's `JsBrowserResult<T>` (no Err
    type) and four JIT codegen stub failures. See "Follow-up".
- Related: `lint_dejits_whole_program_span_struct_collision_2026-08-18.md` (same
  seed limitation: the run/JIT lane flattens every import into one bare-name
  namespace). `exec_core.rs` documents why the `SIMPLE_JIT_DUP_STRUCT_FEED`
  consensus fallback must stay off.
- Binary for every number: a Rust seed built from `src/compiler_rust` at
  `73150c2673f` (`cargo build --profile bootstrap -p simple-driver`, sha256
  `056afef47c8d…`). The deployed `bin/simple` (Sep 27,
  `f2b3edd25068…`) cannot run origin/main at all, because it predates
  `faa15917adc` (host `@when` stripping). It fails to parse
  `src/lib/nogc_sync_mut/io/windows_redirected_process.spl`. Host: M4, 24 GB, macOS 25.5.

## Symptom

`simple run src/app/browser/main.spl simple://home` prints
`[jit-fallback] HIR lowering error: ... whole module dropped to the interpreter`.
At the new 4K default (3840x2160) the headless render does not finish
within `timeout 900`. The run was killed at **900.2 s wall, 734.8 s user, 2.79 GB max RSS**.

| viewport | wall | user | max RSS | engine |
|---|---|---|---|---|
| hello-world `.spl` (loader floor) | 0.08 s | 0.02 s | 23 MB | JIT |
| 64x36 | 51.7 s | 36.5 s | 1.65 GB | interpreter |
| 384x216 (live lane) | 60.5 s | 53.3 s | 1.62 GB | interpreter |
| 3840x2160 (vulkan lane) | >900 s (killed) | 734.8 s | 2.79 GB | interpreter |

The marginal cost is about **0.2 ms of interpreted work per pixel**: going from 64x36 to 384x216
adds 16.8 s user for 80.6k pixels. Most of the ~1.6 GB floor comes from loading
the browser's module graph into the interpreter. Hello world is 23 MB.

## Root cause

The flattened module registers structs and functions by bare name. When a name has two
or more definitions, a field read or return type resolves against the wrong layout. HIR
lowering then fails, and the WHOLE flattened program is demoted.

Each strict run (`SIMPLE_JIT_STRICT=1`) exposed the next collision:

| collision | resolved to | fix (renamed side) |
|---|---|---|
| `TextMetrics.char_count` | `common/layout/text_metrics.spl` | engine2d `helpers_text.TextMetrics` -> `Engine2dTextMetrics` |
| `HtmlToken.token_kind` | `blink/html_parser/token.spl` | browser_engine -> `WebHtmlToken` |
| `ComputedStyle`, `LayoutContext`, `BoxShadow` | blink copies | browser_engine -> `Web*` |
| `hex_byte` returns `text` | `jit_util.hex_byte` | `dom_color` -> `css_hex_byte` / `css_hex_nibble` / `css_hex_digit` |
| `RenderScene.viewport_w` | `common/render_scene` | browser_engine `layout.spl` stub -> `LayoutPaintScene` |
| non-generic `Pair` | (`custom_properties`) | -> `CssVarPair` |
| `BrowserError` / `Logger` / `script_error` / `BrowserResult` (warnings) | JS engine `js_error` copies | JS side -> `JsBrowserError` / `JsLogger` / `js_script_error` / `JsBrowserResult` |

**Remaining blocker, not fixed here:** this lane must not edit network code.

- `gc_async_mut/gpu/browser_engine/net/h1_client.spl` `parse_http_response_bytes`:
  `struct 'ANY' field 'first'`. The type `Pair<[u8],[u8]>` lowers to ANY
  inside the full browser graph, even with an explicit annotation. A
  standalone probe of the same shape lowers fine.
- The same file in isolation (`use ...net.h1_client.*`) also fails in
  `H1Client.request` with `struct 'ANY' field 'tls_conn'`.

## Diagnostic added

`SIMPLE_SEED_RETURN_TYPE_DEBUG=1` now also prints
`lowering error in function <name>: <error>` for any body-lowering failure
(`hir/lower/module_lowering/function.rs`). The whole-module message names
only the entry file. Without this, finding `hex_byte` took a blind search.

## Other findings

- origin/main `gc_async_mut/gpu/engine2d/draw_ir_adv.spl` called
  `draw_ir_command_has_unsupported_v4_state`, but that function does not exist on main or on
  `release/1.0`. It, and the V4 `affine_transform` / `raster_policy` fields it
  reads, live only in `1ef63f7a985`. Every browser render failed with
  `E1002 function not found`. Main's `DrawIrCommand` has no V4 state, so this branch removes the call.
  The guard was vacuous on main.
- ~~JIT `for p in px` takes 1.27 s vs 39 ms indexed.~~ That comparison read in
  one loop and wrote in the other. See the follow-up below for fair numbers and the fix.

## Follow-up 2026-10-04 (branch work/browser-dejit-h1-forin)

### Fixed in the seed

1. **h1_client blocker: single-argument `Result<T>` resolved to ANY.**
   The cause was in `hir/lower/type_resolver.rs`, not in h1_client. The
   annotation experiment above misled the earlier diagnosis. Only
   `Result<T, E>` was instantiated. `Result<T>` (27 owned signatures) fell to
   `_ => ANY`, which erased the Ok payload. `val status = parse_status_line(..)?;
   status.first` then had an ANY receiver. `Result<T>` is now
   `Result<T, ANY>`. This also fixes a silent JIT miscompile: `ok1(41)!` on
   `-> Result<i64>` answered `5448374378690` under the JIT. Now it answers
   `42`, as the interpreter always did.
   Repro: `hir::lower::tests::function_tests::single_arg_result_try_keeps_ok_payload_type`.
   Generalization: `..._force_unwrap_keeps_ok_payload_type` and
   `test/01_unit/compiler/result_single_arg_payload_spec.spl`.
2. **for-in over an array is ~11x faster.** Fair A/B on the same host, same
   counts, 3840x2160 `[u32]` read-and-compare:
   - for-in: **2507 ms -> 222 ms**.
   - indexed `while` read: 112 ms.
   - Cause: `IndexGet` -> `rt_index_get` -> `rt_array_get` validated the
     handle against the global heap registry twice per element (mutex plus
     SipHash `HashSet` lookup, per `sample`).
   - Fix: a statically-typed array iterable now calls `rt_array_get(arr, i64)`
     directly. That is exactly the call `rt_index_get`'s Array arm makes, so
     the element is the same and so is the NIL past a body-shortened end.
     Text and dict iterables keep the generic path.
   - Semantics probe: shrink/grow/assign-during-iteration, `[u32]`, text,
     dict, nested. Identical across old JIT, new JIT and interpreter.
   - Tests: `coverage_for_each_index_get` (updated),
     `coverage_for_each_dict_keeps_generic_index_get`,
     `test/01_unit/compiler/for_in_array_iteration_spec.spl`.
3. **JIT codegen panic.** The panic was `HashMap index` in
   `try_emit_vtable_type_switch`, on `runtime_funcs["rt_method_not_found"]`.
   That symbol was declared only for `BuiltinMethod`. It is now also declared
   for `MethodCallStatic`, and the switch refuses (falls back) instead of
   panicking.
4. Slow-function data below came from a local `SIMPLE_JIT_SLOW_FN_MS`
   probe; upstream now ships the same report as
   `SIMPLE_NATIVE_BUILD_RUST_TRACE=1` (`[rust-jit] slow function`, >=500 ms).

cargo `simple-compiler --lib`: 4199 pass / 34 fail before. After: 4202 pass
(3 new) / 34 fail, an identical failure set.

### Still blocked: the browser still runs interpreted (not shipped, and why)

With (1) applied, the next blockers are the JS engine's single-argument
`JsBrowserResult<T>` and a `LogLevel` enum collision. JS methods do
`match r: Err(e): e.message`, and the `Err` payload is unknown.

An experiment rewrote `JsBrowserResult<T>` to `Result<T, JsError>`. That
change is sound: every `Err` in those functions is a `JsError`, and no `?`
propagates a text error. It also renamed failsafe `LogLevel` to
`FailsafeLogLevel`. With both, the whole browser program reaches the
Cranelift JIT, but the result is **not shippable**:

- Compiling the 11,496 functions takes **~21 min** (1259 s wall under
  load ~30). a per-function codegen timer puts more than half of that in
  ONE synthesized function:

  | function | codegen | blocks | MIR insts |
  |---|---|---|---|
  | `__module_init_dynamic` (init of ~10k globals) | **674 s** | 17 | 151,371 |
  | `spirv_glass_material` | 19 s | 1 | 41,378 |
  | `JsInterpreter.eval_call` | 17 s | 1538 | 351,760 |
  | `JsInterpreter._native_webassembly_function_body_i32_result_with_args_for_module` | 15 s | 1498 | 191,159 |
  | `_apply_decls_without_grid_inner` | 8.8 s | 2597 | 26,400 |
  | `file_rename` (x2, flattened copy too) | 5-8 s | 513 | 1,799 |

  A fix that splits `__module_init_dynamic` into bounded chunks would
  remove more than half of the compile time.
- 4 functions fail codegen and become **empty stubs**, so the 64x36 frame
  paints **345** pixels against the interpreter's **479** (wrong output):
  - `ScriptHost.fetch` and `SimpleScriptExecutor.fetch`:
    `[CODEGEN-AMBIGUOUS-METHOD]` bare `dispatch` with 6 candidates.
  - `browser_renderer_command_capability_new`: unresolved global
    `crypto_sffi`.
  - `BrowserDomEventExecutor.listener_indices_for_target_event`:
    unresolved `self`.

So enabling the JIT today would trade a 52-74 s interpreted 64x36 render
for a ~21 min compile plus wrong pixels. The rewrite is kept out of the
tree; the patch is recorded in the PR body. Unblock condition: the 4 stub
failures fixed (their spec reproducers must show identical pixels to the
interpreter), and whole-program JIT compile time cut. A per-function
interpreter splice for functions that fail lowering would also help;
`apply_hybrid_transform` only covers unresolved externs today.

### Engine divergence found (pre-existing, both seeds)

Consider `for x in c: seen.push(x); c[2] = 99` over `[10, 20, 30]`:

- Under `simple run`, the JIT and the interpreter both see the write:
  `[10, 20, 99]`.
- Under `simple test`, it is not seen: `[10, 20, 30]`.

Not pinned by any spec until the language decides which is correct.

## Follow-up 2026-10-05 (branch work/jit-compile-time)

Root-caused and fixed the full-program JIT blockers:

- **Compile time: one global.** `__module_init_dynamic`'s 151k instructions
  were almost all ONE initializer, `var _kern_ascii_vals: [i32] =
  [_KERN_EMPTY; 72200]` (font_renderer). `lower_array_repeat` unrolled every
  integer-literal count into an explicit literal (72,200 x GlobalLoad +
  BoxInt). A repeat of >= 256 of a pure scalar (int/float/bool, not u8/u64)
  is now a runtime `rt_array_repeat` fill. Dynamic init is ALSO chunked
  (64 initializers per `__dyninit_part_<i>`, called in order by the
  unchanged root), which bounds every future init function. With both, a
  whole-program browser JIT compile went from ~25 min to ~3.5 min.
- **The 4 stub-compiled functions:**
  - `ScriptHost.fetch` / `SimpleScriptExecutor.fetch`: the bare `dispatch`
    was ambiguous with `VulkanFfi.dispatch` (4 params). Codegen now drops
    candidates whose declared param count cannot take the call. The two
    FetchDispatch classes now declare `impl FetchDispatch for ...`, so the
    runtime vtable switch picks between them.
  - `browser_renderer_command_capability_new`: a module-alias call
    `crypto_sffi.random_hex(16)` is unsupported in the flattened run lane.
    It now uses an aliased function import. Seed gap: module-alias calls are
    still unsupported in the JIT lane.
  - `BrowserDomEventExecutor.listener_indices_for_target_event`:
    `expr_uses_self` had no `Coalesce` arm (or ~20 other wrapper variants),
    so a `fn` whose body was `self.x.get(k) ?? []` was lowered as static.
- Result with the JS result-type patch: `compile functions done failed=0`.

**Still blocking a JIT'd browser (being verified):** `finalize_definitions`
panicked: an AArch64 `bl` was 182-320 MB away with no far-call veneer. The
cause was a stale build, not missing code. Cargo does not fingerprint the
contents of a vendored (`directory` source) crate, so a target dir that built
cranelift-jit before #2501 kept the pre-arena object code after the patched
`vendor/cranelift-jit` landed (the seed binary had none of the arena's
strings). Fix: `cargo clean -p cranelift-jit --profile bootstrap` once
after pulling a vendor patch.

Pre-existing divergence found: `[u64::MAX; 300][0] == u64::MAX` is false
through `rt_array_repeat` in both the JIT and the interpreter, but true for
an unrolled literal. u64 repeats therefore stay unrolled.
