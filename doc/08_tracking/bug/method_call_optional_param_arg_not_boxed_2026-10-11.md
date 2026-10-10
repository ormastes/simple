# Method-call arguments are not coerced to Option handles for `T?` scalar parameters

**Status:** open. Found in review of the rebased nil/optional series
(`work/rel-native-nil-compare-rebased-20261010`, resolution `933101bb85e`).
**Engines:** staged-native (any compiler built by the pure-Simple MIR
lowering), both backends. The interpreter is unaffected (dynamic values).
**Parent:** `native_scalar_nil_compare_payload_bits_2026-10-10.md`, fix 5.

## Defect

The representation rule of the parent record says an Optional value is ALWAYS
the enum-id-1 handle or the bare nil sentinel, never a raw payload word. The
coercion that enforces it at a call (`ensure_option_handle` on each argument
whose parameter is declared `T?`) runs on the free-function call path only
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, the
param-directed boxing block). The method-call paths pass their arguments raw:

- `lower_receiver_and_args` (`src/compiler/50.mir/mir_lowering_stmts.spl`),
- `build_args_from_receiver`
  (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`),
- the `Unresolved` method arm in the same file.

So for `me put(v: i64?)`, `w.put(3)` hands the callee the raw word 3. Inside
the callee `v == nil` lowers to `rt_is_none(v)`, and `rt_is_none(3)` is true:
the integer 3 reads as nil. A `bool?` parameter receives raw `true`/`false`,
an `f64?` raw float bits. `v ?? d` and `if val x = v` go through the same
handle predicates and are wrong the same way.

## Evidence (lowering probe, interpreted pure-Simple lowering of this tree)

`rt_enum_new` / `rt_enum_id` / `rt_is_none` occurrences in the lowered MIR:

| function | source | enum_new | enum_id | is_none |
|---|---|---|---|---|
| `free_lit` | `take(3)` with `fn take(o: i64?)` | 1 | 1 | 0 |
| `m_lit` | `w.put(3)` with `me put(v: i64?)` | 0 | 0 | 0 |
| `m_var` | `w.put(x)`, `x: i64` | 0 | 0 | 0 |
| `m_bool` | `w.putb(x)`, `x: bool`, `me putb(v: bool?)` | 0 | 0 | 0 |
| `m_nil` | `w.put(nil)` | 0 | 0 | 0 |
| `put` (callee) | `if v == nil:` | 0 | 0 | 1 |

(Reviewer probe: `C:/dev/simple-bootstrap-storage/intensive-tests/
review_nil_rebased/method_arg_box_probe_spec.spl`, `probe.log`.)

## Why it matters

It is what made the typed HIR codec writers (`put_i64(v: i64?)`) wrong: every
one of the 1,301 `w.put_i64(...)` and 121 `w.put_bool(...)` sites in
`src/compiler/20.hir/generated/hir_codec.spl` is a method call, so
`w.put_i64(3)` would have written `N` and the HIR cache would never hit --
the bug PR #2882 fixed. The codec was therefore put back on the rendered-text
form and does not depend on this defect.

## Fix direction

Apply the same parameter-directed `ensure_option_handle` coercion the
free-function path uses at the three method-call sites, for every dispatch
kind (instance, static, trait, extension, and the `Unresolved` arm), with one
must-fail-before spec per dispatch kind.

## Audit: methods with a scalar `T?` parameter

Scan of src/compiler, src/lib, src/app (text scan of method signatures inside
`class` / `struct` / `impl` / `trait` / `actor` bodies; parameter type
`i8..u64?`, `f32?`, `f64?`, `bool?`, `char?` or `Option<scalar>`): **22
parameters on 19 methods**. "tested" = the body applies `== nil` / `!= nil` /
`??` / `.?` / `if val` / `match` / `unwrap` to the parameter; "forwarded" =
it only stores or passes it on (the raw word then escapes into a field or
another Optional slot, where the series' rule no longer re-boxes an
already-Optional local).

| method | parameter | use |
|---|---|---|
| `src/compiler/35.semantics/resolve_lookup_helpers.spl:82` `MethodResolver.resolve_call_result_type_raw` | `raw_symbol_id: i64?` | tested (one caller, `35.semantics/resolve.spl:549`) |
| `src/compiler/70.backend/backend/common/mir_text_codegen.spl:267` `MirTextCodegen.translate_vhdl_signal_assign` | `delay_ns: i64?` | forwarded |
| `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:804` `MirToLlvm.translate_vhdl_signal_assign` | `delay_ns: i64?` | forwarded |
| `src/compiler/80.driver/build_log.spl:140` `BuildLogger.add_diagnostic` | `line: i64?` | forwarded |
| `src/lib/common/json/builder.spl:84` `JsonBuilder.field_opt_int` | `value: i64?` | tested |
| `src/lib/nogc_sync_mut/io/tcp.spl:534`, `:557` `TcpStream.set_read_timeout` / `set_write_timeout` | `ms: i64?` | tested |
| `src/lib/nogc_sync_mut/io/udp.spl:224` `UdpSocket.set_read_timeout` | `ms: i64?` | tested |
| `src/lib/nogc_sync_mut/net/http.spl:224` `HttpClient.set_timeout` | `timeout_ms: i64?` | forwarded |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:668`, `:684` `ActorScheduler.send_message` / `send_high_priority` | `from_id: i64?` | forwarded |
| `src/app/interpreter/async_runtime/mailbox.spl:115` `MessageRef.new` (static), `:269`, `:328`, `:354` `Mailbox.send` / `send_normal` / `send_high` | `sender_id: i64?` | forwarded |
| `src/app/interpreter/collections/persistent_symbol_table.spl:69` `PersistentScope.new` (static) | `parent_id: i64?` | forwarded |
| `src/app/interpreter/memory/message_transfer.spl:454` `MailboxMessage.new` (static) | `sender_id: i64?` | forwarded |
| `src/app/llm_caret/claude_full/utils/bash/specs/types.spl:8` `BashCommandArgSpec.new` (static) | `isOptional`, `isVariadic`, `isCommand: Option<bool>` | forwarded |
| `src/app/llm_caret/claude_full/utils/toolSchemaCache.spl:8` `CachedToolSchema.new` (static) | `strict`, `eagerInputStreaming: Option<bool>` | forwarded |

Totals: 4 in `src/compiler` (1 tested), 5 in `src/lib` (4 tested), 13 in
`src/app` (0 tested). The HIR codec writers are not in the list: they keep
non-optional parameters.

Limits: non-scalar optionals (`text?`, `Foo?`, `[T]?`) are out of scope of
this record -- their arguments are raw on method calls too, but a pointer or
text handle cannot collide with the nil word the way the integer 3 does.
