# Non-optional return contract (E-SFFI-016) — repo-wide sweep, 2026-08-21

**Status:** class (a)/(b)/(c) CLOSED (guard green, 10 sites baselined behind an
unrelated seed bug). Updated 2026-08-21.

`2a59ff7f5e5` wired the seed's total return-contract validator. A Simple `fn`
declared `-> T` where `T` is not optional now aborts when its body evaluates to
nil:

    nil is forbidden by the non-optional return contract of '<fn>'   [E-SFFI-016]

## Scoping fact that shrinks the surface

The validator (`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`,
`validate_sffi_return_contract`) has exactly **two** call sites, both inside
user-defined Simple function execution (`:749`, `:800`). It does **not** run on
an `extern` call itself. So an `extern fn rt_x(...) -> T` whose runtime impl
returns nil is *latent, not fatal* — it only kills a build once a Simple `fn`
with a non-optional declared return forwards it. Class (b), the thin wrapper,
is therefore the whole live fault surface, and class (a) matters only through it.

Second fact: `sffi_return_contract` classifies `Type::Simple(_)` as
`NonOptional` with no escape for `any`/`Any`. `-> Any` is a non-optional
contract, which is why `Channel.try_recv() -> Any` — documented as "returns nil
if no messages available" — was a guaranteed abort in every polling loop.

## Class (a) — nil-capable `rt_*` externs

Derived mechanically, not by hand: the `insert_simple!("rt_x", impl)`
registrations under `src/compiler_rust/compiler/src/interpreter_extern/`
cross-referenced against which impl functions contain a `Value::Nil` return.

- **1303** `rt_*` registrations total
- **138** of them have a `Value::Nil` return path
- **1572** non-optional Simple wrappers forward some `rt_*` across
  `src/compiler/**` + `src/lib/**`
- **10** of those forwarded a nil-capable extern (class (b), below)

Note that many of the 138 return `Value::Nil` legitimately as the *unit* value
for a `-> void` wrapper; the guard excludes unit/void returns for that reason.

## Class (b) — thin wrappers forwarding a nil-capable extern (ALL FIXED)

| wrapper | file | was | now | why |
|---|---|---|---|---|
| `cranelift_file_read_bytes` | src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:31 | `-> [u8]` | `-> [u8]`, body `?? []` | both call sites already report "empty or unreadable" on `.len()==0` |
| `array_free_deep` | src/compiler/70.backend/sffi_minimal.spl:280 | `-> i64` | `-> i64`, body `?? 0` | `rt_array_free_deep` nils on a freed/foreign pointer |
| `Channel.try_recv` | src/lib/nogc_sync_mut/concurrent/channel.spl:144 | `-> Any` | `-> Any?` | doc already says "returns nil if no messages available" |
| `Channel.recv` | src/lib/nogc_sync_mut/concurrent/channel.spl:151 | `-> Any` | `-> Any?` | doc already says "returns nil if channel closed and empty" |
| `channel_try_recv_by_id` | src/lib/nogc_sync_mut/concurrent/channel.spl:201 | `-> Any` | `-> Any?` | same extern as `try_recv` |
| `file_read_lines` | src/lib/nogc_sync_mut/ffi/io.spl:53 | `-> [text]` | `-> [text]`, body `?? []` | only caller is `file_read_lines(path).len()` |
| `file_read_lines` | src/lib/nogc_sync_mut/sffi/io.spl:53 | `-> [text]` | `-> [text]`, body `?? []` | mirror of the above |
| `coverage_enabled` | src/lib/nogc_sync_mut/{ffi,sffi}/coverage.spl:11 | `-> bool` | `-> bool`, body `?? false` | a nil probe means "not enabled" |
| `random_hex` | src/lib/nogc_sync_mut/security/types.spl:846 | `-> text` | `-> text?` | `rt_random_hex` nils on OsRng failure; other callers already write `random_hex(n) ?? ""`, and collapsing a failed CSPRNG to `""` silently would be a security defect |
| `black_box` | src/lib/common/crypto/constant_time.spl:22 | `-> i64` | `-> i64`, body `?? value` | `rt_black_box` nils only for a 0-arg call (unreachable); `?? value` is identity and total |
| `metal_host_free`, `gpu_lut_free` | src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:194, backend_metal_runtime_ops.spl:70 | `-> i64` | `-> i64`, body `?? 0` | `rt_free` returns `Value::Nil` on **every** branch — these aborted on any call |
| `metal_host_write_i32`, `opencl_host_write_u8`, `cuda_launch_args_write_u8` | backend_metal.spl:197, backend_opencl.spl:46, backend_cuda_launch_args.spl:20 | `-> i64` | `-> i64`, body `?? 0` | `rt_ptr_write_*` nils on a rejected pointer |

Every corresponding `extern fn rt_*` declaration was moved to `-> T?` in the
same edit; a `??` on a non-optional declaration would not typecheck.

Call sites that consumed the newly-optional channel values had to be unwrapped:
`src/lib/nogc_async_mut/concurrent/multicore_green.spl:79,84` (`recv()! as i64`),
`src/app/ui.ipc/async_handler.spl:67` (`render_payload!` after its nil check),
`src/lib/nogc_sync_mut/security/types.spl:838` (`random_hex(8) ?? ""`).

## Class (b) — out of the fixed scope, still open

`src/compiler_rust/lib/std/**` (the seed's own bundled stdlib, a separate
vendored tree) carries the same shapes: `read_lines_unsafe`,
`read_bytes_unsafe`, `channels.spl` `try_recv`/`recv`, `hash.spl` `finish`.
`src/app/**` and `src/runtime/simple_core/**` carry a further ~10
(`cuda_port_free`, `vulkan_port_free`, `ui_web_ws_sha1_write`,
`ui_web_ws_sha1_finish_base64`, `session_token_runtime_random_hex`,
`measurement_ptr_write_i64`, `rt_tuple_get`). These are outside the assigned
`src/compiler` + `src/lib` scope and are left for a follow-up; the guard's
`--root` scan can be widened to them once they are fixed.

## Class (c) — explicit `return nil` / nil tail under a non-optional type

187 sites across `src/compiler/**` + `src/lib/**`. These are *not* extern
related — they are hand-written nil returns under a declared non-optional type,
and each one aborts if its branch is ever taken. Distribution by declared
return type:

     37  any
     28  tuple
     16  text
     14  Any
     12  list
      5  SourceLocation
      5  i64
      5  has_ConstValue
      5  bool)
      4  (ClassDef,
      4  bool)
      3  ({text
      3  Lazy
      2  (text?,
      2  SamlField
      2  Match
      2  HirExpr
      2  has_HoverInfo
      2  has_ConcreteType
      2  BreakpointInfo
      2  bool
      1  Terminator
      1  T
      1  ShbTraitEntry
      1  ShbStructEntry
      1  ShbReexportEntry
      1  ShbFnEntry
      1  ShbEnumEntry
      1  ShbClassEntry
      1  SamlStruct
      1  SamlFunction
      1  SamlExample
      1  SamlEnum
      1  SamlClass
      1  ModuleResolver
      1  MirBlock
      1  HttpResponseData
      1  has_YieldTransform
      1  has_Type
      1  has_SignatureHelp
      1  has_MarkedIdent
      1  has_GpuIntrinsicError
      1  has_ExtensionConfig
      1  has_BackendKind
      1  has_AwaitTransform
      1  has_AsyncInstInfo
      1  HardcodedSecretWarning
      1  EditorDocument
      1  [DeferredHint]
      1  CStruct
      1  [CoherenceError]

The `any`/`Any` bucket (51 of 187) is the largest and the most dangerous,
because `any` reads as "anything including nil" to an author but is
`NonOptional` to the validator. Full site list (file:line:fn:return-type:kind):

```
  src/lib/math.spl:298:average_i64:i64:return-nil
  src/lib/math.spl:303:median_i64:i64:return-nil
  src/compiler/15.blocks/plugin_startup.spl:85:eval_const:has_ConstValue:tail-nil
  src/compiler/60.mir_opt/optimizer_manifest.spl:444:manifest_json_to_string:any:tail-nil
  src/compiler/60.mir_opt/optimizer_manifest.spl:449:manifest_json_to_number:any:tail-nil
  src/compiler/60.mir_opt/optimizer_manifest.spl:454:manifest_json_to_array:any:tail-nil
  src/compiler/60.mir_opt/optimizer_manifest.spl:459:manifest_json_to_object:any:tail-nil
  src/compiler/60.mir_opt/optimizer_manifest.spl:464:manifest_json_object_get:any:return-nil
  src/compiler/60.mir_opt/optimizer_manifest.spl:467:manifest_json_object_get:any:tail-nil
  src/compiler/00.common/di.spl:165:resolve:Any:tail-nil
  src/compiler/90.tools/aop.spl:198:_aop_first_arg:Any:return-nil
  src/compiler/90.tools/aop.spl:200:_aop_first_arg:Any:return-nil
  src/compiler/90.tools/async_integration.spl:116:get_async_inst_info:has_AsyncInstInfo:tail-nil
  src/compiler/90.tools/async_integration.spl:231:create_await_transform:has_AwaitTransform:tail-nil
  src/compiler/90.tools/async_integration.spl:259:create_yield_transform:has_YieldTransform:tail-nil
  src/lib/editor/multi_buffer.spl:27:multi_buffer_get:EditorDocument:tail-nil
  src/lib/common/option.spl:31:option_filter:bool:return-nil
  src/lib/common/option.spl:35:option_filter:bool:tail-nil
  src/lib/common/math.spl:308:average_i64:i64:return-nil
  src/lib/common/math.spl:313:median_i64:i64:return-nil
  src/lib/common/option_ce.spl:55:option_ce_filter:bool):return-nil
  src/lib/common/option_ce.spl:58:option_ce_filter:bool):tail-nil
  src/lib/common/result.spl:22:result_map:i64:return-nil
  src/compiler/15.blocks/blocks/builder.spl:487:eval_const:has_ConstValue:tail-nil
  src/compiler/15.blocks/blocks/builder.spl:508:hover:has_HoverInfo:tail-nil
  src/compiler/15.blocks/blocks/easy.spl:208:eval_const:has_ConstValue:tail-nil
  src/compiler/15.blocks/blocks/easy.spl:256:eval_const:has_ConstValue:tail-nil
  src/compiler/15.blocks/blocks/definition.spl:165:hover:has_HoverInfo:tail-nil
  src/compiler/15.blocks/blocks/definition.spl:172:signature_help:has_SignatureHelp:tail-nil
  src/compiler/15.blocks/blocks/definition.spl:200:eval_const:has_ConstValue:tail-nil
  src/compiler/15.blocks/blocks/definition.spl:213:result_type:has_Type:tail-nil
  src/compiler/20.hir/inference/serialize.spl:66:hints_from_sdn:[DeferredHint]:tail-nil
  src/compiler/60.mir_opt/mir_opt/predicate_promote.spl:99:promote_block_predicate:MirBlock:tail-nil
  src/compiler/30.types/type_system/effects.spl:356:unwrap_promise:text:tail-nil
  src/compiler/40.mono/monomorphize/util.spl:115:infer_concrete_type:has_ConcreteType:tail-nil
  src/compiler/40.mono/monomorphize/util.spl:119:infer_concrete_type:has_ConcreteType:tail-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:158:read_text_dict:({text:return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:166:read_text_dict:({text:return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:171:read_text_dict:({text:return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:225:_read_def_suffix:(text?, {text:return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:232:_read_def_suffix:(text?, {text:return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:368:deserialize_class_def:(ClassDef, i64):return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:378:deserialize_class_def:(ClassDef, i64):return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:387:deserialize_class_def:(ClassDef, i64):return-nil
  src/compiler/40.mono/monomorphize/deferred_deserialize.spl:402:deserialize_class_def:(ClassDef, i64):return-nil
  src/compiler/35.semantics/macro_check/hygiene.spl:161:hygienescope_lookup:has_MarkedIdent:tail-nil
  src/compiler/35.semantics/macro_check/hygiene.spl:305:check_shadowing:text:return-nil
  src/compiler/35.semantics/lint/security_hardcoded_secret.spl:333:_check_password_assignment:HardcodedSecretWarning:tail-nil
  src/compiler/99.loader/module_resolver/types.spl:121:get_extension_config:has_ExtensionConfig:tail-nil
  src/compiler/99.loader/module_resolver/types.spl:386:moduleresolver_new:ModuleResolver:tail-nil
  src/compiler/80.driver/shb/shb_hash.spl:226:shb_find_fn:ShbFnEntry:tail-nil
  src/compiler/80.driver/shb/shb_hash.spl:234:shb_find_struct:ShbStructEntry:tail-nil
  src/compiler/80.driver/shb/shb_hash.spl:242:shb_find_class:ShbClassEntry:tail-nil
  src/compiler/80.driver/shb/shb_hash.spl:250:shb_find_enum:ShbEnumEntry:tail-nil
  src/compiler/80.driver/shb/shb_hash.spl:258:shb_find_trait:ShbTraitEntry:tail-nil
  src/compiler/80.driver/shb/shb_hash.spl:266:shb_find_reexport:ShbReexportEntry:tail-nil
  src/lib/nogc_async_mut/concurrent.spl:124:get:Any:tail-nil
  src/lib/nogc_async_mut/mailbox.spl:40:mailbox_receive:text:return-nil
  src/lib/nogc_async_mut/lazy_val.spl:199:filter:Lazy:tail-nil
  src/lib/nogc_async_mut/array.spl:57:array_find:bool):tail-nil
  src/lib/gc_async_mut/lazy_val.spl:199:filter:Lazy:tail-nil
  src/lib/gc_async_mut/array.spl:57:array_find:bool):tail-nil
  src/compiler/25.traits/trait_coherence.spl:103:check_orphan_rules:[CoherenceError]:tail-nil
  src/compiler/70.backend/gpu_intrinsics.spl:377:validate_gpu_intrinsic_args:has_GpuIntrinsicError:tail-nil
  src/lib/common/cert/x509_typed.spl:237:_xt_dn_cn:text:tail-nil
  src/lib/common/yaml/utilities.spl:88:yaml_mapping_get:any:tail-nil
  src/lib/common/yaml/utilities.spl:197:yaml_sequence_get:any:return-nil
  src/lib/common/yaml/utilities.spl:380:yaml_get_nested:any:return-nil
  src/lib/common/yaml/utilities.spl:383:yaml_get_nested:any:return-nil
  src/lib/common/date/calculate.spl:44:add_days:any:return-nil
  src/lib/common/date/calculate.spl:241:nth_day_of_month:any:return-nil
  src/lib/common/date/calculate.spl:243:nth_day_of_month:any:return-nil
  src/lib/common/date/calculate.spl:364:easter_date:any:return-nil
  src/lib/common/date/calculate.spl:387:good_friday:any:return-nil
  src/lib/common/date/calculate.spl:394:ash_wednesday:any:return-nil
  src/lib/common/date/calculate.spl:401:pentecost:any:return-nil
  src/lib/common/date/types.spl:115:from_ymd:any:return-nil
  src/lib/common/date/types.spl:128:from_days:any:return-nil
  src/lib/common/date/parse.spl:13:parse_iso8601:any:return-nil
  src/lib/common/json/validation.spl:63:json_deep_clone:any:return-nil
  src/lib/common/json/object_ops.spl:28:json_object_get:any:return-nil
  src/lib/common/json/object_ops.spl:31:json_object_get:any:tail-nil
  src/lib/common/json/object_ops.spl:264:json_object_find:bool) -> any:return-nil
  src/lib/common/json/object_ops.spl:268:json_object_find:bool) -> any:tail-nil
  src/lib/common/json/path_ops.spl:47:json_path_get:any:return-nil
  src/lib/common/json/path_ops.spl:54:json_path_get:any:return-nil
  src/lib/common/json/path_ops.spl:57:json_path_get:any:return-nil
  src/lib/common/json/array_ops.spl:34:json_array_get:any:return-nil
  src/lib/common/json/array_ops.spl:36:json_array_get:any:return-nil
  src/lib/common/json/array_ops.spl:213:json_array_last:any:return-nil
  src/lib/common/json/array_ops.spl:344:json_array_find:bool) -> any:return-nil
  src/lib/common/json/array_ops.spl:348:json_array_find:bool) -> any:tail-nil
  src/lib/common/json/types.spl:217:json_to_boolean:any:tail-nil
  src/lib/common/json/types.spl:233:json_to_number:any:tail-nil
  src/lib/common/json/types.spl:249:json_to_string:any:tail-nil
  src/lib/common/json/types.spl:265:json_to_array:any:tail-nil
  src/lib/common/json/types.spl:281:json_to_object:any:tail-nil
  src/lib/common/json/parser.spl:598:json_parse:any:tail-nil
  src/lib/tooling/ds_utils.spl:188:stack_get:any:return-nil
  src/lib/tooling/ds_utils.spl:195:queue_get:any:return-nil
  src/lib/common/saml/ir.spl:159:find_class:SamlClass:tail-nil
  src/lib/common/saml/ir.spl:166:find_enum:SamlEnum:tail-nil
  src/lib/common/saml/ir.spl:173:find_struct:SamlStruct:tail-nil
  src/lib/common/saml/ir.spl:180:find_function:SamlFunction:tail-nil
  src/lib/common/saml/parser.spl:96:_field_from:SamlField:return-nil
  src/lib/common/saml/parser.spl:99:_field_from:SamlField:return-nil
  src/lib/common/saml/parser.spl:155:parse_example_comment:SamlExample:return-nil
  src/lib/nogc_async_mut/concurrent/collections.spl:24:get:Any:tail-nil
  src/lib/nogc_async_mut/concurrent/collections.spl:145:get:Any:tail-nil
  src/lib/nogc_async_mut/concurrent/collections.spl:188:first_key:Any:return-nil
  src/lib/nogc_async_mut/concurrent/collections.spl:194:last_key:Any:return-nil
  src/lib/nogc_async_mut/concurrent/collections.spl:235:first:Any:return-nil
  src/lib/nogc_async_mut/concurrent/collections.spl:241:last:Any:return-nil
  src/lib/nogc_async_mut/web_framework/dispatcher.spl:127:dispatch:HttpResponseData:tail-nil
  src/lib/nogc_async_mut/http_client/request.spl:26:get_header:text:tail-nil
  src/lib/nogc_async_mut/http/url.spl:81:get_query_param:text:return-nil
  src/lib/nogc_async_mut/http/utilities.spl:17:parse_basic_auth:tuple:return-nil
  src/lib/nogc_async_mut/http/utilities.spl:28:parse_basic_auth:tuple:return-nil
  src/lib/nogc_async_mut/http/utilities.spl:51:parse_bearer_token:text:return-nil
  src/lib/nogc_async_mut/http/headers.spl:43:get_header:text:return-nil
  src/lib/nogc_async_mut/http/headers.spl:363:parse_range_header:tuple:return-nil
  src/lib/nogc_async_mut/http/headers.spl:369:parse_range_header:tuple:return-nil
  src/lib/nogc_async_mut/http/headers.spl:435:parse_multipart_part:tuple:return-nil
  src/lib/gc_async_mut/http_client/request.spl:26:get_header:text:tail-nil
  src/lib/gc_async_mut/http/url.spl:81:get_query_param:text:return-nil
  src/lib/gc_async_mut/http/utilities.spl:17:parse_basic_auth:tuple:return-nil
  src/lib/gc_async_mut/http/utilities.spl:28:parse_basic_auth:tuple:return-nil
  src/lib/gc_async_mut/http/utilities.spl:51:parse_bearer_token:text:return-nil
  src/lib/gc_async_mut/http/headers.spl:49:get_header:text:return-nil
  src/lib/gc_async_mut/http/headers.spl:302:parse_range_header:tuple:return-nil
  src/lib/gc_async_mut/http/headers.spl:308:parse_range_header:tuple:return-nil
  src/lib/gc_async_mut/http/headers.spl:377:parse_multipart_part:tuple:return-nil
  src/compiler/10.frontend/c_import/c_to_simple.spl:112:find_c_struct_by_match:CStruct:tail-nil
  src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:374:struct_construct_spread_base:HirExpr:return-nil
  src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:376:struct_construct_spread_base:HirExpr:return-nil
  src/compiler/55.borrow/borrow_check/mod.spl:166:convert_terminator:Terminator:tail-nil
  src/lib/nogc_sync_mut/lazy_val.spl:199:filter:Lazy:tail-nil
  src/lib/nogc_sync_mut/array.spl:57:array_find:bool):tail-nil
  src/compiler/70.backend/backend/backend_helpers.spl:278:backend_for_name:has_BackendKind:tail-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:116:_decode_base64_bytes:list:return-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:128:_decode_base64_bytes:list:return-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:136:_decode_base64_bytes:list:return-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:142:_decode_base64_bytes:list:return-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:182:http_basic_parse:tuple:return-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:187:http_basic_parse:tuple:return-nil
  src/lib/nogc_async_mut/http/auth/basic.spl:198:http_basic_parse:tuple:tail-nil
  src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:262:get_breakpoint:BreakpointInfo:tail-nil
  src/lib/gc_async_mut/http/auth/basic.spl:116:_decode_base64_bytes:list:return-nil
  src/lib/gc_async_mut/http/auth/basic.spl:128:_decode_base64_bytes:list:return-nil
  src/lib/gc_async_mut/http/auth/basic.spl:136:_decode_base64_bytes:list:return-nil
  src/lib/gc_async_mut/http/auth/basic.spl:142:_decode_base64_bytes:list:return-nil
  src/lib/gc_async_mut/http/auth/basic.spl:182:http_basic_parse:tuple:return-nil
  src/lib/gc_async_mut/http/auth/basic.spl:187:http_basic_parse:tuple:return-nil
  src/lib/gc_async_mut/http/auth/basic.spl:198:http_basic_parse:tuple:tail-nil
  src/lib/nogc_sync_mut/unsafe/maybe_uninit.spl:31:mu_assume_init:T:return-nil
  src/lib/nogc_sync_mut/http_client/request.spl:26:get_header:text:tail-nil
  src/lib/nogc_sync_mut/http/url.spl:81:get_query_param:text:return-nil
  src/lib/nogc_sync_mut/http/utilities.spl:17:parse_basic_auth:tuple:return-nil
  src/lib/nogc_sync_mut/http/utilities.spl:28:parse_basic_auth:tuple:return-nil
  src/lib/nogc_sync_mut/http/utilities.spl:51:parse_bearer_token:text:return-nil
  src/lib/nogc_sync_mut/http/headers.spl:43:get_header:text:return-nil
  src/lib/nogc_sync_mut/http/headers.spl:183:parse_range_header:tuple:return-nil
  src/lib/nogc_sync_mut/http/headers.spl:189:parse_range_header:tuple:return-nil
  src/lib/nogc_sync_mut/http/headers.spl:258:parse_multipart_part:tuple:return-nil
  src/lib/nogc_sync_mut/src/table.spl:93:min:Any:return-nil
  src/lib/nogc_sync_mut/src/table.spl:103:max:Any:return-nil
  src/lib/nogc_sync_mut/cli/flags.spl:32:find_flag_by_long:tuple:tail-nil
  src/lib/nogc_sync_mut/cli/flags.spl:42:find_flag_by_short:tuple:tail-nil
  src/lib/nogc_sync_mut/cli/flags.spl:52:find_option_by_long:tuple:tail-nil
  src/lib/nogc_sync_mut/cli/flags.spl:62:find_option_by_short:tuple:tail-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:116:_decode_base64_bytes:list:return-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:128:_decode_base64_bytes:list:return-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:136:_decode_base64_bytes:list:return-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:142:_decode_base64_bytes:list:return-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:182:http_basic_parse:tuple:return-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:187:http_basic_parse:tuple:return-nil
  src/lib/nogc_sync_mut/http/auth/basic.spl:198:http_basic_parse:tuple:tail-nil
  src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:262:get_breakpoint:BreakpointInfo:tail-nil
  src/lib/nogc_sync_mut/debug/remote/dwarf.spl:42:addr_to_source:SourceLocation:return-nil
  src/lib/nogc_sync_mut/debug/remote/dwarf.spl:48:addr_to_source:SourceLocation:return-nil
  src/lib/nogc_sync_mut/debug/remote/dwarf.spl:52:addr_to_source:SourceLocation:return-nil
  src/lib/nogc_sync_mut/debug/remote/dwarf.spl:57:addr_to_source:SourceLocation:return-nil
  src/lib/nogc_sync_mut/debug/remote/dwarf.spl:91:detailed_location:SourceLocation:return-nil
  src/lib/nogc_sync_mut/src/core/random.spl:76:choice:Any:return-nil
  src/lib/nogc_sync_mut/src/core/random.spl:83:choice:Any:return-nil
  src/lib/nogc_sync_mut/src/core/regex.spl:170:_match_pattern:Match:return-nil
  src/lib/nogc_sync_mut/src/core/regex.spl:181:_match_pattern:Match:return-nil
```

Class (c) is **not** fixed here: each site needs its own callers read to choose
`-> T?` versus a total body, and 187 of them is a separate lane. None of them
is reachable from the dynamic sweep below, which is why the sweep is green.

## Dynamic sweep (strict seed)

Seed: `/mnt/data/.cargo-target-epc/release/simple` (pristine origin/main build,
enforces the contract). Shards run ≤2 concurrent, output grepped for
`non-optional return contract` and `E-SFFI-016`.

| shard | spec output lines | `non-optional return contract` / `E-SFFI-016` hits |
|---|---|---|
| test/01_unit/compiler/frontend | 3460 | 0 |
| test/01_unit/compiler/hir | 3520 | 0 |
| test/01_unit/compiler/driver | 3171 | 0 |
| test/01_unit/lib/common | 3859 | 0 |
| test/01_unit/lib/nogc_sync_mut | 3260 | 0 |

**Zero dynamic hits.** Two caveats stated rather than glossed: `compiler/hir`
was cut off by the shard's own 3000s `timeout` (rc=143) after 3520 lines, and
the non-zero shard exit codes (rc=1, rc=42) are the **pre-existing SSPEC
documentization score gate** ("SSPEC score gate: 38 below 80"), not contract
aborts — every shard log greps to 0 for both the message and the code.

A green sweep is consistent with, but weaker than, the static guard: these
directories simply never drove any of the 10 wrappers down its nil path. The
guard is the load-bearing evidence; the sweep only confirms no *additional*
shape was missed by the static scan in these five trees.

## Guard

`scripts/check/check-non-optional-nil-return.shs` — fail-closed, `--selftest`
(5 fixtures: the incident shape must FAIL; an optional return, a `??`-total
body, and a wrapper forwarding a total extern must all PASS; an empty tree must
yield 0 wrappers so the caller is forced to ERROR), verdict as the last stdout
line, ERROR on 0 items in either derived set.

    PASS — 1572 wrapper(s) checked against 138 nil-capable extern(s), 0 returning nil through a non-optional type

Scope is `--root`-based (`src/compiler` + `src/lib`), not a commit range:
this is a property of a tree, and a newly nil-capable *extern impl* can break a
wrapper the push never touched. Widen it to all of `src/` once the out-of-scope
class-(b) sites above are fixed.

## Reproduce spec

`test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl`
(mirrored byte-identically at `test/unit/...`) — 5 examples driving
`file_read_lines` down two distinct read-failure paths and `try_recv` /
`channel_try_recv_by_id` down the empty-channel path, plus a neighbor case
proving a real value still round-trips after a nil poll. On the strict seed
pre-fix the first two examples aborted the whole file; post-fix 5/5 pass.

## Resolution, 2026-08-21

### The 187-site census over-counted; the live number was 172

The census parsed the declared return type by splitting the `fn` line on `:`
and taking field 2, which mangles three shapes and reports all three as
non-optional:

- a TUPLE return type (`-> ({text: text}, i64)?` was read as `({text` -- the
  `?` was in the part that got cut off, so an ALREADY-OPTIONAL function was
  listed as an offender; `read_text_dict` and `_read_def_suffix` are this),
- a closure PARAMETER carrying its own `->` (`predicate: fn(Any) -> bool`)
  being mistaken for the function's return type -- `array_find` in all three
  `array.spl` mirrors has no declared return type at all,
- a `->` nested inside a GENERIC return type (`-> Option<fn() -> i64>`).

A `nil` that is the tail of a nested closure rather than of the function body
(`lazy_val.spl:199`, inside the thunk passed to `Lazy.new`) was also counted.
The guard's class (c) leg parses the return type at paren/angle depth 0 and
does not have these false positives. Live counts on the corrected scan:
172 in `src/compiler` + `src/lib`, 24 in `src/app`, 0 in
`src/runtime/simple_core`.

### Sites fixed

| batch | commit | `T?` | made total | other | not fixed |
|---|---|---|---|---|---|
| `src/compiler/**` | `2c8949e8f03` | 34 | 3 | — | 0 |
| `src/compiler_rust/lib/std/**` (class (b)) | `79e45561d1e` | 2 | 3 | — | 0 |
| `src/lib/common/**` + math/editor/tooling | `71255f9d3c2` | 19 | 1 | 2 bogus annotations removed | 10 |
| `src/lib/{nogc_sync,nogc_async,gc_async}_mut/**` | `eb73528fc34` | 31 | 1 | — | 0 |
| `src/app/**` (class (c) + class (b)) | `3bfd830c898` | 25 | 2 | — | 0 |

`T?` was chosen wherever a caller already distinguished absent from a default
(`if x != nil`, `x!`, `== nil`) or the docstring already said nil meant "not
found"; otherwise the body was made total with a valid default. Two
declarations (`option_filter -> bool`, `result_map -> i64`) were simply wrong
about what their function returned -- they are generic passthroughs -- and the
annotation was removed rather than invented.

### The 10 sites that are NOT fixed, and why

`json_parse` and the nine `date/` constructors (`from_ymd`, `from_days`,
`parse_iso8601`, `add_days`, `nth_day_of_month`, `easter_date`, `good_friday`,
`ash_wednesday`, `pentecost`) all return a TUPLE through `-> any`. `-> any?` is
the correct declaration and nil there is a real "invalid date" / "malformed
JSON" outcome. Widening them makes the strict seed wrap the returned tuple in
an Option enum, so every downstream `.0`/`.1` access fails with "tuple index
access on non-tuple type enum": measured 16 failures against the 5 the
violation itself causes. That is the defect tracked in
`doc/08_tracking/bug/free_fn_optional_wrap_2026-06-26.md`, and these sites
unblock the day it is fixed.

They are recorded in `scripts/check/non_optional_nil_return_classc_baseline.txt`
with that reasoning, and the guard FAILs on any NEW site and on any baselined
site that stops being an offender (a stale baseline is how a ratchet silently
stops ratcheting). The baseline must shrink to empty.

### Guard

`scripts/check/check-non-optional-nil-return.shs` now has a class (c) leg and
scans `src/compiler`, `src/lib`, `src/app` and `src/runtime/simple_core`.
Verdict:

    PASS — 1705 wrapper(s) checked against 138 nil-capable extern(s),
    12475 file(s) scanned for hand-written nil returns against a 10-entry
    baseline (0 new, 0 stale), 0 returning nil through a non-optional type

Three class (b) false-positive sources were found and fixed while widening the
roots, each with a selftest fixture (19 fixtures, fatal, run before every scan):

- the offender join was `grep -F -f`, a SUBSTRING match, so a nil-capable
  shorter name convicted a wrapper forwarding a longer total one --
  `rt_vulkan_free` vs `rt_vulkan_free_buffer`, which is why `vulkan_port_free`
  was reported. It is now an exact-name join on the extracted callee.
- the nil-capability scan kept a Rust fn "open" past its own closing brace, so
  a `Value::Nil` belonging to whatever followed was attributed to it.
- `src/runtime/simple_core` is the pure-Simple implementation OF the runtime
  primitives, so its `rt_tuple_get` calls the `fn rt_array_get` defined in the
  same file, not the extern of that name. A same-file Simple definition now
  shadows the extern.

## Fourth wrapper: compiler/00.common/config.spl `env_get` (2026-08-21, later same day)

A strict-seed `native-build --source src/app --entry-closure --entry
src/app/cli/bootstrap_main.spl` died before its first `[build] parse` line
with `error: semantic: nil is forbidden by the non-optional return contract of
'env_get'`. `src/compiler/00.common/config.spl:7-9` declared its own inline
`env_get(key: text) -> text` (kept local "to avoid an L0->L7 layer violation"),
forwarding `rt_env_get(key)` directly with no nil check -- the same defect
shape as the three wrappers fixed earlier today (`7825f01def2`). It is called
by `CompilerConfig.from_env()` (`driver_types.spl:506`) for `SIMPLE_PROFILE` /
`SIMPLE_LOG` / `SIMPLE_DETERMINISTIC` / `SIMPLE_COVERAGE`, right at driver
startup before parsing -- matching the "dies before parse" symptom exactly.
All 5 call sites in that file already used the `if val x = env_get(...)`
optional-safe pattern, so no caller changes were needed.

Fix: `extern fn rt_env_get(key: text) -> text?` / `fn env_get(key: text) ->
text?:` (both widened; the callers were already written for an optional).

### Why the guard missed it

`rt_env_get`'s Rust impl (`interpreter_extern/system.rs:332`) has no literal
`Value::Nil` in its own body -- it calls a shared conversion helper,
`runtime_to_value(result)` (`interpreter_extern/atomic.rs:531`), which is the
one that actually returns `Value::Nil`. `derive_nil_externs`'s `nil.awk` only
scanned for `Value::Nil` textually within a function's own body span, so a
one-hop delegator was invisible to it -- exactly the shape that let
`rt_env_get` (and, once fixed, 45 *other* pre-existing offenders of the same
shape) escape detection.

Fixed the guard: added `call.awk` (extracts `<caller> <callee>` pairs from a
plain `identifier(` textual scan) and a bounded (5-iteration) fixpoint closure
in `derive_nil_externs` that adds a fn to the nil-capable set if it calls
another fn already known to be nil-capable. Selftest still green (19
fixtures, unchanged).

This closure immediately surfaced 46 pre-existing class (b) offenders (mostly
other `env_get`/`env_cwd`/`args`/`file_mmap_read_bytes`/mutex-`.lock()`-style
wrappers over `rt_*` calls that delegate through `runtime_to_value` or a
similar helper) that were always real but had never been caught. They cannot
all be fixed in one change, so -- matching the class (c) baseline convention
already in this file -- added a class (b) baseline ratchet:
`scripts/check/non_optional_nil_return_classb_baseline.txt` (46 entries,
`<rel-file>:<fn>:<body>` keyed, line-number-free so it doesn't churn on
unrelated edits), with the same FAIL-on-new / FAIL-on-stale rules as the
class (c) leg. The one entry actually fixed here (`config.spl:env_get`) is
NOT in the baseline (dropped out naturally once fixed). Guard now:

    PASS — 1646 wrapper(s) checked against 185 nil-capable extern(s)
    (46 baselined class (b)), 12475 file(s) scanned for hand-written nil
    returns against a 10-entry baseline (0 new, 0 stale), 0 returning nil
    through a non-optional type

### Reproduce spec

`test/01_unit/compiler/config/compiler_config_spec.spl` (mirrored to
`test/unit/compiler/config/compiler_config_spec.spl`), new `describe
"CompilerConfig.from_env"` block: calls `CompilerConfig.from_env()` under the
strict seed. Confirmed FAILing pre-fix with the exact reported message
(`semantic: nil is forbidden by the non-optional return contract of
'env_get'`) and PASSing post-fix (32/32 examples).

### Probe result

Re-ran `SIMPLE_CACHE_SCOPE=envget <strict-seed> native-build --source src/app
--entry-closure --entry src/app/cli/bootstrap_main.spl -o
/mnt/data/seedperf/stage1.envget --threads 1`: no `env_get` non-optional
contract error. Progressed through `load_sources` (958/958 files) and
`source_closure` (666/666 files) cleanly in ~23s before being killed
deliberately (probe purpose only, not a full build).
