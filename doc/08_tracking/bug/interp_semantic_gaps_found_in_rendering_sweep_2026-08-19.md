# Interpreter/semantic gaps found during rendering sanitize sweep (2026-08-19)

**Status:** RESOLVED (per record's own account; not independently re-verified 2026-09-12)

Three concrete product gaps surfaced while sanitizing
`test/02_integration/rendering/`; each was worked around in-lane, but the
underlying defect is real and should be fixed at the source.

## 1. `[] as [T]` cast target rejected by the interpreter semantic layer

`line_boxes: [] as [LayoutLineBox]` in
`src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl`
died with `semantic: type mismatch: unsupported cast target type:
Array { element: Simple("LayoutLineBox"), size: None }` under the deployed
seed. Casting an empty array literal to a typed array is a short, safe,
compact form and should work. Workaround applied: a typed local
(`var no_line_boxes: [LayoutLineBox] = []`). Fix the cast, or reject it at
parse time with a clear message.

## 2. `rt_write_u32s_to_raw_checksum` unregistered in the interpreter extern dispatcher

The symbol is defined in the runtime
(`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs:1219`, and in
the deployed seed per `nm`), but `interpreter_extern/mod.rs` registers only
`rt_write_u32s_to_raw`, so every interpreted call died with
`semantic: unknown extern function: rt_write_u32s_to_raw_checksum`
(web_layout_cuda_live_spec, 6/6 red). Workaround: implemented
`raw_write_u32s_checksum` in pure Simple over the registered bulk write
(`src/lib/nogc_sync_mut/ptr/raw.spl`), checksum computed in Simple with the
same modulus contract. `rt_write_fill_u32s_to_raw_checksum` is likely
unregistered too (still declared, currently unexercised on the interpret
path). Proper fix: register both in the dispatcher (seed change, off-limits
to this lane).

## 3. `env_get(unset) ?? default` never fires — returns "" not nil

`env_get("WINIT_TEXT_FIXTURE_ROOT") ?? "."` in
`winit_ordered_committed_text_spec.spl` yielded `""`, turning every fixture
path into an absolute `/src/...` and making all three tests fail with empty
file reads. Either `env_get` should return nil for an unset variable, or the
quick-reference should warn that `??` cannot be used with it. Workaround:
explicit empty-string guard in the spec.

## Triage 2026-09-12
Body appears to state resolution; not independently re-run in this pass (rule D bulk pass). Older-than-45-days threshold does not apply (record is newer than 2026-07-29). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
