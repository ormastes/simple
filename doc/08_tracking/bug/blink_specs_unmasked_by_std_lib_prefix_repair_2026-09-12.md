# Blink: 3 spec pairs fail for real once the `std.lib.` import prefix is repaired

- Status: OPEN (2026-09-12)
- Found: 2026-09-12, BUGFIX-5, repairing
  `spec_imports_declared_nowhere_2026-08-04` (see that record's 2026-09-12 section)
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  (Rust bootstrap seed, sha256 `3d120a6f`), base `89c5e3f865d`
- Area: `src/lib/blink/paint/**`, `src/lib/blink/**` hit testing, plus one spec
  parse error

Until 2026-09-12 these files imported `use std.lib.<x>`, which resolves nowhere,
so they executed **0 examples** and their failures were invisible. The import
prefix is now fixed; these are what was underneath. They are pre-existing
defects, not regressions from that repair, and they are deliberately left RED.

## Repro

```
bin/simple test test/01_unit/lib/blink/paint_tree_walker_spec.spl --no-session-daemon
bin/simple test test/01_unit/lib/blink/hit_test_spec.spl --no-session-daemon
bin/simple test test/01_unit/lib/blink/css_tokenizer_spec.spl --no-session-daemon
```

(each has an identical twin under `test/unit/lib/blink/`.)

## The three

1. **`paint_tree_walker_spec` — 4 passed, 2 failed.** The walker emits no
   `DrawRect` ops: "background color with a>0 emits a DrawRect op in the canvas'
   recorder" gets `expected 0 to be greater than 0`, and "full walk of 2 boxes
   emits 2 DrawRect ops (parent + child)" gets `expected 0 to equal 2`. The
   transparent-background example passes, so the walk runs and produces nothing.
2. **`hit_test_spec` — 5 passed, 2 failed.** `semantic: function
   `point_in_rect` not found`. Same shape as
   `serial_mcp_detect_tool_name_red_2026-08-09`: the spec imports a helper that
   is not declared in the module it names. Whoever owns blink hit testing should
   decide whether the helper was renamed or never landed.
3. **`css_tokenizer_spec` — parse error, 0 examples.** `parse: Unexpected token:
   expected expression` — the file does not parse at all, so it is dropped
   (`reason=parse-error`). Unrelated to the import prefix; it failed to parse
   before the repair too.

## Not fixed here

Out of BUGFIX-5's shard scope. (1) needs a product-side investigation of the
paint recorder; (2) needs an ownership decision, not a repair; (3) needs the
spec's own syntax fixed and then its examples judged.
