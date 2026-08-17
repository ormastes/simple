# Interpreter nested-field-assignment rejection broke the BeDomNode CSS cascade

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Date: 2026-08-15. Status: WORKED AROUND in dom.spl; underlying interpreter
limitation still open.

## Symptom
Every path through `BeDomNode.set_style` / `inherit_style_into`
(`src/lib/gc_async_mut/gpu/browser_engine/dom.spl`) failed at runtime under the
tree-walk interpreter (the `bin/simple test` engine) with:

    semantic: invalid assignment: cannot assign field on non-object value

This silently broke the whole `<style>`-block cascade:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.spl`
was 0/8 RED, and any spec driving `process_style_blocks` /
`apply_css_rules_to_tree` over hand-built or tree-builder DOMs failed the same
way.

## Cause
The interpreter rejects nested field assignment through an object-valued field
(`self.style.color = v`, `c.style.font_size = x`). `set_style` had ~40 such
writes and `inherit_style_into` had 6.

## Fix (workaround)
Rewrote both functions to the supported pattern: copy the sub-object to a
local (`var s = self.style`), mutate the local, assign the whole sub-object
back once (`self.style = s`). Verified: `style_longhand_cascade_spec.spl` 8/8
green, `style_block_coverage_closure_spec.spl` 28/28 green.

## Unblock condition for closing
Either the interpreter accepts nested field assignment again (then the
workaround is merely stylistic), or the pattern is formally documented as
unsupported in `.claude/rules/language.md` (it currently is listed) and a lint
flags remaining occurrences — `grep -rn '\.style\.[a-z_]* =' src/lib` and
similar nested-write patterns elsewhere in browser_engine may still be latent.

## RESOLVED 2026-08-15 (later same day)
The underlying interpreter defect is FIXED: `node_exec.rs` Case 3 nested field
assignment (`a.b.c = v`) now handles `Value::ClassInstance` receivers (inner
ClassInstance via set_field; inner Object mutate+write-back). Verified by the
CUDA probe path repro (`self.session.module_cache = loaded` in
backend_cuda.spl:428) and `engine2d_backend_matrix_spec.spl` going 7/16 -> 16/16.
The dom.spl workaround can be unwound when convenient.
