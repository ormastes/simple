<!-- codex-architecture -->
# Web iframe `srcdoc` through Draw IR

Status: proposed; implementation blocked on executable TDD evidence

Requirements: REQ-WEB-BROWSER-002/003/004/019/021 and
NFR-WEB-BROWSER-012/017 from the production-hardening requirements.

## Problem

The software renderer recognizes `<iframe srcdoc>`, but
`_web_render_child_pixels` recursively creates a `[u32]` child framebuffer and
`_web_paint_iframes` blits it into the parent. The canonical retained path,
`_simple_web_layout_compose_retained`, emits only the parent
`DrawIrComposition`, so Engine2D loses iframe content.

The legacy pixel helper has five callers:

1. `simple_web_layout_render_html_software_pixels_traced`
2. `simple_web_layout_render_html_software_result`
3. `simple_web_layout_render_html_gpu_frame`
4. `simple_web_layout_render_html_software_pixels_at_scroll`
5. recursive `_web_render_child_pixels`

Pre-rasterizing the child as a `DRAW_IR_COMMAND_IMAGE` would hide child
semantics, clips, ordering, and provenance. It is not an accepted bridge.

## Decision

Keep the flat Draw IR schema. Add one common value transform in
`src/lib/common/ui/draw_ir.spl`:

```simple
fn draw_ir_embed_composition(
    child: DrawIrComposition,
    offset_x: i32,
    offset_y: i32,
    ancestor_clip: DrawIrRect,
    surface_prefix: text,
    component_id: text,
    layer_base: i32
) -> [DrawIrBatch]
```

It returns cloned child batches in original order. For each batch:

- global origin is `(offset_x + embedding.x, offset_y + embedding.y)`;
- dimensions, backend, source, and opacity are preserved;
- surface/batch IDs are prefixed with the iframe's stable component ID;
- layer is `layer_base + embedding.layer`;
- inherited clip is translated to batch-local coordinates and intersected
  with `[0,0,width,height]`;
- every command clip becomes
  `intersection(command.clip_rect, inherited_local_clip)`;
- all other command fields remain unchanged.

Reuse `draw_ir_rect_translate` and `draw_ir_rect_intersection`. One private
exact-copy helper is enough; add no hierarchical IR or command-builder family.

Engine2D already translates commands by the batch origin, applies the batch
rectangle, intersects translated command clips, and composites batches in
array order. A rebased batch plus inherited command clip therefore represents
ancestor offsets and rectangular clips without a nested executor or image.

The child composition is inserted at the iframe paint position: flush the
parent command segment after the iframe owner's final command, insert child
batches, then continue later siblings. Never append all children at the end.

## Web owner

Refactor the parse/style/layout/compose sequence into one private owner:

```simple
fn _simple_web_layout_compose_document(
    html: text,
    width: i32,
    height: i32,
    extra_rules: Rules,
    depth: i32,
    deadline_us: i64,
    vector_fonts: bool,
    animation_time_ms: i64,
    scroll_y: i32,
    overlay: BrowserTextInputOverlay,
    animation_instances: [BrowserCssAnimationInstance],
    images: [SimpleOsHostGpuImageResource]
) -> SimpleWebLayoutDrawIrResult
```

Top-level wrappers pass empty rules, depth `0`, and their resolved deadline.
Iframe children pass decoded `srcdoc`, content-box dimensions, parent `Rules`
only for `space=shared`, `depth + 1`, half the positive remaining deadline,
the parent's animation time/vector-font/images, zero scroll, empty overlay,
and a separate empty animation-instance set.

Extra parent rules precede the child's own extracted rules, preserving child
override order. The owner installs the explicit deadline only for that call
and restores the parent deadline on every return.

`_simple_web_layout_compose_retained` receives depth/deadline, builds the
existing ancestor clip cache, and invokes this owner for visible iframes.

### Material evidence

Draw IR carries semantic commands, not transient material caches. Keep
`material_entries`, `material_counts`, `cpu_material_nodes`, and
`solid_material_nodes` document-local so retained rerender can reuse the
current document's node indices. Do not rebase child-local node indices.

Combine `SimpleWebLayoutMaterialWitness` values after child insertion. For CPU
and solid evidence independently:

1. order is parent document first, then children in exact iframe
   batch-insertion order (nested children are already folded into each child);
2. count is the checked sum of contributor counts;
3. omit zero-count contributors;
4. no child contributor preserves the parent count/hash byte for byte;
5. one child contributor with a zero parent preserves the child count/hash;
6. otherwise hash `v1\n<count>:<64-character-sha256>\n...` with
   `sha256_text`.

The final `material_witness` and initial `material_fallback` use the combined
witness. Engine2D counts the same flattened batches, so backend provenance
compares against the combined count/hash. No material state enters Draw IR.

## Admission and fail-closed rules

- Past `WEB_IFRAME_DEPTH_CAP` or an expired deadline: emit the existing opaque
  `WEB_IFRAME_PLACEHOLDER` rectangle; do not parse the child.
- Missing `srcdoc`: compose the empty white child, matching current behavior;
  fallback DOM descendants remain hidden.
- Hidden/empty/fully clipped boxes emit no child batches.
- `src` never performs file/network I/O.
- Script sharing, navigation, and child input routing remain unsupported.
- Fractional-opacity or parent-sampling ancestor groups fail closed with the
  placeholder until Draw IR has a real group primitive. Independently applying
  opacity to flat batches is incorrect.
- No iframe `DRAW_IR_COMMAND_IMAGE`, `[u32]` child buffer, private Engine2D
  path, or parallel Web IR.

## Ancestor clip

For iframe content rect `F`, current layout ancestor clip `A`, and accumulated
origin:

```text
visible = intersection(A, F)
child-global-clip = translate(visible, accumulated-origin)
batch-local-clip = translate(child-global-clip, -batch-global-origin)
effective-command-clip =
    intersection(command.clip_rect, batch-local-clip)
```

Zero-area intersections stay present zero-area clips. They must never become
`draw_ir_no_rect()`, because absence means unbounded.

## Performance and migration

The transform is O(child batches + commands) and allocates only final flat IR.
It removes recursive `cw * ch` child framebuffers. Existing depth/deadline
authorities remain; add no cache or new offscreen pool.

Keep direct pixels as the oracle until a focused corpus proves exact parity.
Migrate the five callers in the design order. Delete `_web_blit_child`,
`_web_render_child_pixels`, and `_web_paint_iframes` only after caller five.

## Risks

- Wrong insertion order paints a child above a later overlapping sibling.
- Losing a present zero-area clip escapes an overflow ancestor.
- Flat batches cannot preserve ancestor fractional group opacity.
- Child material witnesses must follow child batch-insertion order while
  parent-only hashes remain unchanged.
- Existing docs claiming local `src` support are stale; production is
  `srcdoc`-only and authority must not broaden.

## Sandboxed `srcdoc` child authority (RED)

The current `_web_render_child_pixels` recursion only decodes an attribute into
an offscreen bitmap.  It creates neither a `BrowserSession` child document nor
a script, request, navigation, or input authority.  Those features stay
unsupported until this contract is implemented; Draw IR flattening must not
quietly turn the hidden renderer recursion into a security boundary.

### Identity, URL, base, and origin

Use one typed `BrowserChildIdentity`:

```text
(parent_dom_generation, iframe_route: DomNodeRoute, child_frame_generation)
```

These are three different lifetimes. `parent_dom_generation` invalidates every
child after a top-document replacement. `child_frame_generation` advances for
that iframe on `srcdoc`, sandbox/base-policy, or child-document replacement.
`HostedBrowserRendererProcess.generation` is the process generation carried by
the outer SBR2 hop; it is never a DOM or child-frame generation.

The child document URL is always `about:srcdoc`. Its fallback base is the
parent's effective document base captured when the child commits; the first
valid child `<base href>` may derive the child's effective base through the
existing URL resolver. Fetch and navigation resolve only from that effective
base. URL, base, and origin are separate fields and cannot be reconstructed
from `about:srcdoc`.

Security identity uses the existing typed `Origin`, never serialized origin
text. An absent `sandbox` attribute is unrestricted by that attribute; a
present empty attribute denies all. Known tokens only remove their named
restriction, unknown tokens never broaden, and malformed/oversized token input
fails closed. Iframe sandbox and CSP sandbox are intersected deny-wins. Without
`allow-same-origin`, the child gets a fresh `OpaqueOriginSource.next()` value;
two sibling opaque children must therefore differ. With it, the child inherits
the creator's typed origin. Same-origin still exposes no parent DOM/chrome
object until a separately designed cross-frame API exists.

### Trusted ledger and two capabilities

For the isolated renderer, `HostedBrowserRendererProcess` is the sole trusted
child-record and permit ledger. The worker `BrowserSession` holds a mirror for
render/script dispatch only and cannot mint, extend, or retire authority.

Existing SBR2 is the per-hop process command/reply capability bound to process
generation, root command, and wire request. It does not authorize a child
operation. A separate `BrowserChildPermit` is one-use and bound to the complete
child identity, intent ID/kind, normalized target, and that outer SBR2 tuple.
It is issued only after host validation, consumed immediately before the one
fetch/navigation/input mutation, and cleared on success or failure. Child code
never receives its opaque 32-lowercase-hex value.

The isolated inner schemas, carried only inside a valid outer SBR2 payload,
are frozen as:

```text
SBCI1\t<parent-dom-gen>\t<child-frame-gen>\t<intent-id>\t<direction-len>\t<kind-len>\t<frame-route-len>\t<target-route-len>\t<url-ref-len>\t<method-len>\t<headers-len>\t<body-len>\n
<direction><kind><frame-route><target-route><url-ref><method><headers><body>

SBCP1\t<parent-dom-gen>\t<child-frame-gen>\t<intent-id>\t<kind-len>\t<frame-route-len>\t<target-route-len>\t<normalized-url-len>\t<method-len>\t32\n
<kind><frame-route><target-route><normalized-url><method><permit>
```

Directions are exactly `child-to-host` or `host-to-child`; kinds are exactly
`script`, `fetch`, `navigate-self`, `navigate-top`, `pointer`, `key`, or
`text`. Decimal fields are canonical positive integers. Lengths are UTF-8 byte
lengths; route/URL/method/header/body and total payload reuse existing browser
renderer limits. NUL/control text, overflow, trailing bytes, unknown values,
malformed UTF-8, and oversized fields reject before ledger or DOM/network
mutation. Base URL, effective `Origin`, sandbox policy, process generation,
root request, and wire request are host-ledger data and are deliberately absent
from `SBCI1`; the worker cannot assert them.

For `HostedWebContentSession` there is no renderer wire and no SBR2 claim. It
passes the same typed `BrowserChildIntent` through the shared session broker;
the in-process broker creates and consumes the same scoped local permit around
one validated mutation. Hosted/isolated parity compares policy and effects,
not transport bytes.

Retire all child records/permits on child or parent replacement, iframe
removal, sandbox/base-policy change, Stop, Close, site swap, process failure,
or process-generation change. Script requires `allow-scripts`; fetch uses the
host-ledger base/origin plus CSP/CORS/cookie policy; navigation defaults to the
child and needs `allow-top-navigation` for the parent; input must match the
current child `DomNodeRoute`. Every check precedes mutation.

This reuses `BrowserSession`, `HostedBrowserRendererProcess`,
`BrowserCspSandboxPolicy`, `Origin`/`OpaqueOriginSource`, URL helpers,
`DomNodeRoute`, and the outer SBR2 broker. It adds no Web IR, nested Engine2D
executor, ambient child network facade, or worker-side issuer.
