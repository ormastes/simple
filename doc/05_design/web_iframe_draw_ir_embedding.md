<!-- codex-design -->
# Detail design: Web iframe Draw IR embedding

Architecture: `doc/04_architecture/web_iframe_draw_ir_embedding.md`

Status: RED / pre-migration. The candidate source/spec/manual exist, but the
authenticated focused parity run crashed (`exit 139`); compatibility callers
remain on the established pixel/blit path.

## Minimal source changes

1. `src/lib/common/ui/draw_ir.spl`: add `draw_ir_embed_composition` and one
   private command copy-with-clip helper; reuse existing rect operations.
2. `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:
   `_simple_web_layout_compose_document` scopes/restores child deadlines;
   retained composition carries depth, segments commands, and inserts children
   in paint order.
3. `simple_web_html_layout_renderer_paint_layout.spl`: keep the established
   pixel/blit helpers during parity; delete them only after the qualified
   corpus passes and callers are migrated.
4. Add `test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl`
   and its mirrored zero-stub manual.

No Engine2D change is planned. A required executor change means the flat
transform contract was implemented incorrectly.

## Producer algorithm

Keep aligned `commands/command_owner_nodes` from `_html_draw_ir_commands`.

1. Build `last_command_by_owner`.
2. Append commands in paint order to the current parent segment.
3. After an iframe owner's final command, flush the segment; compute its
   border/padding content rect and intersection with
   `paint_clip_at(ancestor_clip_cache, iframe_index)`.
4. Hidden/empty intersection: emit nothing. Failed depth/deadline/group
   admission: emit clipped placeholder. Otherwise compose the child and append
   `draw_ir_embed_composition(...)`; append its already-nested material witness
   to the ordered child-witness list at the same point.
5. Continue later siblings and flush the tail.

Segment IDs are `html-layout` plus a monotonic segment index. Iframe prefixes
use `_html_draw_ir_component_id` plus depth. Add no hash/cache key.

The existing fractional-opacity partition remains unchanged without iframes.
An iframe inside it is a fail-closed placeholder for this tranche.

After segmentation, `_simple_web_layout_merge_material_witness` folds the
parent witness followed by child witnesses in insertion order. It sums CPU and
solid counts separately and hashes the architecture's framed
`count:sha256` sequence only for multiple nonzero contributors. Raw
entries/counts/node arrays stay parent-document local for retained rerender;
child node indices are never rebased. The combined witness supplies final
provenance and backend execution checks.

## Deadline

```text
remaining = parent_deadline_us - now_us
child_deadline = now_us + remaining / 2
```

If remaining is non-positive, emit placeholder. Otherwise save the current
deadline, install the child deadline, compose, and restore. No retry or sleep.

## Modern SSpec TDD matrix

Frozen displayed steps:

- `Compose iframe srcdoc through Web semantics and Draw IR`
- `Preserve iframe paint order and ancestor clipping`
- `Bound nested iframe work and fail closed`
- `Embed the iframe composition without a pixel blit`

| Scenario | Semantic/layout | Draw IR | Engine2D/pixels | Control |
|---|---|---|---|---|
| basic `srcdoc` | replaced iframe, fallback absent, exact content box | child `html_ast` batches, stable prefixed IDs, zero iframe IMAGE commands | child color only inside box | parent marker/outside unchanged |
| later overlapping sibling | source paint order | child batches precede later sibling | sibling wins overlap | reversed order reverses winner |
| overflow/negative origin | exact ancestor/content intersection | every child command has present local clip | zero child color outside intersection | unclipped count is larger |
| nested depth 2 | two decoded child documents | accumulated rebased origins | deepest unique color visible | no image resource |
| depth 4 | fourth child not parsed | one capped placeholder | placeholder; deepest color zero | depth 3 renders |
| expired deadline | no child parse/layout | placeholder only | bounded deterministic output | live deadline renders |
| separate/shared CSS | parent style absent/present | exact child style metadata | unique color absent/present | child own declaration wins |
| empty `srcdoc`/fallback | fallback hidden | empty child canvas, no fallback commands | white child | fallback color zero |
| external `src` | no resource authority | no external command | deterministic empty child | ledger unchanged |
| fractional ancestor | unsupported group | placeholder, no independent-alpha child batches | fail-closed pixels | opaque renders |
| child material | child material stays document-local | combined count/framed hash follows child insertion order; no transient IR fields | provenance matches Engine2D material execution | parent-only hash is byte-identical |
| retained scroll | stable IDs, shifted box once | no duplicate offset; clip shifts | fresh/retained checksum equal | zero-scroll baseline |
| five caller parity | identical semantic/layout input | canonical composition source | exact supported-corpus pixels/checksum | mismatch blocks migration |

Use only canonical matchers. The manual shows the first three flows and folds
matrix cases. Initial missing helpers call `fail(...)`; never `pass_todo` or a
constant assertion.

## Parity retirement gate

Production compatibility entrypoints remain on the pixel/blit path. The public
diagnostic helper exposes those established pixels for the focused comparison.
Run the focused basic and clipped corpus once with `--assert-ran`; only after
that parity gate may callers migrate and only then delete
`_web_blit_child`, `_web_render_child_pixels`, and `_web_paint_iframes`.

## Verification boundary

Use an admitted current pure-Simple CLI that supports `test`, then run the
focused spec with the interpreter, session-daemon/cache disabled,
`--assert-ran`, and `--fail-fast`; then generate its manual. No Rust seed or
renderer-wide suite. Static review alone remains RED.

## Sandboxed child-document handoff (RED)

Before enabling child script, request/navigation, or input, replace the hidden
`_web_render_child_pixels` assumption with one child record keyed by
`BrowserChildIdentity(parent_dom_generation, iframe_route,
child_frame_generation)`. It stores `document_url = about:srcdoc`, captured
fallback base, resolved effective base, typed `Origin`, intersected
`BrowserCspSandboxPolicy`, and current process generation. Layout receives only
already-admitted child semantic output.

In isolated mode, `HostedBrowserRendererProcess` owns the authoritative record,
the outer SBR2 staged/issued tuple, and a distinct one-use
`BrowserChildPermit`; worker `BrowserSession` is a mirror. `SBCI1` carries only
the child identity plus direction/kind/routes/raw URL reference/method/headers/
body. The host validates canonical framing, bounds, live identity, sandbox,
CSP, origin, route, request, and navigation policy before it creates `SBCP1`.
`SBCP1` returns the exact normalized operation plus an opaque 32-hex permit,
bound in the host ledger to the current outer SBR2 process/root/wire tuple.
Consume it immediately before exactly one mutation and clear it on every exit.

Host-to-child pointer/key/text follows the same order: validate host hit target,
issue `SBCP1` inside a new outer SBR2 command, let the worker mirror consume it
before DOM dispatch, then require the matching outer reply before host-ledger
retirement. Child-to-host script/fetch/navigation arrives as `SBCI1` within an
already-admitted outer reply; the host validates before script-visible state,
network, history, cookie, or DOM mutation.

Direct `HostedWebContentSession` serializes neither schema and uses no SBR2.
It submits the same `BrowserChildIntent` to the shared session broker, which
creates and consumes a local scoped permit around the validated mutation.
Both modes use the same sandbox/origin/base and retirement decisions.

The future SSpec/manual is
`test/03_system/security/browser_iframe_sandbox_contract_spec.spl` mirrored at
`doc/06_spec/03_system/security/browser_iframe_sandbox_contract_spec.md` with
these frozen steps/helpers:

1. `Create the sandboxed srcdoc child document` —
   `setup_iframe_sandbox_contract_fixture` /
   `check_child_document_context`.
2. `Broker one child script operation` — `check_child_script_broker_use`.
3. `Constrain child request navigation and input` —
   `check_child_request_navigation_input`.
4. `Revoke stale child authority` — `check_child_revocation_and_stale_rejection`.

Each checker begins as `fail(...)` until its production owner exists; no
constant assertion or validator-only substitute is admissible. The required
matrix covers absent versus empty sandbox, iframe/CSP deny-wins intersection,
malformed/oversized/unknown tokens and wire fields, two distinct opaque sibling
origins, allowed same-origin without parent access, child URL versus fallback/
effective base, forged/replayed outer SBR2 and inner permit, forged identity
rejection before mutation, stale child route, child reload, parent replacement,
Stop/Close/site swap/process failure, and direct/isolated parity.
