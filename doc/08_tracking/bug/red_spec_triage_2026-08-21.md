# RED spec triage — 2026-08-21

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed),
59757000 bytes, 2026-08-21 03:26:53 UTC. `bin/simple test` runs the tree-walk
interpreter. No seed was rebuilt.

Caveat: `bin/simple` **disappeared for ~80s mid-session** (another session
redeploying). Any timing here is an envelope, not a clean measurement.

## RESOLVED

### `test/01_unit/lib/nogc_sync_mut/http/auth/digest_spec.spl` — FIXED
`Results: 14 total, 14 passed, 0 failed`. Product was wrong, spec was right
(RFC values independently recomputed with `openssl dgst`). Full root cause and
fix: `crypto_types_text_to_bytes_collides_with_base_encoding_2026-08-21.md`.
No regression in the siblings that share the changed modules:
`basic_spec` 15/15, `hmac_rfc4231_spec` 12/12.

## Root-caused, NOT fixed

### `test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl` — 0/4, spec is unrunnable by construction
`semantic: function normalize_type_segments not found`,
`semantic: variable Parser not found`.

The spec does `use compiler.module_resolver.resolution.{normalize_type_segments}`,
but the only definition in the tree is
`src/compiler_rust/compiler/src/module_resolver/resolution.rs:288`, a
**private Rust `fn`** (not `pub`), with no Simple-side binding of any kind.
There is nothing for the import to resolve to and no bridge that could expose
it. This cannot go green without either a seed change making the symbol `pub`
and exporting it to Simple, or rewriting the spec against a real Simple-side
API. Left RED per `.claude/rules/testing.md` — do not weaken the assertions.
The `test/unit/` mirror has the same import at line 9.

### `test/01_unit/compiler/native/inline_asm_spec.spl` — 37/41
Four failures, all `semantic: variable \`nop\` not found`, all on the *bare /
unparenthesized* raw-asm forms ("recognizes asm keyword in code", "parses
simple asm expression", "parses asm with volatile flag", "does not require
parentheses for raw asm"). The parenthesized and empty-block forms pass. The
seed parser is evaluating the raw asm body as an expression instead of holding
it as an opaque template. Frontend/parser defect in the Rust seed — recorded,
not fixed, per the no-seed-build constraint.

### `test/01_unit/lib/nogc_sync_mut/engine/render/shader_compile_spec.spl` — 12/17
Two distinct causes:
1. `semantic: method \`len\` not found on type \`i64\` (receiver value: 0)` on
   "AC-5: second call with same source does not grow spirv cache" — the cache
   accessor returns a scalar where the caller expects a collection.
2. The WGSL transpile assertions ("output does not contain void main()",
   "output contains @vertex", "output contains @fragment") fail because the
   transpiler emits a GLSL passthrough with a `// WGSL … (transpiled from GLSL)`
   banner rather than real WGSL. This is a **genuine unimplemented feature**,
   correctly asserted by the spec. Leave RED.

### `test/01_unit/lib/nogc_sync_immut/native_combinators_spec.spl` — 0/1
`expected <lambda> to equal [7, 8]` — the facade chain returns an unapplied
lambda instead of forcing it. Combinator is never evaluated.

### `test/01_unit/lib/common/web/browser_renderer_protocol_spec.spl` — 9/12
### `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` — 10/12
### `test/01_unit/lib/common/web/browser_session_loading_history_spec.spl` — 1/2
(`expected 24 to equal 25`.) All three modules import
`std.common.base_encoding.utilities.{text_to_bytes, bytes_to_text}` — the
**other half of the same collision** documented in the crypto record. Strongly
suspected same root cause; not yet proven with a reduced probe, and not fixed,
because the safe mitigation used for crypto (unique names + delegators) has a
much larger call-site surface here.

## Not reached

- `test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl`
  — **timed out at 300s** (exit 124), no `Results:` line. Not a failure;
  needs a longer budget or a narrower target before it can be triaged.
- `test/01_unit/compiler/native/build_native_min_spec.spl` — `Results: 1 total,
  0 passed, 1 failed`, but the log carries no `✗` detail line. Needs re-running
  with fuller output.
- "diag" and the second `inline_asm` spec were not disambiguated — there are 5
  `inline_asm*_spec.spl` files and ~20 `*diag*_spec.spl` files under
  `test/01_unit/`. Need the exact paths.
