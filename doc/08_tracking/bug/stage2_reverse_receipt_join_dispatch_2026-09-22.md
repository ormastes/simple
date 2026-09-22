# Stage2 receipt encoding dispatches text join to async join

Date: 2026-09-22. Baseline: `b74a4b94bbb03151b36954423798abae29c2e4c3`.
Status: bounded native red/green PASS; independent Astra review PASS.
Full rebuilt Stage2 admission remains pending.

## Cause and correction

Stage2 completed its native build, then rejected hello-world admission with
`capsule-identity-mismatch`. During the ordinary cache-persist path after that
error, it crashed in `Future_dot_poll+4`, through async `join+220` and
`reverse_reference_receipt_encode_v1+760`. The capsule mismatch is a separate
agent's defect; this correction preserves that error rather than hiding it.

In the frozen bootstrap producer, the encoder's
`[headers].concat(lines).join("\n")` loses the collection type between chained
calls and resolves to the global async free function `join`. An explicit
`[text]` local between concat and join restores collection dispatch.
`red-encode.disasm` calls async `combinators__join`; `green-encode.disasm`
calls `rt_string_join`. These directly substantiate the frozen producer's
behavior. Current Simple `try_ufcs` in `35.semantics/resolve_strategies.spl`
already protects Array/Slice receivers and also rejects insufficient free
function arity; its MIR path can use `rt_array_join_any`. This report does not
claim those current source paths necessarily have the frozen producer's bug.
This is a narrow call-site correction; general chained-call type propagation
remains open.

The same five headers, concatenation, sorted projection lines and newline
separator remain. The local adds no new collection traversal or allocation.
Invalid receipts still return the empty string before encoding. No cache
admission, error policy, digest, wire framing, deduplication or ordering changes.

Exact rejected candidate and crash evidence are retained at:
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/evidence/macos-enforced-bd544/stage2-native-cache-b74a4b9`.
Candidate SHA-256:
`1f89735e5982f6a13c54e92ae874aa68935263d90f6f3e4ee2c6fa6a5604a1b3`.

## Regression and resource evidence

Recipe: `test/fixtures/native/reverse_receipt_join/README.md`.
Evidence: `/Users/ormastes/simple-tmp/stage2-receipt-join-20260922/build/native_probe/receipt-join`.
The projection extracts the real encoder, types and helpers, uses the real key
codec and actual async combinator, and compares exact frames and rejection
results. It does not run filesystem publication or the entire compiler.

Frozen bootstrap-only producer `simple` SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Runtime `libsimple_native_all.a` SHA-256:
`5e11731fa77990ecc170b939d2b16a48a1d9be417069202f365861e69576006d`.
Both reside at the parent attempt's
`build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.

| Measurement | Red | Green |
|---|---:|---:|
| Compiled / cached / failed | 29 / 0 / 0 | 29 / 0 / 0 |
| Native run exit | 139 | 0 |
| Build wall seconds | 3.49 | 3.38 |
| Build sampled tree peak KiB | 277392 | 272448 |
| Build executable peak RSS bytes | 154812416 | 156221440 |
| Run wall seconds | 0.34 | 0.34 |
| Run sampled tree peak KiB | 2496 | 2432 |
| Run executable peak RSS bytes | 8749056 | 9175040 |

Green prints `reverse-receipt-join-pass` after all ten checks. All four guards
have zero observer errors and quiescent cleanup. Cap5859375KiB is sampled
enforcement, not hard containment (`hard_memory_limit=0`). Build deadlines
180s, run deadlines20s. The short single measurements establish a bounded
projection, not a speedup or general performance claim; sampled run peaks
miss short-lived RSS captured by `/usr/bin/time -l`.

Artifact SHA-256 identities:

- Red executable: `a6c0909ca5fa4279cfa229341fc68242925dee2d82fc700dde8ff2c141989fee`.
- Green executable: `3c4eebeec6037690fe5123744978fa0f70585594da758dc9423db358b4730385`.
- Red projection: `1e2f5f41bfef244563f0c172277834672a1cdbbf6e6837e9a054377b0c2637e6`.
- Green projection: `2874350021a5d29ca82d63ef6e2671080d5ce6b9d238b9a24a2a99cc31423834`.
- Corrected source: `9720bfd559eca4036acef739dfe0b8aa182686a31a5c03ef9ba10abf11369fa3`.

One correction cycle, private caches, no bootstrap, deployment or push.
Core/library/MCP/LSP checks, admitted compiler matrix and Stage3 remain gated
on an admitted Stage2 compiler. No general seed test or release PASS is claimed.

Independent Astra review confirmed exact projection extraction, identical
scenarios, the sole production difference, red/green dispatch, meaningful
assertions and resource bounds. No blocking findings. Existing insertion-sort
complexity is unchanged. Working/staged direct-env guards and whitespace checks
passed, and `doc/06_spec` contains zero executable `_spec.spl` files; these are
scoped commit checks, not production verification PASS.
