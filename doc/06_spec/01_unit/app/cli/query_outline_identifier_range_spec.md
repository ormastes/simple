# LSP outline identifier ranges

Status: **AUTHORED / NOT_RUN**. This is a manually authored companion to `test/01_unit/app/cli/query_outline_identifier_range_spec.spl`; no doc generator, SSpec runtime, native LSP endpoint or performance gate was run.

The executable spec calls the production `parse_outline_source` owner through `lsp_invoke_real_owner`. `lsp_assert_contract` checks the observed name, kind, unchanged authored signature, exact start/end and the selected signature substring. Expected offsets are fixture literals, not a copy of the production algorithm. Columns retain the existing convention: zero-based positions in the trimmed signature, with an exclusive end; this does not qualify a transport's absolute document-position conversion.

Each case uses **Prepare the real fixture**, **Invoke the production owner**, and **Check the observed contract** (or **Check the neighboring failure case**).

| Case | Observed contract to check |
|---|---|
| Short function name after its keyword | `fn f(f: i64) -> i64:` selects `[3,4)`, retaining parameter and return metadata. |
| Public/private letters | `pub fn p()` and `pri fn r()` select `[7,8)`; public documentation and original line are retained. |
| Identical scoped visibility name | `pub(package) fn package()` selects `[16,23)`, and `pub(peer) fn peer()` selects `[13,17)`, skipping modifier occurrences. |
| Nested method/static declarations | `me m()` selects `[3,4)` and `static fn s()` selects `[10,11)` in their trimmed signatures; parent `C` and source line remain intact. |
| Extern/function keywords and repeated names | `extern fn e()` selects `[10,11)`; `fn n(n: text)` selects `[3,4)` rather than the keyword's `n` or parameter. |
| Type/binding names | Class, struct, enum, trait, impl, val and var names select their authored identifier after the respective keyword. |
| Import/field/domain neighbors | Import names skip `use`/`import`; fields retain column0; the `schema{}` domain marker retains its existing `[0,6)` range. |
| Recognition boundary | Unsupported `async fn` and a `pubfn` lookalike remain absent. The location repair does not introduce declaration recognition. |

Public-function recognition is inherited from already-landed PR7502, not reimplemented here. Historical endpoint checks belonging to that PR are not execution evidence for this follow-up. Full LSP protocol, revision/action/source-view correctness, native final-source qualification and latency/RSS remain separate open gates.
