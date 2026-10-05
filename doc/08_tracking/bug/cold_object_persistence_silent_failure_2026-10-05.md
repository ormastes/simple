# Cold object persistence failure loses its worker diagnostic

Status: failure-site diagnostic repaired; rebuilt-producer verification pending.

The `memory-validation-703b-cfa73-1` cold and warm attempts each produced six native objects, printed `Cache: reused 0 modules; rebuilt 6.`, then exited 1 without an error message or executable. HIR completed three physical modules. All twelve observed object capsule receipts had matching physical byte counts and SHA-256 values. No runtime assertions executed; the intentional cache-write fault test remained blocked.

The post-object persistence owner returns its error solely through `CompileResult.CodegenError`. Other native capsule failure owners already print and flush at their failure sites because this transport can lose diagnostics. Apply the same practice to persistence: emit a literal error heading, the exact reason, and the four inventory counts before returning the unchanged error. Keep the cache gate, nonzero result, and publication rules unchanged.

The six native identities include three import aliases in addition to the three physical modules. This suggests an inventory mismatch, but the in-memory receipt and accepted identity maps were not recorded. Do not claim that mismatch as proven or relax the gate. The new diagnostic supplies the evidence needed to identify the first rejected condition on the next affected rebuild.

This change does not fix or qualify the memory regression, successful cache reuse, alias identity handling, or cache-write fault recovery. Existing native validation must execute with a rebuilt producer before those claims can be made.
