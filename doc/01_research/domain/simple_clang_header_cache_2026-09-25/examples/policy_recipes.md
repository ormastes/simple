# Policy recipes: what to register and what happens

These are proposed semantics for the SDN example, not existing Simple commands. Start from a reviewed target/toolchain profile rather than learning a new allowed baseline from every compilation.

## 1. Keep an ABI definition fixed

`PROJECT_ABI` must be object-like `3`. `-DPROJECT_ABI=4`, `-UPROJECT_ABI`, or an empty replacement is a policy error. To introduce ABI 4, define an explicitly reviewed profile and separate compatibility domain. An object built with ABI 4 cannot satisfy ABI 3 merely because it has a valid digest.

## 2. Allow a small family of feature variants

Register `FEATURE_LOG` values `0` and `1`. Both configurations are legal; they produce distinct preprocessing/native-resource contexts when relevant. Do not load a PCH made for `0` while compiling the `1` configuration. An unlisted value is an error, not a newly discovered allowed variant.

The standard compiler-generated builtins are admitted as part of the exact toolchain/target/language environment. They are not a manually maintained list of every builtin. Project overrides of that environment require explicit permission.

## 3. Register a generated configuration header

Register `build/generated/config.h` as the output of `//config:generate`, with an allowed exported-macro set. The generator must finish and its output digest must be known before dependent compile actions run. Merely registering the pathname neither trusts arbitrary bytes found there nor permits unlimited macro values.

A content change to a legitimate header normally changes resource identity. It is not inherently a policy violation. Unapproved definitions/values, wrong producer identity or an input escaping the approved root are violations.

## 4. Permit one vendor macro with complex caching

A rule matching `VENDOR_BUILD_TEXT`, origin `vendor/sdk/config.h`, and consumers `vendor/sdk/**` may permit open-ended replacement tokens. Its complete admitted macro/input context remains in cache identity. If it affects `include/project/public_api.h`, the vendor-only rule is insufficient; show the escaping consumer and require a separate reviewed decision.

Do not translate this rule into `-fmodules-ignore-macro=VENDOR_BUILD_TEXT`. An allowed semantic change is not evidence of irrelevance.

## 5. Permit one whole contextual file

An explicit `complex-header` rule can permit contextual macro variation entering `vendor/legacy/generated_api.h`, without enumerating every internal definition. It applies only at that boundary. Use a complete supported TU/native-prefix context, not an arbitrary cached AST fragment.

This file-scoped rule does not automatically legalize a globally forbidden command-line definition across the entire translation unit. Require complete confinement evidence or an explicitly wider legacy profile. Full-context cache keys protect reuse correctness; they do not replace permission checking.

## 6. Disable semantic reuse for a problematic fragment

A file rule for `include/detail/rows.inc` can authorize intentional X-macro expansion and choose `none`. Reprocess it in each actual admitted context. A cached enclosing PCH or whole-object hit cannot hide the work. In delegated Ninja mode, the Simple entry point must force the relevant semantic action when the target is requested; otherwise the launcher might never run.

Raw source bytes may still be shared unless a separate confidentiality/storage policy forbids that. A separate explicitly named resource-only opt-out can allow whole-object caching, but plain `none` has the stronger transitive meaning.

## 7. Dynamic build information

A timestamp-based build-info source can use an explicit no-cache exception. Record whether its producer is intentionally dynamic, and generate current bytes under that contract. Prefer an explicit reproducible build-time input for reproducible releases, with its value in the action key, rather than reading untracked wall time.

## Decision table

| Request | Permission | Cache result |
|---|---|---|
| Unknown `-DFEATURE_FAST=1` | Reject | No admitted resource or action result. |
| Declared `FEATURE_LOG=1` | Accept | Exact valid variant only. |
| Approved vendor macro in approved consumer | Accept | Full supported context, or its explicit none fallback. |
| Same vendor macro escapes to a strict API | Reject unless separately approved | An otherwise valid cache key does not waive the violation. |
| Registered no-cache fragment | Accept its specified contextual variation | Fresh processing; enclosing shortcuts forbidden. |
| Allowed header edit, same mtime/size | Accept | Content/semantic dependency changes still invalidate. |

Review exceptions with an owner, reason, affected targets/dependencies, fallback and expiry. A disabled cache must never become a general disabled verifier.
