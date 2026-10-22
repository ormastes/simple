<!-- codex-research -->
# Selected submodule pin reachability, 2026-09-25

The parent `HEAD` tree has exactly two mode-160000 gitlinks. Each URL below came from the current `.gitmodules`. In a separate temporary initialized Git repository for each child, `git fetch -q --depth=1 <url> <exact-pin>` exited 0, then `git cat-file -t <exact-pin>` returned `commit`.

| Parent path | Parent gitlink | Repository | Exact-pin fetch |
|---|---|---|---|
| `.spipe/spipe` | `19553c58b7c933fea5affa2273d3b624ecc66099` | `https://github.com/ormastes/Spipe.git` | PASS, commit object fetched |
| `examples/08_gpu/simple_cuda_example` | `e74405599b8ac4b5649258dc397af5b3ef4d508b` | `https://github.com/ormastes/simple_cuda_example.git` | PASS, commit object fetched |

This proves both selected commits were directly fetchable from their declared remotes at the check time. It does not prove recursive nested pins, a clean checkout with all files, child compatibility canaries, policy exception scope, or future availability. The local `.spipe/spipe` worktree points at another commit and was not modified. Dormant `.gitmodules` declarations were not fetched. The new `config/build/submodule_inventory.sdn` remains structural policy input; a trusted Git adapter and recurring clean-checkout canary are still required for automated admission.

A later read-only `git ls-tree -r <exact-pin>` against both locally available commit objects found no mode-160000 descendants in either pin. The Simple clean-fetch adapter now checks the fetched commit's complete bounded `ls-tree -r --full-tree` output and rejects any nested gitlink or malformed row, since V1 policy has no transitive pin declarations. A focused standalone Simple run of that new predicate passed (`/tmp/simple-submodule-nested-selfhost-20260925.log`). A subsequent Simple CLI diagnostic explicitly selected the optional CUDA pin alongside required Spipe and returned `LOCAL_DIAGNOSTIC_CLEAN_FETCH_VERIFIED` after clean fetch, canary and nested-tree checks (`/tmp/simple-submodule-nested-live-selfhost-20260925.log`). Its exit code `1` is intentional: local working-tree policy is not protected admission evidence. The release-path binary later identified itself as a Rust bootstrap seed, so these runs do not qualify as pure-Simple self-hosted verification.

The policy parser now rejects duplicate recognized fields, unknown fields, invalid reachability values, and a `fetch_by_default` value that disagrees with `required`. A focused standalone parser smoke returned `SUBMODULE_POLICY_PASS`, but the invoked release-path binary printed the Rust bootstrap-seed warning, so this is diagnostic-seed evidence only. The focused SSpec additions have not run. The CLI's explicit `--policy-rev` route now also returns a diagnostic status and exit code `1`: the existence of a caller-supplied immutable commit does not establish protected policy authority. A base-owned controller must bind candidate, policy and verifier identities before a protected CI result can pass.

Branch-policy follow-up: the selected inventory now names `refs/heads/main` for both parent gitlinks. At this check time, a fresh isolated fetch of each exact pin and its declared remote branch returned `merge-base --is-ancestor` success. The observed Spipe remote tip was `73f516261ea2e791373c3d0ae0fe435c50ef381d`; CUDA's was `b58990d9e5642437a32631c5ef0c36cf8b4ca7b0`. Spipe's local `origin/main` was older, so local tracking refs alone would have been weak evidence. The Simple adapter now repeats the exact-pin fetch, branch fetch, ancestry check, canary and no-nested-gitlink check in a private repository, and records the observed branch tip in `PinReachabilityV1`. Its focused CLI diagnostic returned `LOCAL_DIAGNOSTIC_CLEAN_FETCH_VERIFIED` with exit code `1` on the selected required and optional pins after this change. The release-path binary identified itself as a Rust bootstrap seed, so this is not a self-hosted or protected CI PASS.

A negative fresh-fetch control used Spipe commit `6388d7d61df7262ad61e0d47835e4ffddf911e4c` from the advertised `fix/mcp-token-bounds` branch. The same depth-1 exact-pin fetch followed by full `refs/heads/main` fetch yielded `merge-base --is-ancestor` failure at the observed main tip. This distinguishes an available commit from an approved-branch ancestor; it does not qualify the Simple verifier or remote branch-protection settings.
# Local Git ancestry fixture, 2026-09-25

`sh scripts/check/check-submodule-branch-ancestry-fixture.shs` passed once on
this macOS host: a depth-one exact pin followed by an approved-branch fetch
made the historical pin provably ancestral, while an unrelated exact pin did
not become ancestral. The fixture uses a local `file://` bare remote with
reachable-SHA fetch enabled. It confirms Git's ancestry behavior for the
adapter's sequence, not the Simple adapter's HTTPS policy, parser, protected
controller authority, or end-to-end CLI behavior. Those still require a
deployed pure-Simple verifier and trusted base-owned invocation.
