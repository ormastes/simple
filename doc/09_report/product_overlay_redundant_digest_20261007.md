# Product overlay redundant output hashing

The materializer hashed each physical output immediately after copying, then
hashed it again in mandatory final verification. Remove the immediate digest;
retain independent source replanning, exact manifest comparison, every final
output digest, physical/symlink containment, and complete inventory checks.
Corrupt output is rejected during final verification instead of immediately
after its copy. No caches, hardlinks, frozen views, or clone behavior change.

A retained source manifest contained 66,725 physical outputs. This change
eliminates one digest and repeated ancestor checks per output. It does not
eliminate final source or output verification.

Five interleaved baseline/candidate samples on the same busy Windows host used
100 source files expanded through one directory alias to 200 physical outputs:

| Measure | Baseline | Candidate |
|---|---:|---:|
| p50 elapsed | 8.956 s | 6.870 s |
| p95 elapsed, nearest rank | 11.843 s | 8.767 s |
| Maximum observed peak RSS | 16,338,944 B | 16,334,848 B |
| Digest calls per view | 600 | 400 |
| Digest bytes per view | 2,457,600 B | 1,638,400 B |

Memory is unchanged within noise. Time ratio 0.7403 plus memory ratio 0.99975
gives 1.7400. This small fixture has more aliased outputs proportionately than
the real view; its speedup is not a full-view prediction. A larger preliminary
fixture was stopped during its first candidate to limit load and is excluded.
No full source materialization, native rebuild, or release performance claim
is made. Baseline/candidate manifests matched; final output/source/manifest
mutation injections were each rejected for the expected reason.

The existing `check-product-private-materialization.shs` now invokes focused
regressions checking exactly one final digest per output, two independent
source digests, one mandatory final verifier call, physical alias bytes, and
the three mutation failures. These checks use deterministic operation counts,
not timing thresholds. Host-specific probe evidence and exact binary/module
identities are retained in the private `materializer-postcopy-digest-repair`
packet; production baseline SHA-256 is
`1c818078fe2ffc7f508c11500c2eacd28e2d0f98111ccc4369841bec6ef5b0b6`.
