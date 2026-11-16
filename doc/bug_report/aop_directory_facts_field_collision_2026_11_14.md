# AOP directory facts identity aliases delimiter-bearing fields

Status: native wrong-cache-hit reproduced; repaired checks 1–13 passed; independent Unicode golden blocked by the pinned producer escape defect. Severity: P1
(cache may reuse a different pointcut result). Canonical bug database update is
coordinated by the parent lane; this report does not mark the bug landed.

The existing `aspect_match_shard_v1::_point_fact_text` concatenates
`id|kind|symbol|owner|attrs` without escaping the first four fields. With the
same scope `pkg`, roster `["b|c", "c"]`, point ID `mod::a`, kind `forward`,
empty attrs/body, symbol `a|b` and owner `c` serialize identically to symbol `a`
and owner `b|c`. The negative root is also identical. Selector `a` distinguishes
the points, but their facts key and therefore match-cache lookup collide.
Physical TLDR checksums do not repair a semantic matcher-key collision.

The repair frames every point field by UTF-8 byte length, changes all affected
identity domains in the owning module to v2, and uses byte widths for nested
list/selector frames. Public V1 function and record names remain compatible.
Body digests remain excluded from selector-visible facts. Cache, shard and
universe completeness reject retained facts keys that fail current recomputation;
old match/apply/query identities consequently miss rather than alias new ones.

Bounded identity audit: `_framed` and `_join` are length-framed sequences;
selector `_canon` uses closed operation/form grammar and length-framed operands;
negative roots, selector/facts/match/result/apply identities all receive explicit
v2 domains. `.rr` readers consume the new digest values through existing APIs.
No other owned module reproduces these exact AOP domain encodings. The similarly
named `simple/aop-selector/v1` in MDSOC is a separate canonical owner and is not
changed by this repair.

Five focused regression scenarios are authored in
`test/01_unit/compiler/cache/aop_facts_framing_v2_spec.spl`; the SSpec runner remains unexecuted. They cover the concrete collision/cache result, Unicode/delimiters,
stale-key refusal, body-only selection stability, and an independent fixed UTF-8
framing digest. No unrelated filename or
symbol character is banned.


## Executed focused probe

The private tracked fixture `/tmp/aop-facts-framing-probe-20261114` extracts
actual production registry/guard/matcher/hash declarations, with only private
name alpha-renaming and omission of the unused semantic-query read helper.
The old matcher is extracted from the unchanged release baseline; it is not a
simulated implementation. Runtime is explicit `core-c`, producer SHA256
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.

- Attempt 1: extraction omitted the semantic-query DTO closure but accidentally
  retained its unused helper; HIR failed before executing the matcher.
- Attempt 2, fixture `8d44aa5`: compiled and reproduced the old incorrect cache
  hit. Checks 1–13 passed: distinct repaired keys, correct separate match,
  stale-key refusal, body-only stability and Unicode selection. Exit 14 was the
  independent UTF-8 framing golden, so this is **not a full PASS**.
- Attempt 3, fixture `d0c520c`: ran only the failing golden with preimage
  diagnostics. The actual 367-byte frame contains 14 literal `\u0000` spellings
  and no NUL bytes. Independent SHA256 of the printed hex equals the native
  result `0f5dd699e79ba1ff15bdcb3cbbb923bd57878d071cfce64145d478fda16771ed`.
  The intended golden remains
  `d606ea14d13b8949daccd477e2caa960a2d09879144afe9b586c37dfb6a8eb9e`.

All three compile attempts used a validated 2 GiB, zero-swap cgroup, a 60-second
compiler timeout and an owned 8 GiB available-memory watchdog. The immutable
fixture receipts `attempt1-execution.sdn`, `attempt2-execution.sdn` and
`attempt3-execution.sdn` retain source/binary hashes, logs and resource records.
No previous green criteria were rerun by diagnostic attempt 3. Probe stopped
at three attempts. The escape defect is established for this exact producer,
not claimed to recur on the current source compiler. No oracle was changed to
match the accidental encoding. Full compiler/LSP smoke and full feature
qualification remain unrun.
