# Windows broker frame progress and output ordering

Status: **SOURCE-ONLY NOT_RUN**. These pure cases invoke the actual progress
state classes. They provide no authenticated channel, issued control authority,
Engine effect, native race witness or Windows qualification.

Source: `src/lib/nogc_async_mut/container/providers/windows/docker_broker_progress_v3.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/windows_docker_broker_progress_v3_spec.spl`.

| Authored case | Intended assertion |
|---|---|
| Partial input | Stale request prefix reports known progress; only the current prefix may continue |
| Unknown outcome | Retry and later completion cannot unfreeze an uncertain frame |
| Immutable correlation | Changed nonce, revision, body or target under the same sequence refuses |
| Sequence discipline | Incomplete frames cannot overlap; completion admits only the exact successor |
| Reply binding | Unsolicited, wrong-sequence or oversized-prefix progress refuses without state advance |
| Geometry | Exact rows/columns and geometry digest are separate from byte-prefix accounting |
| Older unknown reply | Unknown freezes without reducing the greatest known accepted prefix |
| Output channels | Ordered stdout/stderr chunks maintain independent offsets |
| TTY and EOF | TTY refuses separate-channel claims; output after EOF refuses |
| Exhaustion and target | Sequence never wraps and another target cannot consume the expected sequence |

NewFrame and ContinueFrame are protocol dispositions, not permission. The actual
consumer must revalidate the live issuer and native barrier for every attempted
effect. Native attempt sequence and pending IO remain outside this pure tracker.
Output consumption creates no second reader and reports no workload completion.
