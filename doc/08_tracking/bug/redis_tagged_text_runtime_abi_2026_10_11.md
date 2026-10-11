# Redis startup violates owned text and listener contracts

Status: OPEN — source repair authored; native fixtures and platform tests UNEXECUTED.

## Actual failure

Pure-Simple producer `892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`
compiled frozen `b58baa89e4d65a40768fceaf8221fdbdbe58da24`. The complete 37-object
Redis closure linked to ELF `a4c2c23d12a4a75132a82de4e8697d3fc1783065262b2f0b8e1ed21e36fbc974`
(2,251,568 bytes). Its one owned sanity attempt requested port 39352, printed
6399 and a numeric server error, then exited 0 before creating a listener.
Zero RESP assertions executed; owned cleanup was proven. The result is FAIL,
not application admission. Historical runtime source/header limits remain.

Retained evidence: `redis-startup-failure-contract-ledger.json` in the campaign
artifact root, SHA256 `33480434b9c81e9f4c84f81dc3602e8d2775e4f49933fd98e2ffce1182bcf812`.
No failed app or link was rerun to author this repair.

## Contracts and repair

The emitted extern calls unwrap text through `rt_interp_cstr` before
`rt_text_to_bytes`, `rt_io_tcp_bind` and `rt_io_tcp_write_text`. All three current
owned runtime entrypoints require tagged text handles. Their boxed-text registry
entries are missing. Register argument 0 for bytes/bind and argument 1 for write
using the existing boxing path; retain foreign C-string and pointer-plus-length
boundaries. A bounded audit of the existing linked Redis ELF found these three
strict tagged-text mismatches; connect is absent from that ELF. The reply-write
path was not executed by the failed startup; its failure is predicted from exact
call instructions and both current C/Rust provider signatures.
Embedded NUL bytes must remain inside the declared text extent.

`TcpListener.bind` and the canonical Rust `native_tcp_bind` promise a listening
socket. The C provider only called `bind`, then returned a descriptor; `accept`
does not perform `listen`. Add `listen(fd, 128)` at that same C boundary and close
the descriptor on failure, preserving negative failure and ownership conventions.
Do not add an extra listen call to the Simple wrapper: the existing Rust provider
already returns a listener and its separate `listen` operation expects a raw
pre-listen socket handle. `bind_fd` retains its separate bind-only contract.

These mismatches remain in release `8303221132a0e44a739b30f92c3a1b7723534e86`;
the source fix does not adapt current code to an obsolete archive.

## Platform limits and distinct failures

The C network implementation is shared by non-Windows hosted platforms; Linux,
macOS and BSD need separate actual tests. Its Windows branch is already an
unsupported stub and is unchanged. The Rust provider's `std::net::TcpListener`
contract covers its supported hosted platforms, with no Rust source edits.
The inspected SimpleOS syscall adapter exposes socket bind/connect/send/recv,
not proof of a complete listening provider. SimpleOS runtime qualification is
BLOCKED pending an authoritative complete listener implementation/receipt.

The numeric `IoError.message` output is a separate compiler owner/field defect:
the actual ELF reads offset 0 and formats an integer; `message` is text at offset
8. This patch does not repair it or claim full Redis startup/RESP success.
The environment pointer-plus-length ABI matches its runtime; an empty result
from the wrong text-to-bytes call independently explains the default port.

## Reproduction and prevention

- `test/fixtures/compiler/redis_startup_contract/text_bytes.spl` observes exact
  empty/singleton/embedded-NUL bytes and genuine C-string behavior.
- `test/fixtures/compiler/redis_startup_contract/listener.spl` exercises actual
  SOSIX alias resolution, invalid-address rejection, real bind/listen/accept,
  exact request bytes, embedded-NUL reply bytes and descriptor cleanup with a
  bounded external peer.
- `test/01_unit/compiler/mir/redis_tagged_text_extern_spec.spl` checks the actual
  registry and preserves distinct pair, boxed, foreign and homonymous contracts.

The forced OS `listen` failure branch is source-reviewed; no fault-injection
runtime coverage is claimed. All executable checks remain UNEXECUTED until a
qualified producer/runtime executes them; normal source hooks are separate.
