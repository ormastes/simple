# x64 freestanding: chained `x.len().to_u32()` / `.to_i64()` mis-lowers

**Target:** `native-build --backend cranelift --target x86_64-unknown-none`
(SimpleOS freestanding kernel). **Status:** OPEN (root cause in the cranelift
lowering of a method-call chained directly onto another call's result); worked
around at every call site by binding the intermediate to a `val`.

## Symptom

A `.len()` (or any method returning an int) chained *directly* into a numeric
cast — `x.len().to_u32()`, `x.len().to_i64()` — lowers to a bogus value on this
target. Passed to a comparison/consumer it produces wrong control flow. Binding
the intermediate to a `val` first makes it correct:

```
# BROKEN on x64 freestanding — yields a bogus (often huge) count:
if self.channels.consume_remote_window(id, output.len().to_u32()): ...
# CORRECT — bind first:
val n = output.len()
if self.channels.consume_remote_window(id, n.to_u32()): ...
```

`len()`, full-`==`, `[u8]` indexing, and a bound-then-cast are all fine; only
the *chained* cast-on-call-result mis-lowers.

## Confirmed instances (all in src/os/apps/sshd/)

1. `do_version_exchange` — `our_version.len().to_i64()` (already bound; note in-code).
2. `_finish_exec_request_inline` — `output.len().to_u32()` gated
   `consume_remote_window`, so the 712-byte `getfile /hello.o` channel data was
   silently dropped (empty file on the host). **Binding `out_len` flipped the
   window-consume from reject→accept — the direct evidence this bug is real.**
3. `_scp_step_inline` — `ctrl.len().to_u32()` / `body.len().to_u32()` gated the
   scp-source C-record and body sends (same silent drop). Bound to `ctrl_len` /
   `body_len`.

## NOT a nested-`me`-mutation bug (hypothesis disproven)

The scp-source stall ("every ack re-entered stage 0") was previously mis-filed
as "`self.scp_stage = 1` set inside the nested `me` call `_scp_step_inline` does
not persist on x64 freestanding." That is FALSE:

- Minimal repro (`struct` with `u32` field, `me outer` calls `me inner` that sets
  `self.f`/`self.g`, incl. a `.to_u32()`-cast variant) prints `NESTED_ME_OK`.
- Existence proof on the *same* freestanding target: `_finish_exec_request_inline`
  (a nested `me` call) mutates `self.state` and `self.channels` and works —
  sessions close and channels are removed. If nested-`me` scalar mutation were
  broken, the whole sshd (cipher/channel/shell state) would be broken.
- `scp_pending` is itself set inside a nested `me` call (`_handle_exec_request_inline`),
  same shape as `scp_stage`, and persists.

The real causes of the scp-source stall were (a) this chained-cast mis-lowering
gating the sends, and (b) each `scp`/`ssh` invocation opening a NEW TCP
connection = a fresh `SshSession` with `scp_stage=0` (not a failed persist).

## Fix / workaround

Bind the intermediate to a `val` before the cast at every call site. A proper
fix belongs in the cranelift backend lowering of a cast applied to a call
result on `--target x86_64-unknown-none`
(`src/compiler/70.backend/backend/cranelift_*.spl`).
