# Simplebox short-write branch rejected by the native parser

Status: source workaround applied; native verification pending.

The first 58-task progressive build ledger records a parse failure at
`src/os/tools/simplebox/simplebox_fs_applets.spl:565:105`: unexpected newline.
The expression mixes an inline `then chunk` branch with a multiline `else:`.
The producer is `3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`;
the failing target source is `b0b36be5e4ee78bded9de2e3f89e6a6bbc669d54`.

Use two block branches while retaining the zero-offset fast path. The original
chunk is reused for a full write; only a partial write constructs a suffix.
Do not replace this with an unconditional slice, which would add copying.
Whether the mixed grammar should be accepted remains a parser compatibility
question; this workaround does not establish that the grammar was repaired.

The native fixture `test/fixtures/compiler/bootstrap_multiline_if/main.spl`
adds seven checks for the full chunk, short-write suffix, empty chunk, and
end offset. These extend ten existing branch checks. All 17 native checks
must execute before claiming runtime verification; source inspection alone
is not a passing native test. Existing frozen build sources are unchanged.
