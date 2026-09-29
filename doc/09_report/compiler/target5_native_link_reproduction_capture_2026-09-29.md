# Target 5 native link input capture (Linux LLD, 2026-09-29)

Status: opt-in production linker capture works in a focused no-stub native
probe. This is an input-evidence mechanism, not a matched C size or Target 5
qualification pass.

`SIMPLE_NATIVE_LINK_REPRODUCE_PATH=/absolute/path/output.tar` now asks the
Linux direct-link path to pass LLD's `--reproduce` option. The path must be a
new absolute `.tar` path. Non-Linux, non-LLD, cross-compiler, internal-linker,
SMF, and CRT-fallback routes refuse the request instead of producing an
unrecorded binary. A successful link also writes `<archive>.receipt` binding
SHA-256 of the LLD archive, native output, and linker executable; failure to
write that receipt removes the output and fails the link. Ordinary links do
not create the archive or hash these inputs.

Focused evidence from the isolated Target 5 worktree:

- A pure-Simple Stage2 no-stub entry-closure build of
  `test/fixtures/compiler/native_link_reproduce_probe.spl` compiled 456
  units with zero failures and linked the native probe.
- With `SIMPLE_LINKER=lld`, the probe linked a minimal C object and exited 0
  with `PASS native_link_reproduce_probe`. The linked binary exited 0. The
  LLD archive contains `response.txt`, `version.txt`, the exact C object,
  CRT objects, libc, loader, and support archives. Its response file records
  `--gc-sections`, `--icf=all`, `-pie`, and the actual link inputs.
- Archive SHA-256:
  `f17c9cbc7bdf6021b898c13ecdadcba4b355928bcf534ab778684abfac537024`;
  output SHA-256:
  `46883a86e7a585f4681ee350f428ff64e7af8b1574d10dbd035ae47f8762f637`;
  linker SHA-256:
  `3b2e366d1a5bcdd2e305a6f4997e809e8af2c46b84469c1a6b496337591a1833`.
  Independent `sha256sum` output matched the receipt fields.
- A non-LLD run created no reproduction archive and exited 1, but the
  diagnostic Stage2 runtime faulted when the fixture called `unwrap_err` on
  the rejected result. That test does not prove the named error. The fixture
  no longer calls `unwrap_err`; the corrected negative path has source review
  only and needs a later native run.

The top-level non-Linux/SMF refusal and failed-link output cleanup were also
added after the positive probe build and have source review only. They need
runtime coverage in the next verification session.

The saved 13,544-byte Stage4 Simple hello predates this capture and still
lacks an exact link-input archive. Next: rebuild that hello with this opt-in
capture, reproduce a C entry using the archived startup/runtime/link inputs,
then run the 30/100-sample startup/RSS and 1.05 size gates. Also add a
fail-closed BS7 checker binding the C comparator to these captured inputs;
the present checker trusts a `matched-startup-v1` label without such proof.

Fresh Stage4 follow-up: this branch's pure-Simple Stage2 bootstrap tool
compiled all 866 selected-K1 source units with zero failures, then its older
SQLite provider contract rejected the current ABI symbol. A refreshed
bootstrap-only tool required explicit SCV cold initialization; with it, source
closure reached 821 files but the runtime directory was interpreted as a
dynamic provider path and the static fallback rejected an untyped `str` SFFI
call. No Stage4 compiler or captured hello was produced. See
`doc/08_tracking/bug/target5_stage4_bootstrap_runtime_path_dual_use_2026-09-29.md`.

Bootstrap-provider follow-up: an existing runtime archive directory no longer
becomes a dynamic-library path in the bootstrap provider. The untyped SFFI
refusal remains fail-closed and now identifies its function and argument
index. Focused Rust tests pass (3 native-loader, 21 dynamic-SFFI). The
refreshed debug bootstrap executable then timed out after 300 seconds on a
Stage4 attempt without a provider-directory warning or a named foreign call.
No fresh Stage4 compiler or hello capture has been produced from these edits.
