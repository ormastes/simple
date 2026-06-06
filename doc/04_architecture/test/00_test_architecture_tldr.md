# Test Architecture TLDR

Simple tests flow from source discovery through runner scheduling, adapter
execution, and evidence generation.

```text
test/**/*.spl / .spipe / markdown
  -> manifest scan
  -> SPipe wrapper or doctest/Sdoctest extraction
  -> direct runner or daemon scheduler
  -> local / container / QEMU / hardware / remote / GUI adapter
  -> result + generated docs + verify gate
```

Remote and bare-metal path:

```text
spec target metadata
  -> daemon resource policy
  -> QEMU/hardware/remote adapter
  -> boot/upload/run
  -> logs + SPipe assertions
```

Markdown/doc path:

```text
md fence or sdoctest block
  -> comment modifiers
  -> temp Simple source
  -> runner
  -> result DB/report
```

Open next:

- `00_test_architecture.md`
- `test_runner_daemon_resource_governor.md`
- `../ui/ui_test_architecture.md`

