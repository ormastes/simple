# Test Architecture TLDR

Simple tests flow from SSpec `.spl` source discovery through SPipe
runner/docgen scheduling, adapter execution, SSpec manual generation, and
evidence generation.

```text
test/**/*.spl / markdown
  -> manifest scan
  -> SSpec wrapper or doctest/Sdoctest extraction
  -> direct runner or daemon scheduler
  -> local / container / QEMU / hardware / remote / GUI adapter
  -> result + generated docs + verify gate
```

SSpec manual path:

```text
test/**/*_spec.spl with step("...")
  -> spipe-docgen
  -> compact numbered manual steps
  -> folded executable source
```

Current SSpec manuals are step-based. `Given_*` / `When_*` / `Then_*` helper
names are legacy style; new manuals should use `step("...")`.

Remote and bare-metal path:

```text
spec target metadata
  -> daemon resource policy
  -> QEMU/hardware/remote adapter
  -> boot/upload/run
  -> logs + SSpec assertions
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
- `../../07_guide/infra/sspec_scenario_manual.md`
- `test_runner_daemon_resource_governor.md`
- `../ui/ui_test_architecture.md`
