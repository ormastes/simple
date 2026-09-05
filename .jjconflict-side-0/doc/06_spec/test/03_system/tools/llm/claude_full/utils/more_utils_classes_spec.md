# Claude Full More Utility Classes

> Checks additional utility class parity surfaces.

<!-- sdn-diagram:id=more_utils_classes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=more_utils_classes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

more_utils_classes_spec -> std
more_utils_classes_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=more_utils_classes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full More Utility Classes

Checks additional utility class parity surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/more_utils_classes_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks additional utility class parity surfaces.

## Scenarios

### Claude full more utility classes

#### should model git watcher lifecycle

- var watcher = GitFileWatcher new
   - Expected: watcher.initialized is true
   - Expected: watcher.watchedPaths.len() equals `2`
- watcher = watcher onHeadChanged
   - Expected: watcher.branchRefPath equals `/repo/.git/refs/heads/main`
   - Expected: watcher.cache[0].dirty is true
   - Expected: watchIntervalMs(true) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var watcher = GitFileWatcher.new().setCache("status").ensureStarted("/repo/.git", "/repo/.git")
expect(watcher.initialized).to_equal(true)
expect(watcher.watchedPaths.len()).to_equal(2)
watcher = watcher.onHeadChanged("/repo/.git/refs/heads/main")
expect(watcher.branchRefPath).to_equal("/repo/.git/refs/heads/main")
expect(watcher.cache[0].dirty).to_equal(true)
expect(watchIntervalMs(true)).to_equal(10)
```

</details>

#### should model shutdown and path conversion errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CleanupTimeoutError.new().message).to_equal("Cleanup timeout")
val converter = WindowsToWSLConverter.new("Ubuntu")
expect(converter.toLocalPath("C:\\Users\\me")).to_equal("/mnt/c/Users/me")
expect(converter.toIDEPath("/mnt/c/Users/me")).to_equal("/mnt/c/Users/me")
expect(checkWSLDistroMatch("\\\\wsl.localhost\\Ubuntu\\home", "Ubuntu")).to_equal(true)
```

</details>

#### should model image errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ImageResizeError.new("too large").name).to_equal("ImageResizeError")
expect(classifyImageErrorCode("ENOMEM", "")).to_equal(5)
val err = ImageSizeError.new([OversizedImage.new(1, 600)], 500)
expect(err.name).to_equal("ImageSizeError")
expect(err.message).to_contain("exceeds API limit")
expect(validateImageSizes([100, 600], 500).oversizedImages[0].index).to_equal(1)
```

</details>

#### should model mailbox queue polling and waiting

- var mailbox = Mailbox new
- mailbox = mailbox send
   - Expected: mailbox.length() equals `1`
   - Expected: mailbox.revision() equals `1`
   - Expected: polled.found is true
   - Expected: polled.message.content equals `hello`
   - Expected: polled.mailbox.length() equals `0`
   - Expected: Mailbox.new().receive("task").waiters equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mailbox = Mailbox.new()
mailbox = mailbox.send(MailboxMessage.new("m1", "user", "hello"))
expect(mailbox.length()).to_equal(1)
expect(mailbox.revision()).to_equal(1)
val polled = mailbox.poll("user")
expect(polled.found).to_equal(true)
expect(polled.message.content).to_equal("hello")
expect(polled.mailbox.length()).to_equal(0)
expect(Mailbox.new().receive("task").waiters).to_equal(1)
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gitFilesystemSourceLinesModeled()).to_equal(699)
expect(gracefulShutdownSourceLinesModeled()).to_equal(529)
expect(idePathConversionSourceLinesModeled()).to_equal(90)
expect(imageResizerSourceLinesModeled()).to_equal(880)
expect(imageValidationSourceLinesModeled()).to_equal(104)
expect(mailboxSourceLinesModeled()).to_equal(73)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
