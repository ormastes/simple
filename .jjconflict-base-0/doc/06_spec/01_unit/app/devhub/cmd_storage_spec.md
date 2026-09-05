# cmd_storage_spec

> Purpose: Prove that cmd_storage dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cmd_storage_spec

Purpose: Prove that cmd_storage dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/cmd_storage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that cmd_storage dispatch.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### cmd_storage dispatch

#### help and unknown verb

#### no args prints help and returns 0

- no args prints help and returns 0
- Verify: no args prints help and returns 0
   - Expected: handle_storage([]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("no args prints help and returns 0")
step("Verify: no args prints help and returns 0")
# @req: REQ-APP-DEVHUB-001
expect(handle_storage([])).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### --help returns 0

- --help returns 0
- Verify: --help returns 0
   - Expected: handle_storage(["--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--help returns 0")
step("Verify: --help returns 0")
expect(handle_storage(["--help"])).to_equal(0)
```

</details>

#### unknown verb returns 1

- unknown verb returns 1
- Verify: unknown verb returns 1
   - Expected: handle_storage(["frobnicate"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown verb returns 1")
step("Verify: unknown verb returns 1")
expect(handle_storage(["frobnicate"])).to_equal(1)
```

</details>

#### ls — validation-only paths

#### local TARGET is rejected (ls only accepts alias/bucket[/prefix])

- local TARGET is rejected (ls only accepts alias/bucket[/prefix])
- Verify: local TARGET is rejected (ls only accepts alias/bucket[/prefix])
   - Expected: handle_storage(["ls", "/tmp/somepath"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("local TARGET is rejected (ls only accepts alias/bucket[/prefix])")
step("Verify: local TARGET is rejected (ls only accepts alias/bucket[/prefix])")
expect(handle_storage(["ls", "/tmp/somepath"])).to_equal(1)
```

</details>

#### unknown alias is rejected before any config/network access

- unknown alias is rejected before any config/network access
- Verify: unknown alias is rejected before any config/network access
   - Expected: handle_storage(["ls", "unknownalias/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown alias is rejected before any config/network access")
step("Verify: unknown alias is rejected before any config/network access")
expect(handle_storage(["ls", "unknownalias/bucket"])).to_equal(1)
```

</details>

#### cat — validation-only paths

#### missing TARGET is a usage error

- missing TARGET is a usage error
- Verify: missing TARGET is a usage error
   - Expected: handle_storage(["cat"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("missing TARGET is a usage error")
step("Verify: missing TARGET is a usage error")
expect(handle_storage(["cat"])).to_equal(1)
```

</details>

#### local TARGET is rejected

- local TARGET is rejected
- Verify: local TARGET is rejected
   - Expected: handle_storage(["cat", "/tmp/somefile"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("local TARGET is rejected")
step("Verify: local TARGET is rejected")
expect(handle_storage(["cat", "/tmp/somefile"])).to_equal(1)
```

</details>

#### bucket-only TARGET (no key) is rejected before touching config

- bucket-only TARGET (no key) is rejected before touching config
- Verify: bucket-only TARGET (no key) is rejected before touching config
   - Expected: handle_storage(["cat", "minio/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bucket-only TARGET (no key) is rejected before touching config")
step("Verify: bucket-only TARGET (no key) is rejected before touching config")
expect(handle_storage(["cat", "minio/bucket"])).to_equal(1)
```

</details>

#### stat — validation-only paths

#### alias-only TARGET (no bucket/key) is rejected

- alias-only TARGET (no bucket/key) is rejected
- Verify: alias-only TARGET (no bucket/key) is rejected
   - Expected: handle_storage(["stat", "minio"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("alias-only TARGET (no bucket/key) is rejected")
step("Verify: alias-only TARGET (no bucket/key) is rejected")
expect(handle_storage(["stat", "minio"])).to_equal(1)
```

</details>

#### unknown alias with full bucket/key is rejected pre-network

- unknown alias with full bucket/key is rejected pre-network
- Verify: unknown alias with full bucket/key is rejected pre-network
   - Expected: handle_storage(["stat", "unknownalias/bucket/key.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown alias with full bucket/key is rejected pre-network")
step("Verify: unknown alias with full bucket/key is rejected pre-network")
expect(handle_storage(["stat", "unknownalias/bucket/key.bin"])).to_equal(1)
```

</details>

#### mb / rb — validation-only paths

#### mb with no bucket segment is rejected

- mb with no bucket segment is rejected
- Verify: mb with no bucket segment is rejected
   - Expected: handle_storage(["mb", "minio"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("mb with no bucket segment is rejected")
step("Verify: mb with no bucket segment is rejected")
expect(handle_storage(["mb", "minio"])).to_equal(1)
```

</details>

#### mb with unknown alias is rejected pre-network

- mb with unknown alias is rejected pre-network
- Verify: mb with unknown alias is rejected pre-network
   - Expected: handle_storage(["mb", "unknownalias/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("mb with unknown alias is rejected pre-network")
step("Verify: mb with unknown alias is rejected pre-network")
expect(handle_storage(["mb", "unknownalias/bucket"])).to_equal(1)
```

</details>

#### rb missing TARGET is a usage error

- rb missing TARGET is a usage error
- Verify: rb missing TARGET is a usage error
   - Expected: handle_storage(["rb"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rb missing TARGET is a usage error")
step("Verify: rb missing TARGET is a usage error")
expect(handle_storage(["rb"])).to_equal(1)
```

</details>

#### rb with no bucket segment is rejected before any config access

- rb with no bucket segment is rejected before any config access
- Verify: rb with no bucket segment is rejected before any config access
   - Expected: handle_storage(["rb", "minio"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rb with no bucket segment is rejected before any config access")
step("Verify: rb with no bucket segment is rejected before any config access")
expect(handle_storage(["rb", "minio"])).to_equal(1)
```

</details>

<details>
<summary>Advanced: rb --force with unknown alias is rejected pre-network (the list+delete-then-delete-bucket loop never runs)</summary>

#### rb --force with unknown alias is rejected pre-network (the list+delete-then-delete-bucket loop never runs)

- rb --force with unknown alias is rejected pre-network (the list+delete-then-delete-bucket loop never runs)
- Verify: rb --force with unknown alias is rejected pre-network (the list+delete-then-delete-bucket loop never runs)
   - Expected: handle_storage(["rb", "unknownalias/bucket", "--force"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rb --force with unknown alias is rejected pre-network (the list+delete-then-delete-bucket loop never runs)")
step("Verify: rb --force with unknown alias is rejected pre-network (the list+delete-then-delete-bucket loop never runs)")
expect(handle_storage(["rb", "unknownalias/bucket", "--force"])).to_equal(1)
```

</details>


</details>

#### rm — arg validation + error paths, all pre-network

#### missing TARGET is a usage error

- missing TARGET is a usage error
- Verify: missing TARGET is a usage error
   - Expected: handle_storage(["rm"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("missing TARGET is a usage error")
step("Verify: missing TARGET is a usage error")
expect(handle_storage(["rm"])).to_equal(1)
```

</details>

#### bucket-only TARGET (no key) is rejected before touching config

- bucket-only TARGET (no key) is rejected before touching config
- Verify: bucket-only TARGET (no key) is rejected before touching config
   - Expected: handle_storage(["rm", "minio/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bucket-only TARGET (no key) is rejected before touching config")
step("Verify: bucket-only TARGET (no key) is rejected before touching config")
expect(handle_storage(["rm", "minio/bucket"])).to_equal(1)
```

</details>

#### unknown alias with full bucket/key is rejected pre-network

- unknown alias with full bucket/key is rejected pre-network
- Verify: unknown alias with full bucket/key is rejected pre-network
   - Expected: handle_storage(["rm", "unknownalias/bucket/key.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown alias with full bucket/key is rejected pre-network")
step("Verify: unknown alias with full bucket/key is rejected pre-network")
expect(handle_storage(["rm", "unknownalias/bucket/key.bin"])).to_equal(1)
```

</details>

#### --recursive with no prefix (bare alias/bucket) refuses before any config access, even with a real alias-shaped TARGET, and names the rb --force escape hatch

- --recursive with no prefix (bare alias/bucket) refuses before any config access, even with a real alias-shaped TARGET, and names the rb --force escape hatch
- Verify: --recursive with no prefix (bare alias/bucket) refuses before any config access, even with a real alias-shaped TARGET, and names the rb --force escape hatch
   - Expected: handle_storage(["rm", "minio/bucket", "--recursive"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--recursive with no prefix (bare alias/bucket) refuses before any config access, even with a real alias-shaped TARGET, and names the rb --force escape hatch")
step("Verify: --recursive with no prefix (bare alias/bucket) refuses before any config access, even with a real alias-shaped TARGET, and names the rb --force escape hatch")
expect(handle_storage(["rm", "minio/bucket", "--recursive"])).to_equal(1)
```

</details>

#### -r (short form) with no prefix also short-circuits pre-network with the same refusal

- -r (short form) with no prefix also short-circuits pre-network with the same refusal
- Verify: -r (short form) with no prefix also short-circuits pre-network with the same refusal
   - Expected: handle_storage(["rm", "minio/bucket", "-r"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-r (short form) with no prefix also short-circuits pre-network with the same refusal")
step("Verify: -r (short form) with no prefix also short-circuits pre-network with the same refusal")
expect(handle_storage(["rm", "minio/bucket", "-r"])).to_equal(1)
```

</details>

#### -r with a non-remote/no-bucket TARGET is a usage error pre-network

- -r with a non-remote/no-bucket TARGET is a usage error pre-network
- Verify: -r with a non-remote/no-bucket TARGET is a usage error pre-network
   - Expected: handle_storage(["rm", "minio", "-r"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-r with a non-remote/no-bucket TARGET is a usage error pre-network")
step("Verify: -r with a non-remote/no-bucket TARGET is a usage error pre-network")
expect(handle_storage(["rm", "minio", "-r"])).to_equal(1)
```

</details>

#### -r with unknown-alias-shaped full TARGET is rejected pre-network (parses as a local path, never remote)

- -r with unknown-alias-shaped full TARGET is rejected pre-network (parses as a local path, never remote)
- Verify: -r with unknown-alias-shaped full TARGET is rejected pre-network (parses as a local path, never remote)
   - Expected: handle_storage(["rm", "unknownalias/bucket/key.bin", "-r"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-r with unknown-alias-shaped full TARGET is rejected pre-network (parses as a local path, never remote)")
step("Verify: -r with unknown-alias-shaped full TARGET is rejected pre-network (parses as a local path, never remote)")
expect(handle_storage(["rm", "unknownalias/bucket/key.bin", "-r"])).to_equal(1)
```

</details>

#### mirror — validation-only paths, all pre-network

#### fewer than 2 positional args is a usage error

- fewer than 2 positional args is a usage error
- Verify: fewer than 2 positional args is a usage error
   - Expected: handle_storage(["mirror"]) equals `1`
   - Expected: handle_storage(["mirror", "src"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fewer than 2 positional args is a usage error")
step("Verify: fewer than 2 positional args is a usage error")
expect(handle_storage(["mirror"])).to_equal(1)
expect(handle_storage(["mirror", "src"])).to_equal(1)
```

</details>

#### local -> local is rejected (mirror requires exactly one local side)

- local -> local is rejected (mirror requires exactly one local side)
- Verify: local -> local is rejected (mirror requires exactly one local side)
   - Expected: handle_storage(["mirror", "/tmp/a", "/tmp/b"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("local -> local is rejected (mirror requires exactly one local side)")
step("Verify: local -> local is rejected (mirror requires exactly one local side)")
expect(handle_storage(["mirror", "/tmp/a", "/tmp/b"])).to_equal(1)
```

</details>

#### remote -> remote is rejected (mirror requires exactly one local side)

- remote -> remote is rejected (mirror requires exactly one local side)
- Verify: remote -> remote is rejected (mirror requires exactly one local side)
   - Expected: handle_storage(["mirror", "minio/bucket/a", "minio/bucket/b"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("remote -> remote is rejected (mirror requires exactly one local side)")
step("Verify: remote -> remote is rejected (mirror requires exactly one local side)")
expect(handle_storage(["mirror", "minio/bucket/a", "minio/bucket/b"])).to_equal(1)
```

</details>

#### upload direction with unknown-alias DST is rejected pre-network

- upload direction with unknown-alias DST is rejected pre-network
- Verify: upload direction with unknown-alias DST is rejected pre-network
   - Expected: handle_storage(["mirror", "/tmp/a", "unknownalias/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("upload direction with unknown-alias DST is rejected pre-network")
step("Verify: upload direction with unknown-alias DST is rejected pre-network")
expect(handle_storage(["mirror", "/tmp/a", "unknownalias/bucket"])).to_equal(1)
```

</details>

#### download direction with unknown-alias SRC is rejected pre-network

- download direction with unknown-alias SRC is rejected pre-network
- Verify: download direction with unknown-alias SRC is rejected pre-network
   - Expected: handle_storage(["mirror", "unknownalias/bucket", "/tmp/a"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("download direction with unknown-alias SRC is rejected pre-network")
step("Verify: download direction with unknown-alias SRC is rejected pre-network")
expect(handle_storage(["mirror", "unknownalias/bucket", "/tmp/a"])).to_equal(1)
```

</details>

#### upload direction with bucket-less DST is rejected before config access

- upload direction with bucket-less DST is rejected before config access
- Verify: upload direction with bucket-less DST is rejected before config access
   - Expected: handle_storage(["mirror", "/tmp/a", "minio"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("upload direction with bucket-less DST is rejected before config access")
step("Verify: upload direction with bucket-less DST is rejected before config access")
expect(handle_storage(["mirror", "/tmp/a", "minio"])).to_equal(1)
```

</details>

#### download direction with bucket-less SRC is rejected before config access

- download direction with bucket-less SRC is rejected before config access
- Verify: download direction with bucket-less SRC is rejected before config access
   - Expected: handle_storage(["mirror", "minio", "/tmp/a"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("download direction with bucket-less SRC is rejected before config access")
step("Verify: download direction with bucket-less SRC is rejected before config access")
expect(handle_storage(["mirror", "minio", "/tmp/a"])).to_equal(1)
```

</details>

#### _mirror_diff — pure size-only diff, no I/O (covers copy/skip/remove semantics both directions)

#### copies entries missing at the destination

- copies entries missing at the destination
- Verify: copies entries missing at the destination
   - Expected: plan.skipped equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("copies entries missing at the destination")
step("Verify: copies entries missing at the destination")
val source = [MirrorEntry(name: "a.txt", size: 10)]
val dest: [MirrorEntry] = []
val plan = _mirror_diff(source, dest, false)
expect(plan.to_copy).to_contain("a.txt")
expect(plan.skipped).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### copies entries present at the destination with a differing size

- copies entries present at the destination with a differing size
- Verify: copies entries present at the destination with a differing size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("copies entries present at the destination with a differing size")
step("Verify: copies entries present at the destination with a differing size")
val source = [MirrorEntry(name: "a.txt", size: 20)]
val dest = [MirrorEntry(name: "a.txt", size: 10)]
val plan = _mirror_diff(source, dest, false)
expect(plan.to_copy).to_contain("a.txt")
```

</details>

#### skips entries already in sync (same name, same size)

- skips entries already in sync (same name, same size)
- Verify: skips entries already in sync (same name, same size)
   - Expected: plan.to_copy.len() equals `0`
   - Expected: plan.skipped equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("skips entries already in sync (same name, same size)")
step("Verify: skips entries already in sync (same name, same size)")
val source = [MirrorEntry(name: "a.txt", size: 10)]
val dest = [MirrorEntry(name: "a.txt", size: 10)]
val plan = _mirror_diff(source, dest, false)
expect(plan.to_copy.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(plan.skipped).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### never populates to_remove without --remove (destination-only entries kept)

- never populates to_remove without --remove (destination-only entries kept)
- Verify: never populates to_remove without --remove (destination-only entries kept)
   - Expected: plan.to_remove.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never populates to_remove without --remove (destination-only entries kept)")
step("Verify: never populates to_remove without --remove (destination-only entries kept)")
val source: [MirrorEntry] = []
val dest = [MirrorEntry(name: "extra.txt", size: 5)]
val plan = _mirror_diff(source, dest, false)
expect(plan.to_remove.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### --remove deletes destination entries absent from the source

- --remove deletes destination entries absent from the source
- Verify: --remove deletes destination entries absent from the source
   - Expected: plan.to_copy.len() equals `0`
   - Expected: plan.skipped equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--remove deletes destination entries absent from the source")
step("Verify: --remove deletes destination entries absent from the source")
val source = [MirrorEntry(name: "keep.txt", size: 1)]
val dest = [MirrorEntry(name: "keep.txt", size: 1), MirrorEntry(name: "extra.txt", size: 5)]
val plan = _mirror_diff(source, dest, true)
expect(plan.to_remove).to_contain("extra.txt")
expect(plan.to_copy.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(plan.skipped).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### works symmetrically for the remote -> local direction (remote as source, local as dest)

- works symmetrically for the remote -> local direction (remote as source, local as dest)
- Verify: works symmetrically for the remote -> local direction (remote as source, local as dest)
   - Expected: plan.skipped equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("works symmetrically for the remote -> local direction (remote as source, local as dest)")
step("Verify: works symmetrically for the remote -> local direction (remote as source, local as dest)")
val remote_side = [MirrorEntry(name: "r.bin", size: 30), MirrorEntry(name: "same.bin", size: 4)]
val local_side = [MirrorEntry(name: "same.bin", size: 4)]
val plan = _mirror_diff(remote_side, local_side, false)
expect(plan.to_copy).to_contain("r.bin")
expect(plan.skipped).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### _mirror_bound_exceeded — pure >1000 safety-cap check, no I/O

#### false when both sides are within the cap

- false when both sides are within the cap
- Verify: false when both sides are within the cap
   - Expected: _mirror_bound_exceeded(5, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("false when both sides are within the cap")
step("Verify: false when both sides are within the cap")
expect(_mirror_bound_exceeded(5, 5)).to_equal(false)
```

</details>

#### true when the source side alone exceeds 1000

- true when the source side alone exceeds 1000
- Verify: true when the source side alone exceeds 1000
   - Expected: _mirror_bound_exceeded(1001, 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("true when the source side alone exceeds 1000")
step("Verify: true when the source side alone exceeds 1000")
expect(_mirror_bound_exceeded(1001, 5)).to_equal(true)
```

</details>

#### true when the destination side alone exceeds 1000

- true when the destination side alone exceeds 1000
- Verify: true when the destination side alone exceeds 1000
   - Expected: _mirror_bound_exceeded(5, 1001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("true when the destination side alone exceeds 1000")
step("Verify: true when the destination side alone exceeds 1000")
expect(_mirror_bound_exceeded(5, 1001)).to_equal(true)
```

</details>

#### false exactly at the 1000 boundary

- false exactly at the 1000 boundary
- Verify: false exactly at the 1000 boundary
   - Expected: _mirror_bound_exceeded(1000, 1000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("false exactly at the 1000 boundary")
step("Verify: false exactly at the 1000 boundary")
expect(_mirror_bound_exceeded(1000, 1000)).to_equal(false)
```

</details>

#### _mirror_json_summary — --json summary shape, built via concatenation

#### renders the full non-dry-run shape

- renders the full non-dry-run shape
- Verify: renders the full non-dry-run shape
   - Expected: _mirror_json_summary(3, 1, 2, false) equals `{"copied":3,"removed":1,"skipped":2,"dry_run":false}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders the full non-dry-run shape")
step("Verify: renders the full non-dry-run shape")
expect(_mirror_json_summary(3, 1, 2, false)).to_equal("{\"copied\":3,\"removed\":1,\"skipped\":2,\"dry_run\":false}")
```

</details>

#### renders dry_run:true when planning only

- renders dry_run:true when planning only
- Verify: renders dry_run:true when planning only
   - Expected: _mirror_json_summary(3, 1, 2, true) equals `{"copied":3,"removed":1,"skipped":2,"dry_run":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders dry_run:true when planning only")
step("Verify: renders dry_run:true when planning only")
expect(_mirror_json_summary(3, 1, 2, true)).to_equal("{\"copied\":3,\"removed\":1,\"skipped\":2,\"dry_run\":true}")
```

</details>

#### renders zeros when nothing needed action

- renders zeros when nothing needed action
- Verify: renders zeros when nothing needed action
   - Expected: _mirror_json_summary(0, 0, 0, false) equals `{"copied":0,"removed":0,"skipped":0,"dry_run":false}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders zeros when nothing needed action")
step("Verify: renders zeros when nothing needed action")
expect(_mirror_json_summary(0, 0, 0, false)).to_equal("{\"copied\":0,\"removed\":0,\"skipped\":0,\"dry_run\":false}")
```

</details>

#### presign / presign-put — validation-only paths

#### presign missing TARGET is a usage error

- presign missing TARGET is a usage error
- Verify: presign missing TARGET is a usage error
   - Expected: handle_storage(["presign"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("presign missing TARGET is a usage error")
step("Verify: presign missing TARGET is a usage error")
expect(handle_storage(["presign"])).to_equal(1)
```

</details>

#### presign bucket-only TARGET (no key) is rejected

- presign bucket-only TARGET (no key) is rejected
- Verify: presign bucket-only TARGET (no key) is rejected
   - Expected: handle_storage(["presign", "minio/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("presign bucket-only TARGET (no key) is rejected")
step("Verify: presign bucket-only TARGET (no key) is rejected")
expect(handle_storage(["presign", "minio/bucket"])).to_equal(1)
```

</details>

#### presign-put bucket-only TARGET (no key) is rejected

- presign-put bucket-only TARGET (no key) is rejected
- Verify: presign-put bucket-only TARGET (no key) is rejected
   - Expected: handle_storage(["presign-put", "minio/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("presign-put bucket-only TARGET (no key) is rejected")
step("Verify: presign-put bucket-only TARGET (no key) is rejected")
expect(handle_storage(["presign-put", "minio/bucket"])).to_equal(1)
```

</details>

#### du — validation-only paths

#### missing TARGET is a usage error

- missing TARGET is a usage error
- Verify: missing TARGET is a usage error
   - Expected: handle_storage(["du"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("missing TARGET is a usage error")
step("Verify: missing TARGET is a usage error")
expect(handle_storage(["du"])).to_equal(1)
```

</details>

#### alias-only TARGET (no bucket) is rejected

- alias-only TARGET (no bucket) is rejected
- Verify: alias-only TARGET (no bucket) is rejected
   - Expected: handle_storage(["du", "minio"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("alias-only TARGET (no bucket) is rejected")
step("Verify: alias-only TARGET (no bucket) is rejected")
expect(handle_storage(["du", "minio"])).to_equal(1)
```

</details>

#### unknown alias with bucket is rejected pre-network

- unknown alias with bucket is rejected pre-network
- Verify: unknown alias with bucket is rejected pre-network
   - Expected: handle_storage(["du", "unknownalias/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown alias with bucket is rejected pre-network")
step("Verify: unknown alias with bucket is rejected pre-network")
expect(handle_storage(["du", "unknownalias/bucket"])).to_equal(1)
```

</details>

#### health — validation-only paths

#### unknown alias is rejected before touching config at all

- unknown alias is rejected before touching config at all
- Verify: unknown alias is rejected before touching config at all
   - Expected: handle_storage(["health", "unknownalias"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown alias is rejected before touching config at all")
step("Verify: unknown alias is rejected before touching config at all")
expect(handle_storage(["health", "unknownalias"])).to_equal(1)
```

</details>

#### cp — direction inference + validation, all pre-network

#### fewer than 2 positional args is a usage error

- fewer than 2 positional args is a usage error
- Verify: fewer than 2 positional args is a usage error
   - Expected: handle_storage(["cp", "onlyone"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fewer than 2 positional args is a usage error")
step("Verify: fewer than 2 positional args is a usage error")
expect(handle_storage(["cp", "onlyone"])).to_equal(1)
```

</details>

#### local -> local is rejected (error_local_local)

- local -> local is rejected (error_local_local)
- Verify: local -> local is rejected (error_local_local)
   - Expected: handle_storage(["cp", "/tmp/a.bin", "/tmp/b.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("local -> local is rejected (error_local_local)")
step("Verify: local -> local is rejected (error_local_local)")
expect(handle_storage(["cp", "/tmp/a.bin", "/tmp/b.bin"])).to_equal(1)
```

</details>

#### remote -> remote is rejected (error_remote_remote)

- remote -> remote is rejected (error_remote_remote)
- Verify: remote -> remote is rejected (error_remote_remote)
   - Expected: handle_storage(["cp", "minio/bucket/a.bin", "minio/bucket/b.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("remote -> remote is rejected (error_remote_remote)")
step("Verify: remote -> remote is rejected (error_remote_remote)")
expect(handle_storage(["cp", "minio/bucket/a.bin", "minio/bucket/b.bin"])).to_equal(1)
```

</details>

#### upload direction with unknown-alias DST is rejected pre-network

- upload direction with unknown-alias DST is rejected pre-network
- Verify: upload direction with unknown-alias DST is rejected pre-network
   - Expected: handle_storage(["cp", "/tmp/a.bin", "unknownalias/bucket/key.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("upload direction with unknown-alias DST is rejected pre-network")
step("Verify: upload direction with unknown-alias DST is rejected pre-network")
expect(handle_storage(["cp", "/tmp/a.bin", "unknownalias/bucket/key.bin"])).to_equal(1)
```

</details>

#### download direction with unknown-alias SRC is rejected pre-network

- download direction with unknown-alias SRC is rejected pre-network
- Verify: download direction with unknown-alias SRC is rejected pre-network
   - Expected: handle_storage(["cp", "unknownalias/bucket/key.bin", "/tmp/out.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("download direction with unknown-alias SRC is rejected pre-network")
step("Verify: download direction with unknown-alias SRC is rejected pre-network")
expect(handle_storage(["cp", "unknownalias/bucket/key.bin", "/tmp/out.bin"])).to_equal(1)
```

</details>

#### upload direction with bucket-only DST (no key) is rejected before config access

- upload direction with bucket-only DST (no key) is rejected before config access
- Verify: upload direction with bucket-only DST (no key) is rejected before config access
   - Expected: handle_storage(["cp", "/tmp/a.bin", "minio/bucket"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("upload direction with bucket-only DST (no key) is rejected before config access")
step("Verify: upload direction with bucket-only DST (no key) is rejected before config access")
expect(handle_storage(["cp", "/tmp/a.bin", "minio/bucket"])).to_equal(1)
```

</details>

#### upload direction with a nonexistent SRC file is rejected pre-network, even with a real alias-shaped DST (file_exists is checked before resolve_alias_config — real std.io_runtime, not the old mock file_ops)

- upload direction with a nonexistent SRC file is rejected pre-network, even with a real alias-shaped DST (file_exists is checked before resolve_alias_config — real std.io_runtime, not the old mock file_ops)
- Verify: upload direction with a nonexistent SRC file is rejected pre-network, even with a real alias-shaped DST (file_exists is checked before resolve_alias_config — real std.io_runtime, not the old mock file_ops)
   - Expected: handle_storage(["cp", "/tmp/definitely-does-not-exist-cmd-storage-cp-spec.bin", "minio/bucket/key.bin"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("upload direction with a nonexistent SRC file is rejected pre-network, even with a real alias-shaped DST (file_exists is checked before resolve_alias_config — real std.io_runtime, not the old mock file_ops)")
step("Verify: upload direction with a nonexistent SRC file is rejected pre-network, even with a real alias-shaped DST (file_exists is checked before resolve_alias_config — real std.io_runtime, not the old mock file_ops)")
expect(handle_storage(["cp", "/tmp/definitely-does-not-exist-cmd-storage-cp-spec.bin", "minio/bucket/key.bin"])).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-DEVHUB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25f18a58d13c5405304c27b6706386b3853d499eedaef235049b4e4ea668c59c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25f18a58d13c5405304c27b6706386b3853d499eedaef235049b4e4ea668c59c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25f18a58d13c5405304c27b6706386b3853d499eedaef235049b4e4ea668c59c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/cmd_storage_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/cmd_storage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/cmd_storage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/cmd_storage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/cmd_storage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 43 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/cmd_storage_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no args prints help and returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_storage_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--help returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_storage_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown verb returns 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
