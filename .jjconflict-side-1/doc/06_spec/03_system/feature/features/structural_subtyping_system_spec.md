# Structural Subtyping System Specification

> 1. fn get name

<!-- sdn-diagram:id=structural_subtyping_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=structural_subtyping_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

structural_subtyping_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=structural_subtyping_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Structural Subtyping System Specification

## Scenarios

### Structural Subtyping: Phase 1 - Basic compatibility

#### struct with same fields is compatible

1. fn get name
2. fn make minimal name
3. fn make extended name
   - Expected: get_name(m) equals `minimal`
   - Expected: get_name(e) equals `extended`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Minimal:
    name: text
struct Extended:
    name: text
    extra: i64

fn get_name(obj: Minimal) -> text:
    obj.name

fn make_minimal_name() -> text: "minimal"
fn make_extended_name() -> text: "extended"

val m = Minimal(name: "minimal")
val e = Extended(name: "extended", extra: 42)
expect(get_name(m)).to_equal("minimal")
expect(get_name(e)).to_equal("extended")
```

</details>

#### struct field access works regardless of type name

1. compute fn: fn
2. compute fn: fn
3. extra fn: fn
4. fn double
5. fn get info
   - Expected: f(5) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct PortA:
    compute_fn: fn(i64) -> i64
struct PortB:
    compute_fn: fn(i64) -> i64
    extra_fn: fn() -> text

fn double(x: i64) -> i64: x * 2
fn get_info() -> text: "info"

val b = PortB(compute_fn: double, extra_fn: get_info)
val f = b.compute_fn
expect(f(5)).to_equal(10)
```

</details>

#### extended struct can be passed to function expecting base struct

1. save fn: fn
2. find fn: fn
3. save fn: fn
4. find fn: fn
5. count fn: fn
6. fn process base
7. f
8. fn do save
9. fn do find
10. fn do count
   - Expected: result equals `ext:item-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct BasePort:
    save_fn: fn(text) -> bool
    find_fn: fn(text) -> text

struct ExtendedRepo:
    save_fn: fn(text) -> bool
    find_fn: fn(text) -> text
    count_fn: fn() -> i64

fn process_base(repo: BasePort) -> text:
    val f = repo.find_fn
    f("item-42")

fn do_save(x: text) -> bool: true
fn do_find(x: text) -> text: "ext:" + x
fn do_count() -> i64: 0

val extended = ExtendedRepo(
    save_fn: do_save,
    find_fn: do_find,
    count_fn: do_count
)
val result = process_base(extended)
expect(result).to_equal("ext:item-42")
```

</details>

#### exact type match still works after structural subtyping support

1. value fn: fn
2. fn get value
3. f
4. fn return 42
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct ExactPort:
    value_fn: fn() -> i64

fn get_value(p: ExactPort) -> i64:
    val f = p.value_fn
    f()

fn return_42() -> i64: 42
val port = ExactPort(value_fn: return_42)
val result = get_value(port)
expect(result).to_equal(42)
```

</details>

### Structural Subtyping: Phase 2 - Port satisfaction

#### extended repo satisfies order repo port fields

1. save fn: fn
2. find fn: fn
3. save fn: fn
4. find fn: fn
5. count fn: fn
6. fn always save
7. fn find by id
8. fn count all
   - Expected: sf("order1") is true
   - Expected: ff("123") equals `order:123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct OrderRepoPort:
    save_fn: fn(text) -> bool
    find_fn: fn(text) -> text

struct ExtendedOrderRepo:
    save_fn: fn(text) -> bool
    find_fn: fn(text) -> text
    count_fn: fn() -> i64

fn always_save(order: text) -> bool: true
fn find_by_id(id: text) -> text: "order:{id}"
fn count_all() -> i64: 99

val repo = ExtendedOrderRepo(
    save_fn: always_save,
    find_fn: find_by_id,
    count_fn: count_all
)

val sf = repo.save_fn
val ff = repo.find_fn
expect(sf("order1")).to_equal(true)
expect(ff("123")).to_equal("order:123")
```

</details>

#### structural subtyping works for multiple struct params

1. log fn: fn
2. store fn: fn
3. log fn: fn
4. level fn: fn
5. store fn: fn
6. flush fn: fn
7. fn pipeline
8. lf
9. sf
10. fn do log
11. fn do store
12. fn get level
13. fn do flush
   - Expected: result equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct LogPort:
    log_fn: fn(text)

struct StoragePort:
    store_fn: fn(text)

struct ExtendedLog:
    log_fn: fn(text)
    level_fn: fn() -> i64

struct ExtendedStorage:
    store_fn: fn(text)
    flush_fn: fn() -> bool

fn pipeline(logger: LogPort, storage: StoragePort) -> text:
    val lf = logger.log_fn
    lf("start")
    val sf = storage.store_fn
    sf("data")
    "done"

fn do_log(msg: text): ()
fn do_store(d: text): ()
fn get_level() -> i64: 2
fn do_flush() -> bool: true

val ext_log = ExtendedLog(log_fn: do_log, level_fn: get_level)
val ext_storage = ExtendedStorage(store_fn: do_store, flush_fn: do_flush)
val result = pipeline(ext_log, ext_storage)
expect(result).to_equal("done")
```

</details>

#### struct with extra non-fn field satisfies port

1. fn read data
2. d name + ":" + str
   - Expected: result equals `test:5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct DataPort:
    name: text
    count: i64

struct RichData:
    name: text
    count: i64
    extra: text

fn read_data(d: DataPort) -> text:
    d.name + ":" + str(d.count)

val rich = RichData(name: "test", count: 5, extra: "unused")
val result = read_data(rich)
expect(result).to_equal("test:5")
```

</details>

#### field access on the passed structurally-compatible struct works

1. read fn: fn
2. read fn: fn
3. path fn: fn
4. fn do read
5. f
6. fn read content
7. fn get path
   - Expected: content equals `file-content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct ReaderPort:
    read_fn: fn() -> text

struct FileReader:
    read_fn: fn() -> text
    path_fn: fn() -> text

fn do_read(r: ReaderPort) -> text:
    val f = r.read_fn
    f()

fn read_content() -> text: "file-content"
fn get_path() -> text: "/tmp/test.txt"

val reader = FileReader(
    read_fn: read_content,
    path_fn: get_path
)
val content = do_read(reader)
expect(content).to_equal("file-content")
```

</details>

### Structural Subtyping: Phase 3 - System integration

#### port-based dependency injection pattern works

1. query fn: fn
2. insert fn: fn
3. query fn: fn
4. insert fn: fn
5. fn run service
6. ins
7. qry
8. fn mock query
9. fn mock insert
   - Expected: result equals `mock_result_for:all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct DatabasePort:
    query_fn: fn(text) -> text
    insert_fn: fn(text) -> bool

struct MockDatabase:
    query_fn: fn(text) -> text
    insert_fn: fn(text) -> bool
    call_count: i64

fn run_service(db: DatabasePort) -> text:
    val ins = db.insert_fn
    ins("record1")
    val qry = db.query_fn
    qry("all")

fn mock_query(q: text) -> text: "mock_result_for:" + q
fn mock_insert(r: text) -> bool: true

val mock_db = MockDatabase(
    query_fn: mock_query,
    insert_fn: mock_insert,
    call_count: 0
)
val result = run_service(mock_db)
expect(result).to_equal("mock_result_for:all")
```

</details>

#### chained structural compatibility with two levels of extension

1. basic fn: fn
2. basic fn: fn
3. extra fn: fn
4. basic fn: fn
5. extra fn: fn
6. advanced fn: fn
7. fn use level1
8. f
9. fn ret num
10. fn ret str
11. fn double it
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Level1:
    basic_fn: fn() -> i64

struct Level2:
    basic_fn: fn() -> i64
    extra_fn: fn() -> text

struct Level3:
    basic_fn: fn() -> i64
    extra_fn: fn() -> text
    advanced_fn: fn(i64) -> i64

fn use_level1(p: Level1) -> i64:
    val f = p.basic_fn
    f()

fn ret_num() -> i64: 100
fn ret_str() -> text: "extra"
fn double_it(x: i64) -> i64: x * 2

val l3 = Level3(basic_fn: ret_num, extra_fn: ret_str, advanced_fn: double_it)
val result = use_level1(l3)
expect(result).to_equal(100)
```

</details>

#### struct satisfies interface when passed as function argument

1. find fn: fn
2. find fn: fn
3. fn find user
4. f
5. fn lookup user
   - Expected: result equals `user_42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Repository:
    find_fn: fn(i64) -> text

struct UserRepository:
    find_fn: fn(i64) -> text
    name: text

fn find_user(repo: Repository, user_id: i64) -> text:
    val f = repo.find_fn
    f(user_id)

fn lookup_user(id: i64) -> text: "user_" + str(id)

val user_repo = UserRepository(find_fn: lookup_user, name: "users")
val result = find_user(user_repo, 42)
expect(result).to_equal("user_42")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/structural_subtyping_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Structural Subtyping: Phase 1 - Basic compatibility
- Structural Subtyping: Phase 2 - Port satisfaction
- Structural Subtyping: Phase 3 - System integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
