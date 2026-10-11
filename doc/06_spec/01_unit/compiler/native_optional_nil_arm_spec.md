# Native Optional absence-arm diagnostic fixtures

Authored manual, not generated SSpec output. The six fixtures below are executable native entry sources with real exit-code checks. Each recorded execution projected its exact bytes to `src/app/probe/main.spl`; the imported production compiler was retained80030. The repository fixture path is portable source storage, not a claim that its module name was the compiled owner.

On retained80030, three original nil-pattern sources reproduce MIR rejection; three explicit-None counterparts emit objects and their real authored mains pass. The scalar pair checks Some(3), Some(0) and nil; the reordered pair retains identical checks with absence first. The array pair checks empty Some distinct from nil, each high-bit byte and the original arrays after matching. Positive executable evidence is3/3, representing14 exit-code assertions. Original nil sources must become compile-and-run positives once a producer containing the real fix is admitted; their expected failure is specific to80030, not the language contract.

Setup preserves nil construction, native arrays, the canonical runtime, exact producer/tool/source pins and direct process containment. The originals are not rewritten to satisfy a parser. No production runtime stub, constant replacement, fake main or seed fallback is used. The original module0424 final cycle3 now emits its real library object with all nine entry functions; its three-owner cache and snapshot bindings passed the retained audit. These fixtures and that object do not prove every reader cast/string conversion or whole-suite behavior.

## explicit_none.spl

Source SHA256 `0223e2be97f4eba97cdd92ec09dccbca6bc6cef3aa8e82999b695fb081ae41b6`. Full actual setup and authored checks:

```simple
fn choose(value: i64?) -> i64:
    match value:
        case Some(raw): raw
        case None: -1

fn main() -> i64:
    if choose(Some(3)) != 3: return 11
    if choose(Some(0)) != 0: return 12
    if choose(nil) != -1: return 13
    print "optional-arm-probe-ok"
    0
```

## explicit_none_first.spl

Source SHA256 `760a2f7b06750273305e4627034ad7c4723dd897616b38ea430e00040b9af2ed`. Full actual setup and authored checks:

```simple
fn choose(value: i64?) -> i64:
    match value:
        case None: -1
        case Some(raw): raw

fn main() -> i64:
    if choose(Some(3)) != 3: return 11
    if choose(Some(0)) != 0: return 12
    if choose(nil) != -1: return 13
    print "optional-arm-probe-ok"
    0
```

## original_nil.spl

Source SHA256 `f87efe0749654f191a95e9bc7744ecfc12a9630cccda7e7a5fd10fe9ea2e5075`. Full actual setup and authored checks:

```simple
fn choose(value: i64?) -> i64:
    match value:
        case Some(raw): raw
        case nil: -1

fn main() -> i64:
    if choose(Some(3)) != 3: return 11
    if choose(Some(0)) != 0: return 12
    if choose(nil) != -1: return 13
    print "optional-arm-probe-ok"
    0
```

## original_nil_first.spl

Source SHA256 `5faa306058110fe1f09353017d7bea879b81ac385a98f9c10e1fac2667493404`. Full actual setup and authored checks:

```simple
fn choose(value: i64?) -> i64:
    match value:
        case nil: -1
        case Some(raw): raw

fn main() -> i64:
    if choose(Some(3)) != 3: return 11
    if choose(Some(0)) != 0: return 12
    if choose(nil) != -1: return 13
    print "optional-arm-probe-ok"
    0
```

## explicit_none_bytes.spl

Source SHA256 `d8e85bd75283904666dc875cb7fb70d8c802c0e6bc5472f402b2705f50d628df`. Full actual setup and authored checks:

```simple
# New boxed-payload prevention criterion. No original scalar criterion is rerun.
fn classify(value: [u8]?) -> i64:
    match value:
        case Some(raw):
            if raw.len() == 0:
                return 0
            if raw.len() != 3:
                return -2
            if raw[0] != 0x7f:
                return -3
            if raw[1] != 0x80:
                return -4
            if raw[2] != 0xff:
                return -5
            1
        case None: -1

fn absent_bytes() -> [u8]?:
    nil

fn main() -> i64:
    val empty: [u8] = []
    val payload: [u8] = [0x7f, 0x80, 0xff]
    if classify(Some(empty)) != 0:
        return 11
    if classify(Some(payload)) != 1:
        return 12
    if classify(absent_bytes()) != -1:
        return 13
    if empty.len() != 0:
        return 14
    if payload.len() != 3:
        return 15
    if payload[0] != 0x7f:
        return 16
    if payload[1] != 0x80:
        return 17
    if payload[2] != 0xff:
        return 18
    print "array-optional-probe-ok"
    0
```

## original_nil_bytes.spl

Source SHA256 `239cff24fed1371b24486a9684b845e4ad43d5ce3f96ae403c4d912754d6c07f`. Full actual setup and authored checks:

```simple
# New boxed-payload prevention criterion. No original scalar criterion is rerun.
fn classify(value: [u8]?) -> i64:
    match value:
        case Some(raw):
            if raw.len() == 0:
                return 0
            if raw.len() != 3:
                return -2
            if raw[0] != 0x7f:
                return -3
            if raw[1] != 0x80:
                return -4
            if raw[2] != 0xff:
                return -5
            1
        case nil: -1

fn absent_bytes() -> [u8]?:
    nil

fn main() -> i64:
    val empty: [u8] = []
    val payload: [u8] = [0x7f, 0x80, 0xff]
    if classify(Some(empty)) != 0:
        return 11
    if classify(Some(payload)) != 1:
        return 12
    if classify(absent_bytes()) != -1:
        return 13
    if empty.len() != 0:
        return 14
    if payload.len() != 3:
        return 15
    if payload[0] != 0x7f:
        return 16
    if payload[1] != 0x80:
        return 17
    if payload[2] != 0xff:
        return 18
    print "array-optional-probe-ok"
    0
```
