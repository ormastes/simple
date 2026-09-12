# `me` mutations are silently dropped when the receiver was bound from an Optional-typed expression

- Status: OPEN (2026-09-12)
- Severity: HIGH — silent wrong answer, no warning, no diagnostic
- Area: Rust seed interpreter (`src/compiler_rust`), method dispatch / optional unwrap
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5`
- Found while isolating `vulkan_ffi_ledger_lost_under_spec_harness_2026-08-09.md`,
  which is one instance of this defect.

## Symptom

Calling a `me` (mutating) method on a value bound from an **Optional-returning**
expression mutates a throwaway copy. The write-back never reaches the binding, so
every later read sees the original state. Nothing warns; the call returns normally.

## Minimal repro (self-contained, no FFI, no optional field)

```simple
class OptLedger:
    _count: i64 = 0
    _last: text = ""

impl OptLedger:
    static fn make_plain() -> OptLedger:
        OptLedger(_count: 0, _last: "")
    static fn make_opt() -> OptLedger?:          # <-- the ONLY difference
        OptLedger(_count: 0, _last: "")
    fn count() -> i64:
        self._count
    me record(op: text) -> bool:
        self._count = self._count + 1
        self._last = op
        false
```

Under `bin/simple test ... --no-session-daemon`:

```
PLAINCTOR count=2 last=[shutdown]      # static fn -> OptLedger      CORRECT
OPTCTOR   count=0 last=[]              # static fn -> OptLedger?     WRONG
```

## Narrowing (all measured, same binary, same run)

| variant | result |
|---|---|
| receiver from `static fn -> T` | `count=2` correct |
| receiver from `static fn -> T?` | `count=0` **lost** |
| same, with an explicit `if l == nil: return` guard before the call | `count=0` **still lost** |
| `val l: T = o!` rebound into a non-optional local, then mutate | `count=2` correct |
| two `self._count = self._count + 1` inside ONE `me` call | `count=0` **lost** |

The last row is the decisive one: even mutations made within a single `me` call are
gone afterwards, so the defect is in the **write-back of the unwrapped receiver**,
not in sequencing between calls. The nil-guard row shows a narrowing `if` does not
re-bind the local to a non-optional value, so guarding does not help.

## Eliminated (do not re-test these)

Each was run as a minimal class under the same harness and behaved **correctly**:
a plain class with a `me` mutator; a class holding a `DynLib?` foreign-handle
field; a `me` wrapper calling another `me` method on `self`; a `me` wrapper that
`match`es on an enum field before calling the inner `me` method. The
`vulkan_ffi_ledger_lost_under_spec_harness` record proposed the `DynLib?` field as
"the cheapest discriminator" — it is not the trigger; the Optional-typed
constructor return is.

## Workaround (pure Simple, available today)

Rebind through `!` into an explicitly non-optional local before mutating:

```simple
val maybe = Thing.create()          # -> Thing?
if maybe == nil:
    return
val thing: Thing = maybe!           # mutations now stick
```

## Why this is not fixed here

The write-back lives in the seed interpreter's method dispatch, which is Rust
(`src/compiler_rust`), outside the pure-Simple scope of this pass. Filed with the
isolation above so whoever owns the interpreter can go straight to the unwrap path.

## Blast radius

Any `me`-method state accumulation on a value obtained from an Optional-returning
constructor is silently inert. The repo convention `static fn create*() -> T?` is
common, so this is not a one-class defect. Known instance:
`src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl` (`VulkanDynFfi.create_dynamic`),
whose rejection ledger is inert and whose spec
`test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl` is RED for exactly this reason.
