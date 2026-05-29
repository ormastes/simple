# trait forwarding
*Source:* `test/feature/usage/trait_forwarding_spec.spl`

## Feature: Trait Alias Forwarding (Phase 3)

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | delegates immutable method to field | pass |
| 2 | delegates mutable method to field | pass |
| 3 | forwards to multiple different fields | pass |
| 4 | forwards methods that take arguments | pass |
| 5 | preserves state across mutable forwarding calls | pass |
| 6 | returns correct values through forwarding chain | pass |
| 7 | forwarding works alongside own methods | pass |
| 8 | forwarding with mixed mutable and immutable methods | pass |

**Example:** delegates immutable method to field
    Given val w = Wrapper(inner: Inner(data: 42))
    Then  expect(w.get_data()).to_equal(42)

**Example:** delegates mutable method to field
    Given var c = Container(items: MutableList(length: 0, last_added: 0))
    Then  expect(c.size()).to_equal(1)

**Example:** forwards to multiple different fields
    Given var app = App(log: Logger(entries: 0, prefix: "APP"), fmt: Formatter(style: "bold"))
    Then  expect(app.entry_count()).to_equal(1)
    Given val styled = app.style_text("test")
    Then  expect(styled).to_equal("bold: test")

**Example:** forwards methods that take arguments
    Given val w = MathWrapper(calc: Calculator(x: 10, y: 0))
    Then  expect(w.add(3, 4)).to_equal(17)
    Then  expect(w.multiply(5, 6)).to_equal(30)

**Example:** preserves state across mutable forwarding calls
    Given var tc = TrackedCounter(counter: Counter(n: 0))
    Then  expect(tc.value()).to_equal(2)

**Example:** returns correct values through forwarding chain
    Given val svc = Service(store: DataStore(name: "myapp", version: 3))
    Then  expect(svc.get_name()).to_equal("myapp")
    Then  expect(svc.get_version()).to_equal(3)
    Then  expect(svc.describe()).to_equal("myapp v3")

**Example:** forwarding works alongside own methods
    Given val car = Car(engine: Engine(power: 200), color: "red")
    Then  expect(car.horsepower()).to_equal(200)
    Then  expect(car.get_color()).to_equal("red")
    Then  expect(car.summary()).to_equal("red car with 200hp")

**Example:** forwarding with mixed mutable and immutable methods
    Given var s = Stream(buf: Buffer(content: "", size: 0))
    Then  expect(s.read()).to_equal("hello world")
    Then  expect(s.count()).to_equal(2)


