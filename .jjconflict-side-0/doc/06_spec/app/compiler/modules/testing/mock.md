Here’s a comprehensive design proposal for a mock library suitable for the Simple language (the toy language in your GitHub repo) based on common mocking concepts and limitations seen in established tools such as RSpec Mocks, Mockito, and mainstream mock frameworks.

0. Definitions and Core Concepts

Before proposing an API and design, let’s clarify terminology:

Test Double: generic term for any stand-in for a real object (Mocks, Stubs, Fakes, Spies) .

Stub: provides canned responses to method/function calls with no behavior verification.

Mock: doubles with behavior verification — test can assert that certain calls did happen .

Spy: records interactions for later verification.

Fake: a lighter or limited implementation of a real type for testing.


Many mock libraries treat all these under a unified interface (e.g., Jest, Mockito, Mockery) to make usage easier, but separating concerns clarifies semantics and reduces coupling.

1. Goals & Requirements

The mock library should:

1. Be available as a standard library or core package in Simple so that testing and mocking are idiomatic.


2. Allow creation of test doubles that stand in for functions, methods, and interfaces.


3. Support:

Stubbing return values

Verification of calls (behavior)

Argument matching

Optional spies

Chained call mocks



4. Provide type safety and compile-time checks whenever possible (given Simple is statically typed).


5. Have an ergonomic DSL for expressing mocks — influenced by RSpec’s expressive style .



2. Mock Library API Design

Below is a language-level mock library design, including key types, operations and a minimal test syntax.

2.1 Core Types

// The core test double type
mock Double<T>

// A spy double: records calls and optionally calls through
spy Spy<T>

Here, T is a type or interface that a mock will implement.


---

2.2 Creating Doubles

let userDaoMock = mock UserDao
let serviceSpy  = spy MyService

mock <Type>: create a mock implementing the interface or class.

spy <Type>: create a spy that wraps a real object (optional) to record calls.


This aligns with typical mocking patterns where mocks replace dependencies and spies record interactions.


---

2.3 Setting Behavior

Return value stubbing:

userDaoMock.when(:findById).with(123).returns(User(id:123, name:"Alice"))

when(method): identifies a method to configure.

with(args…): argument pattern match.

returns(value): fixed return value for that method invocation.


Function Call Order and Multiple Returns:

userDaoMock.when(:nextVal).returnsOnce(1).returns(2)

.returnsOnce: next call yields 1, then default behavior.



---

2.4 Spies & Verification

After exercise, tests can verify interactions:

serviceSpy.verify(:process).called()
serviceSpy.verify(:process).calledTimes(3)
serviceSpy.verify(:process).calledWith(123)

.called(): assert that method was called at least once.

.calledTimes(n): exact count.

.calledWith(...): verify specific argument set.


Spies record all calls; mocks can optionally record as needed. A spy may wrap a real object or be purely a recording proxy.


---

2.5 Argument Matchers

Support flexible matching:

userDaoMock.when(:save).with(any(), gt(10)).returns(true)

Matchers like any(), gt(x), lt(x) make specifying expectations easier.


---

2.6 DSL Example

test "Should notify when user created" {
    let notifier = mock Notifier
    let repo     = mock UserRepository

    repo.when(:save).with(any(User)).returns(User(id:1, name:"Bob"))
    notifier.when(:notify).returns()

    let service  = UserService(repo, notifier)
    service.createUser("Bob")

    notifier.verify(:notify).called()
}

This DSL reads clearly and shows standard patterns found in RSpec-style mocks.


---

3. Design Considerations

3.1 Type Safety

Mocks must ensure that the methods configured actually exist on the target type. The compiler can check when(:methodName) against the interface of T.

3.2 Behavioral vs State Verification

Mocks should support both:

State verification: what did the mock return or how did it behave

Behavior verification: what methods were called
Some libraries blur these (RSpec doubles, Mockito, etc.) but distinguishing them improves clarity.


3.3 Test Isolation & Cleanup

Mocks should automatically reset expectations between tests. A beforeEach/afterEach style hook may be used.

3.4 Deep Call Chains

Handling nested method calls in mocks can be tricky (“mock train wrecks”). The API should allow specification of nested returns:

let nested = mock Library
nested.when(:getHeadLibrarian().getName()).returns("Jane")

Language support for nested spec DSL is a bonus.


---

4. Limitations & Future Extensions

Current limitations to address:

Mocking deep nested structures needs careful API design.

Automatic generation of mocks from interfaces where none are explicitly defined.

Support for async or concurrency (actors) mocking as Simple grows.


Potential extensions:

Contract-based mocking: derived from type definitions.

Property based mock generation.

Record/Replay modes.



---

5. Summary

This mock library design for Simple provides:

1. Type-safe creation of test doubles (mocks, spies).


2. Expressive configuration of behavior and verification, inspired by RSpec and mainstream mock frameworks .


3. Clear DSL for tests, enabling simple and readable test code.



It can grow into a core part of the language’s testing ecosystem, enabling robust unit testing with isolation and clear assertions about interactions.

If you want, I can also generate a reference implementation (syntax and sample code) of this mock library in the Simple language.
