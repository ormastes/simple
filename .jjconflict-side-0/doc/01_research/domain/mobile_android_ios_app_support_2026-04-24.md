<!-- codex-research -->
# Domain Research: Android and iOS App Support

Date: 2026-04-24

Related local research: `doc/01_research/local/mobile_android_ios_app_support_2026-04-24.md`

## Executive Summary

For this repo, the best default strategy is:

- shared language/runtime/core
- native mobile shells
- native UI on each platform

Concretely, that means Android should bias toward Jetpack Compose and iOS/iPadOS toward SwiftUI, while Simple provides shared business logic, rendering-neutral app state, generated bindings, or a C ABI bridge.

That approach fits both current platform guidance and the repo’s current architecture better than forcing a single cross-platform GUI stack.

## What “Support Android and iOS App Development” Actually Means

There are four materially different goals:

| Goal | What it means |
|---|---|
| Native shell support | A Simple app can run inside Android/iOS host apps and talk to native UI |
| Shared business logic | App logic, models, networking, storage rules, and state machines are shared |
| Shared UI | One UI description or widget tree runs on both platforms |
| Full mobile platform lane | Build, package, sign, test, and publish mobile apps from the main toolchain |

The repo is currently closest to the first two goals. The fourth goal is a much larger platform program.

## Platform Guidance That Matters

### Android

Android’s official guidance is strongly adaptive-layout and large-screen oriented:

- Jetpack Compose adaptive layouts: <https://developer.android.com/develop/ui/compose/layouts/adaptive>
- Large-screen app quality guidance: <https://developer.android.com/docs/quality-guidelines/archive/adaptive/large-screen-app-quality>
- Screen-size support overview: <https://developer.android.com/guide/topics/large-screens/support-different-screen-sizes>
- Screen compatibility overview: <https://developer.android.com/guide/practices/screens_support>
- Android ABIs: <https://developer.android.com/ndk/guides/abis>
- Android App Bundle: <https://developer.android.com/guide/app-bundle>

Important implications:

- phone-only assumptions are not acceptable for tablets/foldables
- resizable, adaptive layouts matter more than fixed device classes
- keyboard, mouse, stylus, and multi-window behavior are part of quality
- packaging and native-code delivery are tied to Android ABI handling and AAB publishing

### iOS and iPadOS

Apple guidance is strongly scene-, layout-, and window-aware:

- HIG Layout: <https://developer.apple.com/design/human-interface-guidelines/layout>
- Designing for iPadOS: <https://developer.apple.com/design/human-interface-guidelines/designing-for-ipados>
- UIKit scenes: <https://developer.apple.com/documentation/uikit/specifying-the-scenes-your-app-supports>
- UIKit lifecycle: <https://developer.apple.com/documentation/UIKit/managing-your-app-s-life-cycle>
- SwiftUI `ScenePhase`: <https://developer.apple.com/documentation/swiftui/scenephase>
- Register an App ID: <https://developer.apple.com/help/account/identifiers/register-an-app-id>

Important implications:

- iPad is not just “big iPhone”
- window resizing, multitasking, and scene lifecycle are first-class
- native accessibility and platform conventions matter heavily
- signing, bundle ID, capabilities, and store workflow are unavoidable platform constraints

## GUI Strategy Options

### Option Table

| Option | GUI model | How generated language fits | Phone + tablet fit | Best fit | Main pitfalls |
|---|---|---|---|---|---|
| Native-first: Compose + SwiftUI | Two native declarative UIs over shared core/runtime | Generate bindings, shared models, exported C ABI, or platform-neutral state machines | Strongest for Android phones/tablets and iPhone/iPad | Best overall quality and store fit | Two UI codebases, duplicated feature work, visual parity discipline needed |
| Shared logic + native UI | Shared app logic, native UI per platform | Language focuses on business logic, domain model, networking, persistence, reducers, effects | Very strong | Best fit when the language/runtime is the product | Still two UI codebases; mobile shell integration still required |
| Flutter | One shared widget/runtime stack | Language either embeds Flutter module or generates Dart/intermediate bindings | Good if deliberately adapted for large screens | Best when one shared UI codebase is mandatory | Platform fidelity drift, plugin dependence, engine/binary/startup costs |
| React Native | Shared React UI with native modules when needed | Language likely sits behind JS bridge, native module, or generated TS/JS layer | Acceptable, but tablet polish requires explicit work | Best only with a strong React/JS ecosystem reason | Bridge complexity, perf-sensitive screens, native divergence, dependency churn |
| Repo-owned cross-platform renderer | Custom renderer/runtime owned by Simple | Language owns widget tree, rendering, lifecycle abstraction, and packaging seams | Potentially strong in theory | Best only if cross-platform UI ownership is a strategic product goal | Highest cost and risk; hardest to match platform fit, accessibility, input, and store expectations |

## “How GUI” by Approach

| Approach | GUI implementation model | What Simple should generate or own |
|---|---|---|
| Native-first | Compose on Android, SwiftUI on iOS/iPadOS | Shared state model, navigation model, command/effect layer, native bindings |
| Shared logic + native UI | Same as native-first, but stronger emphasis on shared app core | Domain logic, persistence layer, networking, reducers, validation, serialization |
| Flutter | Flutter renders most UI; host app embeds engine/module | Embed Flutter module or generate bridge layer into Dart/platform channels |
| React Native | React tree renders UI via RN runtime and native components | Generate JS/TS bindings or use native module bridge |
| Repo-owned renderer | Simple owns widget tree and backend renderer | Entire rendering/input/lifecycle abstraction, plus mobile backend glue |

## Generated-Language Fit

### Best Near-Term Fit

The generated language should primarily own:

- shared domain model
- app state and reducers
- async side-effect orchestration
- validation/business rules
- serialization/networking/storage logic
- exported C ABI or host-call boundary

The generated language should not own, at first:

- full native UI generation for both Compose and SwiftUI
- direct store signing/publishing logic
- a universal abstraction that hides all lifecycle differences

### Why

Android and Apple have converged on declarative UI, but not on the same UI framework, lifecycle hooks, input models, or packaging rules. A shared logic layer survives that difference cleanly. A forced shared UI abstraction does not.

## Phone and Tablet Considerations

### Android Phones and Tablets

Platform guidance expects:

- adaptive layouts rather than hardcoded phone/tablet branches
- large-screen navigation changes such as bottom bar to rail/panel
- support for resizing, split screen, desktop windowing, stylus, keyboard, and mouse

Implication for Simple:

- UI descriptions must be size- and capability-aware
- layout breakpoints should be based on window metrics, not device names

### iPhone and iPad

Platform guidance expects:

- scene-aware lifecycle
- iPad multitasking and resizable windows
- layouts that hold up under compact and regular width/height combinations
- keyboard, pointer, touch, and Pencil-friendly behavior where relevant

Implication for Simple:

- iPad must be treated as its own UX quality target
- a generated or shared layout system must preserve native window and scene semantics

## Toolchain and Runtime Realities

| Area | Android reality | Apple reality | Implication for Simple |
|---|---|---|---|
| Native code | NDK ABI matrix matters | Apple-native toolchain and bundle/signing rules matter | Native library output is feasible, but packaging is platform-owned |
| Cross compilation | LLVM/Clang cross compilation is normal | iOS build/distribution still depends on Apple toolchain workflow | Compiler output alone is not enough for a productized lane |
| Packaging | AAB and ABI delivery rules matter | App ID, signing, capabilities, and Xcode flow matter | Mobile support is not just codegen; it is release pipeline work |
| Lifecycle | Activity/process/window driven | Scene/app/window driven | Do not hide lifecycle differences behind a thin fake abstraction |

Reference:

- Clang cross-compilation: <https://clang.llvm.org/docs/CrossCompilation.html>

### Practical Toolchain Recommendation

The best first shipping shape is:

- LLVM-native code generation for the shared language core/runtime
- stable C ABI at the embedding boundary
- Android host app packages native libraries through the NDK/Gradle/AAB path
- iOS host app packages native output as a framework or XCFramework through Xcode

This avoids overloading the compiler with store packaging and native UI generation before the host boundary is stable.

## FFI Boundary Recommendation

| Platform | Recommended boundary | Why |
|---|---|---|
| Android | C ABI plus coarse JNI/Kotlin bridge | JNI is viable, but a coarse boundary reduces crossing overhead and ownership bugs |
| iOS/iPadOS | C ABI plus Objective-C/Swift wrapper | C and Objective-C interop is the safest first bridge; targeting raw Swift ABI first is the wrong optimization |

Implication for Simple:

- generate stable shared-library exports first
- keep ownership, string, collection, and async boundaries explicit
- treat direct Swift ABI generation as out of scope for the first mobile lane

## Recommendation

### Recommended Strategy

1. Use Simple as a shared runtime/core language for app logic.
2. Keep mobile GUI native-first:
   Android: Jetpack Compose.
   iOS/iPadOS: SwiftUI.
3. Bridge through exported C ABI, generated bindings, or a host SDK layer.
4. Reuse the repo’s existing shared UI/session abstractions where they help state, actions, and rendering-neutral intent.
5. Treat full first-class Android/iOS support as a later phase after native-shell integration works.

### Why This Fits This Repo

This repo already has:

- a typed shared UI/session model
- explicit backend seams
- SFFI/export infrastructure
- some mobile-facing Tauri experimentation

It does not yet have:

- first-class Android/iOS host backend kinds
- a proven mobile compositor/input backend
- a finished mobile packaging/signing/test lane in the main toolchain

That makes shared-core plus native shells the highest-value, lowest-regret path.

## Phased Plan

| Phase | Scope | Outcome |
|---|---|---|
| 1 | Shared core only | Mobile host apps call Simple-produced libraries for logic |
| 2 | Native UI integration | Compose and SwiftUI shells bind to Simple state/actions |
| 3 | Packaging lane | Android `arm64-v8a` first, plus `x86_64` emulator/dev; iOS device and simulator slices packaged as a framework/XCFramework |
| 4 | Tablet-quality adaptation | Large-screen navigation, multitasking, keyboard/mouse/stylus polish |
| 5 | Build/test lane | Android/iOS CI, packaging, signing, device/emulator validation |
| 6 | Optional shared UI experiments | Evaluate whether a repo-owned or partially shared UI layer is still worth it |

## Pitfalls

| Pitfall | Why it fails |
|---|---|
| Building a single fake cross-platform mobile UI first | It front-loads the hardest unsolved part and fights both platform guidance and current repo maturity |
| Treating tablets as scaled phones | Both Android and iPadOS expect adaptive or window-aware behavior |
| Solving codegen before host integration | The actual blocker is lifecycle, input, rendering, and packaging integration |
| Making Tauri/mobile shell the long-term architecture by default | It is useful for prototyping, but it does not align cleanly with the repo’s shared-WM direction yet |
| Hiding lifecycle differences behind one shallow abstraction | Android activities/windows and Apple scenes/windows are similar in spirit, not identical in contract |

## Source List

- Android Developers, adaptive layouts: <https://developer.android.com/develop/ui/compose/layouts/adaptive>
- Android Developers, large-screen quality: <https://developer.android.com/docs/quality-guidelines/archive/adaptive/large-screen-app-quality>
- Android Developers, screen-size support: <https://developer.android.com/guide/topics/large-screens/support-different-screen-sizes>
- Android Developers, screen compatibility: <https://developer.android.com/guide/practices/screens_support>
- Android NDK ABIs: <https://developer.android.com/ndk/guides/abis>
- Android App Bundle: <https://developer.android.com/guide/app-bundle>
- Apple HIG Layout: <https://developer.apple.com/design/human-interface-guidelines/layout>
- Apple HIG iPadOS: <https://developer.apple.com/design/human-interface-guidelines/designing-for-ipados>
- Apple UIKit scenes: <https://developer.apple.com/documentation/uikit/specifying-the-scenes-your-app-supports>
- Apple UIKit lifecycle: <https://developer.apple.com/documentation/UIKit/managing-your-app-s-life-cycle>
- Apple SwiftUI scene phase: <https://developer.apple.com/documentation/swiftui/scenephase>
- Apple App ID registration: <https://developer.apple.com/help/account/identifiers/register-an-app-id>
- Apple static frameworks: <https://developer.apple.com/documentation/xcode/creating-a-static-framework>
- JetBrains Kotlin Multiplatform, share code: <https://www.jetbrains.com/help/kotlin-multiplatform-dev/multiplatform-share-on-platforms.html>
- JetBrains Compose Multiplatform overview: <https://www.jetbrains.com/help/kotlin-multiplatform-dev/compose-multiplatform-and-jetpack-compose.html>
- Flutter adaptive/responsive design: <https://docs.flutter.dev/ui/adaptive-responsive>
- Flutter add-to-app: <https://docs.flutter.dev/add-to-app>
- React Native architecture overview: <https://reactnative.dev/architecture/overview>
- Android NDK other build systems: <https://developer.android.com/ndk/guides/other_build_systems>
- Android JNI tips: <https://developer.android.com/ndk/guides/jni-tips>
- Clang cross compilation: <https://clang.llvm.org/docs/CrossCompilation.html>
