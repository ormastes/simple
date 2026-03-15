// SimpleApp.swift — iOS bridge for Simple applications
//
// Minimal Swift wrapper that sets up UIApplication and calls into
// Simple's app_main() via C interop.
//
// Usage:
//   1. Compile Simple app to static library (.a) with ios-arm64 preset
//   2. Link this Swift file with the Simple static library
//   3. Set this as the app entry point in Xcode project
//
// The Simple runtime exports:
//   int32_t simple_app_main(int32_t argc, const char** argv);

import UIKit

// C function exported by the Simple runtime/app
@_silgen_name("simple_app_main")
func simple_app_main(_ argc: Int32, _ argv: UnsafeMutablePointer<UnsafeMutablePointer<CChar>?>?) -> Int32

@main
class SimpleAppDelegate: UIResponder, UIApplicationDelegate {
    var window: UIWindow?
    private var appExitCode: Int32 = 0

    func application(
        _ application: UIApplication,
        didFinishLaunchingWithOptions launchOptions: [UIApplication.LaunchOptionsKey: Any]?
    ) -> Bool {
        // Convert launch arguments to C-style argc/argv
        let args = ProcessInfo.processInfo.arguments
        let argc = Int32(args.count)

        // Create C string array
        var cStrings = args.map { strdup($0) }
        cStrings.withUnsafeMutableBufferPointer { buffer in
            appExitCode = simple_app_main(argc, buffer.baseAddress)
        }

        // Clean up C strings
        for ptr in cStrings {
            free(ptr)
        }

        return true
    }

    func applicationWillTerminate(_ application: UIApplication) {
        // Simple app shutdown is handled by the runtime's
        // __simple_runtime_shutdown() call in app_main
    }

    func applicationDidEnterBackground(_ application: UIApplication) {
        // Apps can handle this via the update() loop checking state
    }

    func applicationWillEnterForeground(_ application: UIApplication) {
        // Apps can handle this via the update() loop checking state
    }
}
