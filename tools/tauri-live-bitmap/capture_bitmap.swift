// Offscreen WKWebView bitmap capture. This exercises macOS WebKit, the engine
// Tauri uses on macOS, and writes raw RGBA pixels for the existing ARGB proof
// and checksum pipeline.
//
// Usage:
//   WEBKIT_CAPTURE_HTML=fixture.html \
//   WEBKIT_CAPTURE_WIDTH=96 WEBKIT_CAPTURE_HEIGHT=64 \
//   WEBKIT_CAPTURE_RAW_RGBA=out.rgba \
//   swift capture_bitmap.swift

import Cocoa
import WebKit

let env = ProcessInfo.processInfo.environment
let htmlPath = env["WEBKIT_CAPTURE_HTML"] ?? ""
let width = Int(env["WEBKIT_CAPTURE_WIDTH"] ?? "96") ?? 96
let height = Int(env["WEBKIT_CAPTURE_HEIGHT"] ?? "64") ?? 64
let rawPath = env["WEBKIT_CAPTURE_RAW_RGBA"] ?? "webkit-window.rgba"
let settleMs = Int(env["WEBKIT_CAPTURE_SETTLE_MS"] ?? "600") ?? 600

func fail(_ msg: String) -> Never {
    FileHandle.standardError.write(("error=" + msg + "\n").data(using: .utf8)!)
    exit(1)
}

guard width > 0, height > 0 else {
    fail("invalid dimensions")
}

guard !htmlPath.isEmpty, let html = try? String(contentsOfFile: htmlPath, encoding: .utf8) else {
    fail("cannot read WEBKIT_CAPTURE_HTML=\(htmlPath)")
}

let app = NSApplication.shared
app.setActivationPolicy(.prohibited)

final class BitmapCapturer: NSObject, WKNavigationDelegate {
    let webView: WKWebView
    let html: String
    let width: Int
    let height: Int
    let settleMs: Int
    let rawPath: String

    init(html: String, width: Int, height: Int, settleMs: Int, rawPath: String) {
        self.html = html
        self.width = width
        self.height = height
        self.settleMs = settleMs
        self.rawPath = rawPath
        let cfg = WKWebViewConfiguration()
        cfg.suppressesIncrementalRendering = true
        self.webView = WKWebView(frame: NSRect(x: 0, y: 0, width: width, height: height), configuration: cfg)
        super.init()
        self.webView.navigationDelegate = self
    }

    func start() {
        webView.loadHTMLString(html, baseURL: URL(fileURLWithPath: htmlPath).deletingLastPathComponent())
    }

    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        DispatchQueue.main.asyncAfter(deadline: .now() + .milliseconds(settleMs)) {
            self.capture()
        }
    }

    func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
        fail("navigation failed: \(error.localizedDescription)")
    }

    func capture() {
        let config = WKSnapshotConfiguration()
        config.rect = CGRect(x: 0, y: 0, width: width, height: height)
        config.afterScreenUpdates = true
        webView.takeSnapshot(with: config) { image, error in
            if let error = error {
                fail("snapshot failed: \(error.localizedDescription)")
            }
            guard let image = image, let cg = image.cgImage(forProposedRect: nil, context: nil, hints: nil) else {
                fail("snapshot image missing")
            }
            var bytes = [UInt8](repeating: 0, count: self.width * self.height * 4)
            guard let ctx = CGContext(
                data: &bytes,
                width: self.width,
                height: self.height,
                bitsPerComponent: 8,
                bytesPerRow: self.width * 4,
                space: CGColorSpaceCreateDeviceRGB(),
                bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
            ) else {
                fail("bitmap context failed")
            }
            ctx.interpolationQuality = .none
            ctx.draw(cg, in: CGRect(x: 0, y: 0, width: self.width, height: self.height))
            do {
                try Data(bytes).write(to: URL(fileURLWithPath: self.rawPath))
            } catch {
                fail("write failed: \(error.localizedDescription)")
            }
            print("webkit_bitmap=\(self.rawPath)")
            print("webkit_width=\(self.width)")
            print("webkit_height=\(self.height)")
            exit(0)
        }
    }
}

let capturer = BitmapCapturer(html: html, width: width, height: height, settleMs: settleMs, rawPath: rawPath)
capturer.start()

DispatchQueue.main.asyncAfter(deadline: .now() + 20) { fail("timeout") }
app.run()
