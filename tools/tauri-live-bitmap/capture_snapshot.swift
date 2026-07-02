// Offscreen WKWebView pixel snapshot capture for macOS renderer evidence.
//
// Usage:
//   WEBKIT_CAPTURE_HTML=fixture.html \
//   WEBKIT_CAPTURE_WIDTH=96 WEBKIT_CAPTURE_HEIGHT=64 \
//   WEBKIT_CAPTURE_RAW_RGBA=out.rgba \
//   WEBKIT_CAPTURE_FRAME_US=frame-us.txt \
//   swift tools/tauri-live-bitmap/capture_snapshot.swift

import Cocoa
import WebKit

let env = ProcessInfo.processInfo.environment
let htmlPath = env["WEBKIT_CAPTURE_HTML"] ?? ""
let width = Int(env["WEBKIT_CAPTURE_WIDTH"] ?? "96") ?? 96
let height = Int(env["WEBKIT_CAPTURE_HEIGHT"] ?? "64") ?? 64
let rawOutputPath = env["WEBKIT_CAPTURE_RAW_RGBA"] ?? "webkit-snapshot.rgba"
let frameUsPath = env["WEBKIT_CAPTURE_FRAME_US"] ?? ""
let settleMs = Int(env["WEBKIT_CAPTURE_SETTLE_MS"] ?? "600") ?? 600

func fail(_ msg: String) -> Never {
    FileHandle.standardError.write(("error=\(msg)\n").data(using: .utf8)!)
    exit(1)
}

guard width > 0, height > 0 else {
    fail("invalid-dimensions")
}

guard !htmlPath.isEmpty, let html = try? String(contentsOfFile: htmlPath, encoding: .utf8) else {
    fail("cannot-read-html")
}

let baseURL = URL(fileURLWithPath: htmlPath).deletingLastPathComponent()
let app = NSApplication.shared
app.setActivationPolicy(.prohibited)

final class SnapshotCapturer: NSObject, WKNavigationDelegate {
    let webView: WKWebView
    let html: String
    let baseURL: URL
    let width: Int
    let height: Int
    let settleMs: Int
    let rawOutputPath: String
    let frameUsPath: String

    init(html: String, baseURL: URL, width: Int, height: Int, settleMs: Int,
         rawOutputPath: String, frameUsPath: String) {
        self.html = html
        self.baseURL = baseURL
        self.width = width
        self.height = height
        self.settleMs = settleMs
        self.rawOutputPath = rawOutputPath
        self.frameUsPath = frameUsPath

        let cfg = WKWebViewConfiguration()
        cfg.suppressesIncrementalRendering = true
        self.webView = WKWebView(
            frame: NSRect(x: 0, y: 0, width: width, height: height),
            configuration: cfg
        )
        super.init()
        self.webView.navigationDelegate = self
        self.webView.setValue(false, forKey: "drawsBackground")
    }

    func start() {
        webView.loadHTMLString(html, baseURL: baseURL)
    }

    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        DispatchQueue.main.asyncAfter(deadline: .now() + .milliseconds(settleMs)) {
            self.snapshot()
        }
    }

    func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
        fail("navigation-failed:\(error.localizedDescription)")
    }

    func snapshot() {
        let config = WKSnapshotConfiguration()
        config.rect = NSRect(x: 0, y: 0, width: width, height: height)

        let start = DispatchTime.now().uptimeNanoseconds
        webView.takeSnapshot(with: config) { image, error in
            let end = DispatchTime.now().uptimeNanoseconds
            if let error = error {
                fail("snapshot-failed:\(error.localizedDescription)")
            }
            guard let image = image else {
                fail("snapshot-missing-image")
            }
            guard let cgImage = image.cgImage(forProposedRect: nil, context: nil, hints: nil) else {
                fail("snapshot-missing-cgimage")
            }

            let bytesPerPixel = 4
            let bytesPerRow = self.width * bytesPerPixel
            var rgba = [UInt8](repeating: 0, count: self.height * bytesPerRow)
            guard let colorSpace = CGColorSpace(name: CGColorSpace.sRGB) else {
                fail("missing-srgb-color-space")
            }
            guard let ctx = CGContext(
                data: &rgba,
                width: self.width,
                height: self.height,
                bitsPerComponent: 8,
                bytesPerRow: bytesPerRow,
                space: colorSpace,
                bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
            ) else {
                fail("snapshot-context-failed")
            }
            ctx.interpolationQuality = .none
            ctx.draw(cgImage, in: CGRect(x: 0, y: 0, width: self.width, height: self.height))

            let data = Data(rgba)
            do {
                try data.write(to: URL(fileURLWithPath: self.rawOutputPath))
                if !self.frameUsPath.isEmpty {
                    let frameUs = max(1, Int((end - start) / 1000))
                    try "\(frameUs)\n".write(toFile: self.frameUsPath, atomically: true, encoding: .utf8)
                }
            } catch {
                fail("snapshot-write-failed:\(error.localizedDescription)")
            }
            print("webkit_snapshot_raw_rgba=\(self.rawOutputPath)")
            print("webkit_snapshot_width=\(self.width)")
            print("webkit_snapshot_height=\(self.height)")
            exit(0)
        }
    }
}

let capturer = SnapshotCapturer(
    html: html,
    baseURL: baseURL,
    width: width,
    height: height,
    settleMs: settleMs,
    rawOutputPath: rawOutputPath,
    frameUsPath: frameUsPath
)
capturer.start()

DispatchQueue.main.asyncAfter(deadline: .now() + 20) {
    fail("timeout")
}
app.run()
