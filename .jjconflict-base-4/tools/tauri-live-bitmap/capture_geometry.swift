// Offscreen WKWebView geometry capture — renders HTML through macOS WebKit
// (the same engine Tauri uses on macOS) and emits per-selector computed
// geometry as JSON, mirroring tools/electron-live-bitmap audit output so the
// two engines can be compared directly.
//
// Usage:
//   WEBKIT_CAPTURE_HTML=fixture.html \
//   WEBKIT_CAPTURE_WIDTH=600 WEBKIT_CAPTURE_HEIGHT=120 \
//   WEBKIT_CAPTURE_SELECTORS=".simple-app-title,.simple-titlebar-widget" \
//   WEBKIT_CAPTURE_OUTPUT=out.json \
//   swift capture_geometry.swift

import Cocoa
import WebKit

let env = ProcessInfo.processInfo.environment
let htmlPath = env["WEBKIT_CAPTURE_HTML"] ?? ""
let width = Double(env["WEBKIT_CAPTURE_WIDTH"] ?? "600") ?? 600
let height = Double(env["WEBKIT_CAPTURE_HEIGHT"] ?? "120") ?? 120
let selectors = (env["WEBKIT_CAPTURE_SELECTORS"] ?? "")
    .split(separator: ",").map { $0.trimmingCharacters(in: .whitespaces) }.filter { !$0.isEmpty }
let outputPath = env["WEBKIT_CAPTURE_OUTPUT"] ?? "webkit_geometry.json"
let settleMs = Int(env["WEBKIT_CAPTURE_SETTLE_MS"] ?? "600") ?? 600

func fail(_ msg: String) -> Never {
    FileHandle.standardError.write(("error=" + msg + "\n").data(using: .utf8)!)
    exit(1)
}

guard !htmlPath.isEmpty, let html = try? String(contentsOfFile: htmlPath, encoding: .utf8) else {
    fail("cannot read WEBKIT_CAPTURE_HTML=\(htmlPath)")
}

// JSON-encode the selector list for injection into the page script.
let selectorsJSON: String = {
    let data = try! JSONSerialization.data(withJSONObject: selectors, options: [])
    return String(data: data, encoding: .utf8)!
}()

let app = NSApplication.shared
app.setActivationPolicy(.prohibited)

final class Capturer: NSObject, WKNavigationDelegate {
    let webView: WKWebView
    let html: String
    let selectorsJSON: String
    let vpWidth: Int
    let vpHeight: Int
    let settleMs: Int
    let outputPath: String
    let selectorCount: Int

    init(html: String, selectorsJSON: String, width: Double, height: Double,
         settleMs: Int, outputPath: String, selectorCount: Int) {
        self.html = html
        self.selectorsJSON = selectorsJSON
        self.vpWidth = Int(width)
        self.vpHeight = Int(height)
        self.settleMs = settleMs
        self.outputPath = outputPath
        self.selectorCount = selectorCount
        let cfg = WKWebViewConfiguration()
        webView = WKWebView(frame: NSRect(x: 0, y: 0, width: width, height: height), configuration: cfg)
        super.init()
        webView.navigationDelegate = self
    }

    func start() {
        webView.loadHTMLString(html, baseURL: nil)
    }

    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        DispatchQueue.main.asyncAfter(deadline: .now() + .milliseconds(settleMs)) {
            self.extract()
        }
    }

    func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
        fail("navigation failed: \(error.localizedDescription)")
    }

    func extract() {
        let js = """
        (function() {
          var selectors = \(selectorsJSON);
          function styleNum(cs, p){ return cs.getPropertyValue(p); }
          var items = [];
          selectors.forEach(function(sel){
            var nodes = Array.prototype.slice.call(document.querySelectorAll(sel));
            nodes.forEach(function(el, index){
              var r = el.getBoundingClientRect();
              var cs = getComputedStyle(el);
              items.push({
                selector: sel, index: index, tag: el.tagName.toLowerCase(),
                rect: { left: Math.round(r.left), top: Math.round(r.top),
                        width: Math.round(r.width), height: Math.round(r.height) },
                display: cs.display, position: cs.position,
                boxSizing: cs.boxSizing, borderTopWidth: cs.borderTopWidth,
                paddingTop: cs.paddingTop, paddingLeft: cs.paddingLeft,
                fontFamily: cs.fontFamily, fontSize: cs.fontSize,
                lineHeight: cs.lineHeight, appearance: cs.appearance || cs.webkitAppearance,
                color: cs.color, background: cs.backgroundColor,
                userSelect: cs.userSelect || cs.webkitUserSelect, cursor: cs.cursor
              });
            });
          });
          return JSON.stringify({ producer: "webkit-wkwebview-geometry",
            viewport: { width: \(vpWidth), height: \(vpHeight) }, items: items });
        })();
        """
        webView.evaluateJavaScript(js) { result, error in
            if let error = error { fail("js error: \(error.localizedDescription)") }
            guard let json = result as? String else { fail("no json result") }
            try? json.write(toFile: self.outputPath, atomically: true, encoding: .utf8)
            print("webkit_geometry=\(self.outputPath)")
            print("webkit_items=\(self.selectorCount)")
            exit(0)
        }
    }
}

let cap = Capturer(html: html, selectorsJSON: selectorsJSON, width: width, height: height,
                   settleMs: settleMs, outputPath: outputPath, selectorCount: selectors.count)
cap.start()

// Safety timeout so the run loop never hangs forever.
DispatchQueue.main.asyncAfter(deadline: .now() + 20) { fail("timeout") }
app.run()
