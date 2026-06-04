#!/usr/bin/env python3
"""Capture HTML rendering via WebKitGTK (Tauri-equivalent on Linux).
Outputs ARGB JSON in the same format as capture_html_argb.js (Electron).

Env vars:
  WEBKIT_CAPTURE_HTML    - HTML string to render
  WEBKIT_CAPTURE_WIDTH   - viewport width (default 320)
  WEBKIT_CAPTURE_HEIGHT  - viewport height (default 240)
  WEBKIT_CAPTURE_OUTPUT  - output JSON path
  WEBKIT_CAPTURE_SETTLE_MS - settle time in ms (default 1000)
"""
import os, sys, json, ctypes

import gi
gi.require_version('Gtk', '3.0')
gi.require_version('WebKit2', '4.1')
from gi.repository import Gtk, WebKit2, GLib
import cairo

html = os.environ.get('WEBKIT_CAPTURE_HTML', '<p>Hello</p>')
width = int(os.environ.get('WEBKIT_CAPTURE_WIDTH', '320'))
height = int(os.environ.get('WEBKIT_CAPTURE_HEIGHT', '240'))
output_path = os.environ.get('WEBKIT_CAPTURE_OUTPUT', '')
settle_ms = int(os.environ.get('WEBKIT_CAPTURE_SETTLE_MS', '1000'))

win = Gtk.Window()
win.set_default_size(width, height)
win.set_decorated(False)

webview = WebKit2.WebView()
webview.set_size_request(width, height)
settings = webview.get_settings()
settings.set_enable_javascript(True)
settings.set_hardware_acceleration_policy(WebKit2.HardwareAccelerationPolicy.NEVER)
win.add(webview)
win.show_all()

def on_snapshot_ready(wv, result):
    try:
        surface = wv.get_snapshot_finish(result)
        sw = surface.get_width()
        sh = surface.get_height()

        buf = surface.get_data()
        stride = surface.get_stride()
        pixels = []
        for y in range(min(sh, height)):
            for x in range(min(sw, width)):
                off = y * stride + x * 4
                b = buf[off]
                g = buf[off + 1]
                r = buf[off + 2]
                a = buf[off + 3]
                pixels.append((a << 24) | (r << 16) | (g << 8) | b)

        pad_count = width * height - len(pixels)
        if pad_count > 0:
            pixels.extend([0xFFFFFFFF] * pad_count)

        result_data = {"width": width, "height": height, "pixels": pixels}
        if output_path:
            with open(output_path, 'w') as f:
                json.dump(result_data, f)
            print(f"wrote {output_path}")
        else:
            print(f"pixels={len(pixels)}")
    except Exception as e:
        print(f"snapshot error: {e}", file=sys.stderr)
    Gtk.main_quit()

def do_snapshot():
    webview.get_snapshot(
        WebKit2.SnapshotRegion.FULL_DOCUMENT,
        WebKit2.SnapshotOptions.NONE,
        None,
        on_snapshot_ready
    )
    return False

def on_load_changed(wv, event):
    if event == WebKit2.LoadEvent.FINISHED:
        GLib.timeout_add(settle_ms, do_snapshot)

GLib.timeout_add(settle_ms + 5000, lambda: (Gtk.main_quit(), False)[1])

webview.connect('load-changed', on_load_changed)
webview.load_html(html, 'file:///')

Gtk.main()
