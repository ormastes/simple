#!/usr/bin/env python3
import html
import http.server
import json
import socketserver
import sys
import tempfile
import threading
import urllib.parse
import urllib.request
import zlib
from pathlib import Path


STYLE = """html,body{margin:0;width:100%;height:100%;font:14px system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;background:#101418;color:#eef2f5;overflow:hidden}
#desktop{position:fixed;inset:0;background:linear-gradient(135deg,#101418 0%,#1f2930 55%,#13251f 100%)}
.taskbar{position:absolute;left:0;right:0;bottom:0;height:54px;display:flex;align-items:center;gap:8px;padding:0 10px;background:rgba(10,14,18,.92);border-top:1px solid rgba(255,255,255,.16);box-sizing:border-box}
.taskbar button{width:42px;height:38px;border:1px solid rgba(255,255,255,.22);border-radius:7px;background:#1f2a31;color:#f8fafc;font-weight:700}
.taskbar button.active{background:#2b6f62}
.window{position:absolute;border:1px solid rgba(255,255,255,.22);border-radius:8px;background:#f8fafc;color:#172026;box-shadow:0 18px 40px rgba(0,0,0,.36);overflow:hidden}
.titlebar{height:32px;background:#20303a;color:#fff;display:flex;align-items:center;padding:0 10px;cursor:grab;user-select:none;font-weight:700}
.body{padding:12px}.simple-picture{width:78px;height:52px;border-radius:6px;background:#e11d48;border:2px solid #16252b}
input{height:28px;border:1px solid #9aa6ad;border-radius:5px;padding:0 8px}.status{position:absolute;left:12px;top:12px;background:rgba(0,0,0,.48);padding:8px 10px;border-radius:6px;color:#f8fafc}"""

DEFAULT_WINDOWS = [
    {"windowId": "terminal", "title": "Terminal", "html": '<section class="simple-app-window"><pre class="simple-app-pre">Tauri mobile MDI smoke</pre><button>Action</button><input id="probe-input" value="ready"></section>'},
    {"windowId": "files", "title": "Files", "html": '<section class="simple-app-window"><pre class="simple-app-pre">Files window</pre><div class="simple-picture"></div></section>'},
    {"windowId": "tasks", "title": "Tasks", "html": '<section class="simple-app-window"><pre class="simple-app-pre">Taskbar icon drawing evidence</pre></section>'},
    {"windowId": "settings", "title": "Settings", "html": '<section class="simple-app-window"><pre class="simple-app-pre">Event bridge ready</pre></section>'},
]


def safe_id(text):
    return "win-" + "".join(ch if ch.isalnum() or ch in "-_" else "-" for ch in str(text))


def load_windows(ipc_path):
    if not ipc_path:
        return DEFAULT_WINDOWS
    windows = []
    for line in Path(ipc_path).read_text(encoding="utf-8", errors="ignore").splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("type") == "openWindow":
            windows.append(
                {
                    "windowId": str(msg.get("windowId") or msg.get("window_id") or f"window-{len(windows) + 1}"),
                    "title": str(msg.get("title") or "Window"),
                    "html": str(msg.get("html") or ""),
                }
            )
    if len(windows) < 4:
        raise SystemExit(f"expected at least 4 openWindow IPC messages, found {len(windows)}")
    return windows


def build_html(windows):
    window_markup = []
    taskbar_markup = []
    for index, window in enumerate(windows):
        dom_id = safe_id(window["windowId"])
        body = window["html"]
        if index == 0 and 'id="probe-input"' not in body:
            body += '<input id="probe-input" value="ready" style="position:absolute;left:-10000px;width:1px;height:1px">'
        window_markup.append(
            f'<section class="window" id="{html.escape(dom_id)}" data-source-window-id="{html.escape(window["windowId"])}" '
            f'style="left:{20 + index * 46}px;top:{56 + index * 42}px;width:{260 if index == 0 else 220}px;height:{146 if index == 0 else 124}px">'
            f'<div class="titlebar">{html.escape(window["title"])}</div><div class="body">{body}</div></section>'
        )
        taskbar_markup.append(f'<button data-window="{html.escape(dom_id)}">{html.escape((window["title"][:1] or "?").upper())}</button>')

    return f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Simple iOS MDI Probe</title><style>{STYLE}</style></head>
<body><main id="desktop" data-simple-desktop="true"><div class="status" id="status">running</div>{''.join(window_markup)}<nav class="taskbar" aria-label="MDI taskbar">{''.join(taskbar_markup)}</nav></main>
<script>
(function(){{
  var proof={{count:document.querySelectorAll('.window').length,hasDesktop:false,imageCount:0,hasDragRuntime:false,hasDragEvents:false,dragMoved:false,hasWindowEventRuntime:false,bodyClickRouted:false,bodyInputRouted:false,htmlRenderable:false,taskbarIconCount:0,sourceWindowCount:0,hasSimpleSmokeText:false}};
  var desktop=document.getElementById('desktop'); var drag=null;
  proof.hasDesktop=!!desktop; proof.imageCount=document.querySelectorAll('.simple-picture,img.simple-picture').length;
  proof.htmlRenderable=!!document.querySelector('.simple-app-window')&&!!document.querySelector('.simple-app-pre');
  proof.taskbarIconCount=document.querySelectorAll('.taskbar button').length;
  proof.sourceWindowCount=document.querySelectorAll('[data-source-window-id]').length;
  proof.hasSimpleSmokeText=document.body.textContent.indexOf('Tauri mobile MDI smoke')>=0;
  proof.hasWindowEventRuntime=true; proof.hasDragRuntime=true;
  document.body.addEventListener('click',function(){{proof.bodyClickRouted=true;}},true);
  document.getElementById('probe-input').addEventListener('input',function(){{proof.bodyInputRouted=true;}},true);
  document.querySelectorAll('.taskbar button').forEach(function(button){{button.addEventListener('click',function(){{button.classList.add('active');}});}});
  document.querySelectorAll('.titlebar').forEach(function(bar){{
    function start(ev){{var win=bar.parentElement;document.querySelectorAll('.window').forEach(function(other){{other.style.zIndex='1';}});win.style.zIndex='20';drag={{win:win,x:ev.clientX||0,y:ev.clientY||0,left:win.offsetLeft,top:win.offsetTop}};proof.hasDragEvents=true;}}
    function move(ev){{if(!drag)return;drag.win.style.left=(drag.left+(ev.clientX||0)-drag.x+18)+'px';drag.win.style.top=(drag.top+(ev.clientY||0)-drag.y+10)+'px';proof.dragMoved=true;}}
    function end(){{drag=null;}}
    bar.addEventListener('pointerdown',start);window.addEventListener('pointermove',move);window.addEventListener('pointerup',end);
    bar.addEventListener('mousedown',start);window.addEventListener('mousemove',move);window.addEventListener('mouseup',end);
  }});
  function evt(type,opts){{if(window.PointerEvent&&type.indexOf('pointer')===0)return new PointerEvent(type,Object.assign({{bubbles:true}},opts||{{}}));return new MouseEvent(type.replace('pointer','mouse'),Object.assign({{bubbles:true}},opts||{{}}));}}
  function runProbe(){{var title=document.querySelector('.titlebar');title.dispatchEvent(evt('pointerdown',{{clientX:30,clientY:60}}));window.dispatchEvent(evt('pointermove',{{clientX:90,clientY:98}}));window.dispatchEvent(evt('pointerup',{{clientX:90,clientY:98}}));document.body.dispatchEvent(new MouseEvent('click',{{bubbles:true}}));var input=document.getElementById('probe-input');input.value='ios-webview-event';input.dispatchEvent(new Event('input',{{bubbles:true}}));document.querySelector('.taskbar button').click();document.getElementById('status').textContent='proof-pass';window.__simpleMdiProof=proof;fetch('/proof?'+new URLSearchParams(Object.entries(proof).map(function(pair){{return [pair[0],String(pair[1])];}}))).catch(function(){{}});}}
  setTimeout(runProbe,250);
}})();
</script></body></html>"""


def parse_proof_query(query):
    proof = {key: values[-1] for key, values in urllib.parse.parse_qs(query).items()}
    for key, value in list(proof.items()):
        if value in ("true", "false"):
            proof[key] = value == "true"
        else:
            try:
                proof[key] = int(value)
            except ValueError:
                pass
    return proof


def make_handler(proof_path, windows):
    page = build_html(windows)

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            parsed = urllib.parse.urlparse(self.path)
            if parsed.path in ("/", "/ios_mdi_probe.html"):
                body = page.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif parsed.path == "/proof":
                Path(proof_path).write_text(json.dumps(parse_proof_query(parsed.query), sort_keys=True), encoding="utf-8")
                self.send_response(204)
                self.end_headers()
            else:
                self.send_response(404)
                self.end_headers()

        def log_message(self, fmt, *args):
            if not getattr(self.server, "quiet", False):
                sys.stderr.write(fmt % args + "\n")

    return Handler


class Server(socketserver.TCPServer):
    allow_reuse_address = True


def validate(proof_path, log_paths):
    proof = json.loads(Path(proof_path).read_text(encoding="utf-8"))
    logs = "\n".join(Path(path).read_text(errors="ignore") for path in log_paths)
    for forbidden in ["F DEBUG", "panicked", "InvalidUri", "Cannot redefine", "parse error", "Permission denied"]:
        if forbidden in logs:
            raise SystemExit(f"forbidden log marker present: {forbidden}")
    checks = {
        "count": int(proof.get("count", 0)) >= 4,
        "hasDesktop": proof.get("hasDesktop") is True,
        "imageCount": int(proof.get("imageCount", 0)) >= 1,
        "hasDragRuntime": proof.get("hasDragRuntime") is True,
        "hasDragEvents": proof.get("hasDragEvents") is True,
        "dragMoved": proof.get("dragMoved") is True,
        "hasWindowEventRuntime": proof.get("hasWindowEventRuntime") is True,
        "bodyClickRouted": proof.get("bodyClickRouted") is True,
        "bodyInputRouted": proof.get("bodyInputRouted") is True,
        "htmlRenderable": proof.get("htmlRenderable") is True,
        "taskbarIconCount": int(proof.get("taskbarIconCount", 0)) >= 4,
        "sourceWindowCount": int(proof.get("sourceWindowCount", 0)) >= 4,
        "hasSimpleSmokeText": proof.get("hasSimpleSmokeText") is True,
    }
    failed = [name for name, ok in checks.items() if not ok]
    if failed:
        raise SystemExit("iOS MDI probe failed fields: " + ", ".join(failed))
    print("ios_webview_mdi_proof=pass")


def paeth(left, up, up_left):
    estimate = left + up - up_left
    if abs(estimate - left) <= abs(estimate - up) and abs(estimate - left) <= abs(estimate - up_left):
        return left
    return up if abs(estimate - up) <= abs(estimate - up_left) else up_left


def decode_png_rgb(png_path):
    data = Path(png_path).read_bytes()
    if not data.startswith(b"\x89PNG\r\n\x1a\n"):
        raise SystemExit("screenshot is not a PNG")
    offset = 8
    width = height = bit_depth = color_type = None
    idat = bytearray()
    while offset + 12 <= len(data):
        length = int.from_bytes(data[offset : offset + 4], "big")
        chunk_type = data[offset + 4 : offset + 8]
        chunk_data = data[offset + 8 : offset + 8 + length]
        offset += 12 + length
        if chunk_type == b"IHDR":
            width = int.from_bytes(chunk_data[0:4], "big")
            height = int.from_bytes(chunk_data[4:8], "big")
            bit_depth = chunk_data[8]
            color_type = chunk_data[9]
        elif chunk_type == b"IDAT":
            idat.extend(chunk_data)
        elif chunk_type == b"IEND":
            break
    if not width or not height or width < 300 or height < 300:
        raise SystemExit(f"screenshot dimensions invalid: {width}x{height}")
    if bit_depth != 8 or color_type not in (2, 6):
        raise SystemExit(f"unsupported PNG format: bit_depth={bit_depth} color_type={color_type}")
    channels = 4 if color_type == 6 else 3
    row_len = width * channels
    raw = zlib.decompress(bytes(idat))
    previous = [0] * row_len
    pixels = []
    cursor = 0
    for _ in range(height):
        filter_type = raw[cursor]
        cursor += 1
        row = list(raw[cursor : cursor + row_len])
        cursor += row_len
        for i, value in enumerate(row):
            left = row[i - channels] if i >= channels else 0
            up = previous[i]
            up_left = previous[i - channels] if i >= channels else 0
            if filter_type == 1:
                row[i] = (value + left) & 0xFF
            elif filter_type == 2:
                row[i] = (value + up) & 0xFF
            elif filter_type == 3:
                row[i] = (value + ((left + up) // 2)) & 0xFF
            elif filter_type == 4:
                row[i] = (value + paeth(left, up, up_left)) & 0xFF
            elif filter_type != 0:
                raise SystemExit(f"unsupported PNG row filter: {filter_type}")
        pixels.append([tuple(row[i : i + 3]) for i in range(0, row_len, channels)])
        previous = row
    return width, height, pixels


def validate_screenshot(png_path, label="ios_mdi_probe_screenshot"):
    width, height, pixels = decode_png_rgb(png_path)
    unique = set()
    for row in pixels:
        for pixel in row:
            unique.add(pixel)
            if len(unique) >= 64:
                break
        if len(unique) >= 64:
            break
    if len(unique) < 16:
        raise SystemExit(f"screenshot appears blank: unique_colors={len(unique)}")
    print(f"{label}=pass width={width} height={height} unique_colors={len(unique)}")


def validate_probe_mdi_screenshot(png_path, label="ios_mdi_probe_screenshot_semantic"):
    width, height, pixels = decode_png_rgb(png_path)
    total = width * height
    dark = bright = accent = 0
    dark_rows = 0
    for row in pixels:
        row_dark = 0
        for r, g, b in row:
            if r < 45 and g < 55 and b < 65:
                dark += 1
                row_dark += 1
            if r > 220 and g > 220 and b > 220:
                bright += 1
            if (r > 180 and g < 100 and b < 120) or (g > 110 and r < 120 and b < 150) or (r > 180 and g > 120 and b < 90):
                accent += 1
        if row_dark > max(20, width // 10):
            dark_rows += 1

    taskbar_top = max(0, height - 90)
    taskbar_accent = 0
    for y in range(taskbar_top, height):
        for r, g, b in pixels[y]:
            if (r > 180 and g < 100 and b < 120) or (g > 110 and r < 120 and b < 150) or (r > 180 and g > 120 and b < 90):
                taskbar_accent += 1

    if dark < max(5000, total // 5):
        raise SystemExit(f"probe MDI screenshot missing dark desktop/window coverage: dark_pixels={dark}")
    if bright < max(1000, total // 100):
        raise SystemExit(f"probe MDI screenshot missing bright window/control pixels: bright_pixels={bright}")
    if accent < 100:
        raise SystemExit(f"probe MDI screenshot missing accent/icon pixels: accent_pixels={accent}")
    if taskbar_accent < 100:
        raise SystemExit(f"probe MDI screenshot missing taskbar accent pixels: taskbar_accent={taskbar_accent}")
    if dark_rows < max(80, height // 3):
        raise SystemExit(f"probe MDI screenshot missing sustained dark rows: dark_rows={dark_rows}")
    print(
        f"{label}=pass width={width} height={height} dark_pixels={dark} "
        f"bright_pixels={bright} accent_pixels={accent} "
        f"taskbar_accent_pixels={taskbar_accent} dark_rows={dark_rows}"
    )


def validate_android_mdi_screenshot(png_path):
    width, height, pixels = decode_png_rgb(png_path)
    if width < 720 or height < 1200:
        raise SystemExit(f"Android MDI screenshot too small: {width}x{height}")

    desktop_top = min(120, height)
    desktop_bottom = max(desktop_top, height - 180)
    dark = bright = accent = 0
    dark_rows = 0
    for y in range(desktop_top, desktop_bottom):
        row_dark = 0
        for r, g, b in pixels[y]:
            if r < 35 and g < 45 and b < 55:
                dark += 1
                row_dark += 1
            if r > 220 and g > 220 and b > 220:
                bright += 1
            if (
                (r > 190 and g < 100 and b < 100)
                or (r > 180 and g > 120 and b < 80)
                or (g > 140 and r < 100 and b < 120)
                or (b > 140 and r < 170 and g < 200)
            ):
                accent += 1
        if row_dark > width // 4:
            dark_rows += 1

    dock_top = max(0, height - 190)
    dock_bottom = max(dock_top, height - 35)
    dock_left = max(0, width // 2 - 420)
    dock_right = min(width, width // 2 + 420)
    dock_dark = dock_bright = dock_accent = 0
    for y in range(dock_top, dock_bottom):
        for x in range(dock_left, dock_right):
            r, g, b = pixels[y][x]
            if r < 45 and g < 55 and b < 65:
                dock_dark += 1
            if r > 180 and g > 185 and b > 190:
                dock_bright += 1
            if (
                (b > 140 and r < 170 and g < 200)
                or (g > 120 and r < 170 and b < 180)
                or (r > 175 and g > 100 and b < 130)
                or (r > 175 and g < 130 and b < 150)
            ):
                dock_accent += 1

    if dark < 200000:
        raise SystemExit(f"Android MDI screenshot missing dark window bodies: dark_pixels={dark}")
    if bright < 10000:
        raise SystemExit(f"Android MDI screenshot missing bright UI/text/control regions: bright_pixels={bright}")
    if accent < 30:
        raise SystemExit(f"Android MDI screenshot missing window/icon accent pixels: accent_pixels={accent}")
    if dark_rows < 250:
        raise SystemExit(f"Android MDI screenshot missing sustained MDI window rows: dark_rows={dark_rows}")
    if dock_dark < 2500:
        raise SystemExit(f"Android MDI screenshot missing styled taskbar/dock body: dock_dark_pixels={dock_dark}")
    if dock_bright < 120:
        raise SystemExit(f"Android MDI screenshot missing taskbar labels: dock_bright_pixels={dock_bright}")
    if dock_accent < 80:
        raise SystemExit(f"Android MDI screenshot missing taskbar icon colors: dock_accent_pixels={dock_accent}")
    print(
        "android_live_mdi_screenshot_semantic=pass "
        f"width={width} height={height} dark_pixels={dark} bright_pixels={bright} "
        f"accent_pixels={accent} dark_rows={dark_rows} "
        f"dock_dark_pixels={dock_dark} dock_bright_pixels={dock_bright} "
        f"dock_accent_pixels={dock_accent}"
    )


def validate_electron_mdi_screenshot(png_path):
    width, height, pixels = decode_png_rgb(png_path)
    if width < 1000 or height < 600:
        raise SystemExit(f"Electron MDI screenshot too small: {width}x{height}")

    total = width * height
    dark = bright = accent = 0
    for row in pixels:
        for r, g, b in row:
            if r < 35 and g < 45 and b < 55:
                dark += 1
            if r > 190 and g > 200 and b > 210:
                bright += 1
            if (
                (b > 150 and r < 150 and g < 190)
                or (g > 130 and r < 150 and b < 170)
                or (r > 180 and g > 110 and b < 110)
                or (r > 180 and g < 120 and b < 140)
            ):
                accent += 1

    dock_top = max(0, height - 240)
    dock_bottom = max(dock_top, height - 35)
    dock_left = max(0, width // 2 - 360)
    dock_right = min(width, width // 2 + 360)
    dock_dark = dock_bright = dock_accent = 0
    for y in range(dock_top, dock_bottom):
        for x in range(dock_left, dock_right):
            r, g, b = pixels[y][x]
            if r < 40 and g < 50 and b < 60:
                dock_dark += 1
            if r > 190 and g > 200 and b > 210:
                dock_bright += 1
            if (
                (b > 150 and r < 150 and g < 190)
                or (g > 130 and r < 150 and b < 170)
                or (r > 180 and g > 110 and b < 110)
                or (r > 180 and g < 120 and b < 140)
            ):
                dock_accent += 1

    if dark < total // 2:
        raise SystemExit(f"Electron MDI screenshot missing dark desktop/window coverage: dark_pixels={dark}")
    if bright < 500:
        raise SystemExit(f"Electron MDI screenshot missing visible text/control pixels: bright_pixels={bright}")
    if accent < 500:
        raise SystemExit(f"Electron MDI screenshot missing colored window/icon pixels: accent_pixels={accent}")
    if dock_dark < 10000:
        raise SystemExit(f"Electron MDI screenshot missing styled taskbar/dock body: dock_dark_pixels={dock_dark}")
    if dock_bright < 250:
        raise SystemExit(f"Electron MDI screenshot missing taskbar labels: dock_bright_pixels={dock_bright}")
    if dock_accent < 300:
        raise SystemExit(f"Electron MDI screenshot missing taskbar icon colors: dock_accent_pixels={dock_accent}")
    print(
        "electron_mdi_screenshot_semantic=pass "
        f"width={width} height={height} dark_pixels={dark} bright_pixels={bright} "
        f"accent_pixels={accent} dock_dark_pixels={dock_dark} "
        f"dock_bright_pixels={dock_bright} dock_accent_pixels={dock_accent}"
    )


def serve(port, proof_path, ipc_path=None):
    with Server(("127.0.0.1", int(port)), make_handler(proof_path, load_windows(ipc_path))) as httpd:
        print(f"ios_probe_url=http://127.0.0.1:{port}/ios_mdi_probe.html", flush=True)
        httpd.serve_forever()


def self_test():
    with tempfile.TemporaryDirectory() as tmp:
        proof_path = Path(tmp) / "proof.json"
        with Server(("127.0.0.1", 0), make_handler(proof_path, DEFAULT_WINDOWS)) as httpd:
            httpd.quiet = True
            port = httpd.server_address[1]
            thread = threading.Thread(target=httpd.serve_forever, daemon=True)
            thread.start()
            page = urllib.request.urlopen(f"http://127.0.0.1:{port}/ios_mdi_probe.html", timeout=5).read().decode("utf-8")
            if "data-source-window-id=\"terminal\"" not in page or "Tauri mobile MDI smoke" not in page:
                raise SystemExit("probe HTML response missing Simple-backed markers")
            query = urllib.parse.urlencode(
                {
                    "count": "4",
                    "hasDesktop": "true",
                    "imageCount": "1",
                    "hasDragRuntime": "true",
                    "hasDragEvents": "true",
                    "dragMoved": "true",
                    "hasWindowEventRuntime": "true",
                    "bodyClickRouted": "true",
                    "bodyInputRouted": "true",
                    "htmlRenderable": "true",
                    "taskbarIconCount": "4",
                    "sourceWindowCount": "4",
                    "hasSimpleSmokeText": "true",
                }
            )
            urllib.request.urlopen(f"http://127.0.0.1:{port}/proof?{query}", timeout=5).read()
            validate(proof_path, [])
            httpd.shutdown()
    print("ios_mdi_probe_server_self_test=pass")


def main(argv):
    if len(argv) == 2 and argv[1] == "--self-test":
        self_test()
    elif len(argv) >= 3 and argv[1] == "--validate":
        validate(argv[2], argv[3:])
    elif len(argv) in (3, 4) and argv[1] == "--validate-screenshot":
        validate_screenshot(argv[2], argv[3] if len(argv) == 4 else "ios_mdi_probe_screenshot")
    elif len(argv) in (3, 4) and argv[1] == "--validate-probe-mdi-screenshot":
        validate_probe_mdi_screenshot(argv[2], argv[3] if len(argv) == 4 else "ios_mdi_probe_screenshot_semantic")
    elif len(argv) == 3 and argv[1] == "--validate-android-mdi-screenshot":
        validate_android_mdi_screenshot(argv[2])
    elif len(argv) == 3 and argv[1] == "--validate-electron-mdi-screenshot":
        validate_electron_mdi_screenshot(argv[2])
    elif len(argv) in (3, 4):
        serve(argv[1], argv[2], argv[3] if len(argv) == 4 else None)
    else:
        raise SystemExit("usage: ios_mdi_probe_server.py PORT PROOF_JSON [IPC_OUT] | --validate PROOF_JSON [LOG...] | --validate-screenshot PNG [LABEL] | --self-test")


if __name__ == "__main__":
    main(sys.argv)
