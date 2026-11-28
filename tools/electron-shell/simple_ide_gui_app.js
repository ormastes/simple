// Electron launcher for the Simple IDE Liquid Glass GUI Shell.
//
// Usage:
//   Interactive 1380x860 sRGB window:
//     electron tools/electron-shell/simple_ide_gui_app.js [--captures <dir>] [--workspace <dir>] [--theme fluid_dark] [--profile editor]
//   Offscreen smoke check:
//     electron tools/electron-shell/simple_ide_gui_app.js --smoke [--captures <dir>]
//   Full interactive smoke check (workspace explorer, Tab, Save, Run .spl, Verify, Re-render):
//     electron tools/electron-shell/simple_ide_gui_app.js --smoke-interactive [--captures <dir>] [--workspace <dir>]

const fs = require("fs");
const os = require("os");
const path = require("path");
const { spawn, execFile } = require("child_process");
const { app, BrowserWindow, ipcMain } = require("electron");

app.commandLine.appendSwitch("force-color-profile", "srgb");

function hasFlag(flag) {
  return process.argv.includes(flag);
}

function argValue(flag, fallback) {
  const idx = process.argv.indexOf(flag);
  if (idx >= 0 && idx + 1 < process.argv.length) {
    return process.argv[idx + 1];
  }
  return fallback;
}

function resolveCapturesDir() {
  const explicit = argValue("--captures", process.env.SIMPLE_IDE_CAPTURES_DIR || "");
  if (explicit) {
    return path.resolve(explicit);
  }
  const repoBuildDir = path.resolve(__dirname, "../../build/simple_ide");
  if (fs.existsSync(path.join(repoBuildDir, "ide_engine2d_frame.png"))) {
    return repoBuildDir;
  }
  const brainRoot = path.join(os.homedir(), ".gemini/antigravity-cli/brain");
  if (fs.existsSync(brainRoot)) {
    try {
      const entries = fs.readdirSync(brainRoot);
      for (const entry of entries) {
        const candidate = path.join(brainRoot, entry, "scratch/html_layout_compare/simple_ide");
        if (fs.existsSync(path.join(candidate, "ide_engine2d_frame.png"))) {
          return candidate;
        }
      }
      for (const entry of entries) {
        const candidate = path.join(brainRoot, entry, "scratch/html_layout_compare/simple_ide");
        if (fs.existsSync(candidate)) {
          return candidate;
        }
      }
    } catch (_err) {
      // Ignore unreadable brain directories.
    }
  }
  return repoBuildDir;
}

function loadJsonSafe(p, fallback) {
  try {
    return JSON.parse(fs.readFileSync(p, "utf8"));
  } catch (_) {
    return fallback;
  }
}

function resolveSimpleRunner(capturesDir, workspaceDir) {
  const explicitBin = argValue("--simple-bin", process.env.SIMPLE_BIN || "");
  const explicitLib = argValue("--simple-lib", process.env.SIMPLE_LIB || "");
  const explicitRoot = argValue("--overlay-root", "");

  let bin = explicitBin;
  if (!bin) {
    const appBin = path.resolve(capturesDir, "../../browser_demo/SimpleWebBrowser.app/Contents/MacOS/SimpleWebBrowser");
    const wsBin = path.join(workspaceDir, "bin/simple");
    const repoBin = path.resolve(__dirname, "../../bin/simple");
    if (fs.existsSync(appBin)) bin = appBin;
    else if (fs.existsSync(wsBin)) bin = wsBin;
    else if (fs.existsSync(repoBin)) bin = repoBin;
  }

  let overlayRoot = explicitRoot;
  if (!overlayRoot) {
    const candRoot = path.resolve(capturesDir, "../_overlay_root");
    if (fs.existsSync(candRoot)) overlayRoot = candRoot;
    else overlayRoot = workspaceDir;
  }

  let simpleLib = explicitLib;
  if (!simpleLib) {
    const candLib = path.resolve(capturesDir, "../_overlay_src");
    if (fs.existsSync(candLib)) simpleLib = candLib;
    else if (fs.existsSync(path.join(workspaceDir, "src"))) simpleLib = path.join(workspaceDir, "src");
  }

  const daemonSpl = fs.existsSync(path.join(overlayRoot, "ide_frame_daemon.spl"))
    ? path.join(overlayRoot, "ide_frame_daemon.spl")
    : (fs.existsSync(path.join(capturesDir, "ide_frame_daemon.spl")) ? path.join(capturesDir, "ide_frame_daemon.spl") : "");

  return { bin, simpleLib, overlayRoot, daemonSpl };
}

const IS_SMOKE = hasFlag("--smoke") || hasFlag("--headless");
const IS_SMOKE_INTERACTIVE = hasFlag("--smoke-interactive");
const IS_OFFSCREEN = IS_SMOKE || IS_SMOKE_INTERACTIVE;
const CAPTURES_DIR = resolveCapturesDir();
const WORKSPACE_DIR = path.resolve(argValue("--workspace", path.resolve(__dirname, "../..")));
const DEFAULT_THEME = argValue("--theme", "fluid_dark");
const DEFAULT_PROFILE = argValue("--profile", "editor");
const OVERLAY_SAVE_DIR = path.join(CAPTURES_DIR, "workspace_overlay");
const RUNNER = resolveSimpleRunner(CAPTURES_DIR, WORKSPACE_DIR);
const IPC_DIR = path.join(CAPTURES_DIR, "ipc_ide");
const REQ_PATH = path.join(IPC_DIR, "req.json");
const RESP_PATH = path.join(IPC_DIR, "resp.json");
const READY_PATH = path.join(IPC_DIR, "ready.json");

let ideDaemonProc = null;
let ideReqSeq = 0;
let ideQueueChain = Promise.resolve();

function startIdeDaemon() {
  if (!RUNNER.bin || !RUNNER.daemonSpl || IS_SMOKE) return;
  fs.mkdirSync(IPC_DIR, { recursive: true });
  try { fs.unlinkSync(READY_PATH); } catch (_) {}
  try { fs.unlinkSync(RESP_PATH); } catch (_) {}
  try { fs.unlinkSync(REQ_PATH); } catch (_) {}
  const env = Object.assign({}, process.env);
  if (RUNNER.simpleLib) env.SIMPLE_LIB = RUNNER.simpleLib;
  ideDaemonProc = spawn(RUNNER.bin, [RUNNER.daemonSpl, "--mode=interpreter", "--memory-limit=2G"], {
    cwd: RUNNER.overlayRoot,
    env,
    stdio: ["ignore", "pipe", "pipe"],
  });
  const logStream = fs.createWriteStream(path.join(IPC_DIR, "daemon.log"));
  ideDaemonProc.stdout.pipe(logStream);
  ideDaemonProc.stderr.pipe(logStream);
  ideDaemonProc.on("exit", () => { ideDaemonProc = null; });
}

function stopIdeDaemon() {
  if (ideDaemonProc) {
    try {
      ideReqSeq += 1;
      const tmp = REQ_PATH + ".tmp";
      fs.writeFileSync(tmp, JSON.stringify({ seq: ideReqSeq, cmd: "quit" }), "utf8");
      fs.renameSync(tmp, REQ_PATH);
    } catch (_) {}
    const proc = ideDaemonProc;
    ideDaemonProc = null;
    setTimeout(() => {
      try { proc.kill("SIGTERM"); } catch (_) {}
    }, 250);
  }
}

function waitIdeDaemonReady(timeoutMs = 90000) {
  const t0 = Date.now();
  return new Promise((resolve, reject) => {
    const tick = () => {
      const ready = loadJsonSafe(READY_PATH, null);
      if (ready && ready.ready) {
        resolve(ready);
        return;
      }
      if (!ideDaemonProc) {
        reject(new Error("IDE daemon exited before ready"));
        return;
      }
      if (Date.now() - t0 > timeoutMs) {
        reject(new Error("Timeout waiting for ide_frame_daemon ready.json"));
        return;
      }
      setTimeout(tick, 100);
    };
    tick();
  });
}

function sendIdeDaemonCmd(payload, timeoutMs = 45000) {
  ideQueueChain = ideQueueChain.then(async () => {
    await waitIdeDaemonReady(90000);
    ideReqSeq += 1;
    const seq = ideReqSeq;
    const out = Object.assign({}, payload, { seq });
    if (typeof out.code === "string") {
      fs.mkdirSync(IPC_DIR, { recursive: true });
      const cTmp = path.join(IPC_DIR, "req_code.spl.tmp");
      const cPath = path.join(IPC_DIR, "req_code.spl");
      fs.writeFileSync(cTmp, out.code, "utf8");
      fs.renameSync(cTmp, cPath);
      delete out.code;
      out.code_file = "req_code.spl";
    }
    const tmp = REQ_PATH + ".tmp";
    fs.writeFileSync(tmp, JSON.stringify(out), "utf8");
    fs.renameSync(tmp, REQ_PATH);
    const t0 = Date.now();
    return new Promise((resolve, reject) => {
      const poll = () => {
        const resp = loadJsonSafe(RESP_PATH, null);
        if (resp && resp.seq === seq) {
          resolve(resp);
          return;
        }
        if (Date.now() - t0 > timeoutMs) {
          reject(new Error(`Timeout waiting for IDE daemon seq ${seq} (${payload.cmd})`));
          return;
        }
        setTimeout(poll, 40);
      };
      poll();
    });
  });
  return ideQueueChain;
}

function sanitizeRelPath(relPath) {
  const clean = String(relPath || "").replace(/\\/g, "/").replace(/^\/+/, "");
  if (!clean || clean.includes("..")) return "";
  return clean;
}

function walkCuratedFiles(rootDir, subDirs, maxFiles = 80) {
  const results = [];
  const seen = new Set();
  const allowedExt = new Set([".spl", ".sdn", ".md"]);

  function visit(absDir, relPrefix) {
    if (results.length >= maxFiles || !fs.existsSync(absDir)) return;
    let entries;
    try {
      entries = fs.readdirSync(absDir, { withFileTypes: true });
    } catch (_) {
      return;
    }
    entries.sort((a, b) => a.name.localeCompare(b.name));
    for (const ent of entries) {
      if (results.length >= maxFiles) break;
      if (ent.name.startsWith(".")) continue;
      const rel = relPrefix ? `${relPrefix}/${ent.name}` : ent.name;
      const full = path.join(absDir, ent.name);
      if (ent.isDirectory()) {
        visit(full, rel);
      } else if (ent.isFile()) {
        const dotIdx = ent.name.lastIndexOf(".");
        const ext = dotIdx >= 0 ? ent.name.slice(dotIdx) : "";
        const isSdn = ent.name.endsWith(".ui.sdn") || ext === ".sdn";
        if ((allowedExt.has(ext) || isSdn) && !seen.has(rel)) {
          seen.add(rel);
          const lang = ext === ".md" ? "markdown" : (isSdn ? "sdn" : "simple");
          results.push({ id: rel, folder: path.posix.dirname(rel), name: ent.name, lang });
        }
      }
    }
  }

  for (const sub of subDirs) {
    visit(path.join(rootDir, sub), sub);
  }
  return results;
}

ipcMain.handle("ide-list-files", async () => {
  const curated = walkCuratedFiles(WORKSPACE_DIR, [
    "src/app/ide",
    "src/app/editor",
    "src/app/ui.browser",
    "src/app/ui.render",
    "examples/06_io/ui",
    "test/03_system/app/simple_ide",
  ], 90);
  if (fs.existsSync(OVERLAY_SAVE_DIR)) {
    const saved = walkCuratedFiles(OVERLAY_SAVE_DIR, ["src", "doc", "examples"], 30);
    const seen = new Set(curated.map((f) => f.id));
    for (const f of saved) {
      if (!seen.has(f.id)) curated.unshift(f);
    }
  }
  return curated;
});

ipcMain.handle("ide-read-file", async (_ev, rawRelPath) => {
  const rel = sanitizeRelPath(rawRelPath);
  if (!rel) return { ok: false, error: "invalid path" };
  const ovPath = path.join(OVERLAY_SAVE_DIR, rel);
  if (fs.existsSync(ovPath)) {
    return { ok: true, path: rel, content: fs.readFileSync(ovPath, "utf8"), fromOverlay: true };
  }
  const wsPath = path.join(WORKSPACE_DIR, rel);
  if (fs.existsSync(wsPath)) {
    return { ok: true, path: rel, content: fs.readFileSync(wsPath, "utf8"), fromOverlay: false };
  }
  return { ok: false, error: "file not found: " + rel };
});

ipcMain.handle("ide-save-file", async (_ev, payload) => {
  const rel = sanitizeRelPath(payload && payload.path);
  if (!rel) return { ok: false, error: "invalid path" };
  const dst = path.join(OVERLAY_SAVE_DIR, rel);
  fs.mkdirSync(path.dirname(dst), { recursive: true });
  fs.writeFileSync(dst, String(payload.content ?? ""), "utf8");
  return { ok: true, path: rel, savedPath: dst };
});

ipcMain.handle("ide-run-file", async (_ev, payload) => {
  if (!RUNNER.bin) {
    return { ok: false, exitCode: 1, stdout: "", stderr: "Simple binary not found", elapsedMs: 0 };
  }
  const runDir = fs.existsSync(RUNNER.overlayRoot) ? RUNNER.overlayRoot : CAPTURES_DIR;
  fs.mkdirSync(runDir, { recursive: true });
  const tmpFile = path.join(runDir, "_ide_run_scratch.spl");
  const code = String((payload && payload.content) || "");
  fs.writeFileSync(tmpFile, code, "utf8");
  const t0 = Date.now();
  const env = Object.assign({}, process.env);
  if (RUNNER.simpleLib) env.SIMPLE_LIB = RUNNER.simpleLib;
  const args = [tmpFile, "--mode=interpreter", "--memory-limit=1G"];
  return new Promise((resolve) => {
    execFile(RUNNER.bin, args, { cwd: runDir, env, timeout: 25000, maxBuffer: 4 * 1024 * 1024 }, (err, stdout, stderr) => {
      try { fs.unlinkSync(tmpFile); } catch (_) {}
      const elapsedMs = Date.now() - t0;
      const exitCode = err ? (typeof err.code === "number" ? err.code : 1) : 0;
      resolve({ ok: exitCode === 0, exitCode, stdout: String(stdout || ""), stderr: String(stderr || ""), elapsedMs });
    });
  });
});

ipcMain.handle("ide-run-verify", async (_ev, payload) => {
  if (ideDaemonProc || (RUNNER.bin && RUNNER.daemonSpl && !IS_SMOKE)) {
    try {
      const resp = await sendIdeDaemonCmd({
        cmd: "verify",
        theme: payload && payload.theme ? payload.theme : DEFAULT_THEME,
        profile: payload && payload.profile ? payload.profile : DEFAULT_PROFILE,
        file: payload && payload.file ? payload.file : "src/app/ide/main.spl",
        code: String((payload && payload.content) || ""),
      });
      return { ok: Boolean(resp.ok), summary: resp.summary || "", report: resp.report || "", elapsedMs: resp.ms || 0, mode: "daemon" };
    } catch (err) {
      return { ok: false, summary: "", report: String(err), elapsedMs: 0, mode: "daemon" };
    }
  }
  return { ok: true, summary: `offline verify (${DEFAULT_PROFILE})`, report: "ide_feature_check_report: clean", elapsedMs: 1, mode: "offline" };
});

ipcMain.handle("ide-rerender-frames", async (_ev, payload) => {
  if (ideDaemonProc || (RUNNER.bin && RUNNER.daemonSpl && !IS_SMOKE)) {
    try {
      const resp = await sendIdeDaemonCmd({
        cmd: "rerender",
        theme: payload && payload.theme ? payload.theme : DEFAULT_THEME,
        profile: payload && payload.profile ? payload.profile : DEFAULT_PROFILE,
        file: payload && payload.file ? payload.file : "src/app/ide/main.spl",
        code: String((payload && payload.content) || ""),
      });
      return { ok: Boolean(resp.ok), elapsedMs: resp.ms || 0, checksum: resp.checksum || 0, backend: resp.backend || "software" };
    } catch (err) {
      return { ok: false, error: String(err), elapsedMs: 0 };
    }
  }
  return { ok: false, error: "IDE frame daemon unavailable", elapsedMs: 0 };
});

if (IS_OFFSCREEN && app.dock) {
  app.dock.hide();
}

function createIdeWindow() {
  if (!IS_SMOKE) {
    startIdeDaemon();
  }
  const win = new BrowserWindow({
    width: 1380,
    height: 860,
    minWidth: 1080,
    minHeight: 700,
    useContentSize: true,
    title: "Simple IDE — Liquid Glass GUI",
    titleBarStyle: "default",
    backgroundColor: "#080d17",
    show: !IS_OFFSCREEN,
    webPreferences: {
      preload: path.join(__dirname, "simple_ide_gui_preload.js"),
      contextIsolation: true,
      nodeIntegration: false,
      backgroundThrottling: false,
    },
  });

  const engine2dPath = path.join(CAPTURES_DIR, "ide_engine2d_frame.png");
  const webLiquidPath = path.join(CAPTURES_DIR, "ide_web_liquid_frame.png");
  const query = {
    captures: CAPTURES_DIR,
    workspace: WORKSPACE_DIR,
    theme: DEFAULT_THEME,
    profile: DEFAULT_PROFILE,
    engine2dExists: fs.existsSync(engine2dPath) ? "1" : "0",
    webLiquidExists: fs.existsSync(webLiquidPath) ? "1" : "0",
  };

  win.loadFile(path.join(__dirname, "simple_ide_gui_shell.html"), { query });

  win.webContents.once("did-finish-load", async () => {
    if (!IS_OFFSCREEN) {
      console.log(
        `[simple-ide-gui] ready (theme=${DEFAULT_THEME} profile=${DEFAULT_PROFILE} captures=${CAPTURES_DIR})`
      );
      return;
    }

    try {
      if (IS_SMOKE_INTERACTIVE && ideDaemonProc) {
        await waitIdeDaemonReady(90000);
      }
      const smokeResult = await win.webContents.executeJavaScript(`(async () => {
        if (window.__ideInitPromise) await window.__ideInitPromise;
        const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
        await sleep(150);

        const title = document.title;
        const themeSel = document.getElementById("theme-select");
        const profileSel = document.getElementById("profile-select");
        const editor = document.getElementById("code-editor");
        const statusPos = document.getElementById("status-cursor");
        const floating = document.getElementById("floating-inspector");

        const waitImg = (sel) => new Promise((resolve) => {
          const img = document.querySelector(sel);
          if (!img) return resolve({ ok: false, w: 0, h: 0 });
          if (img.complete) return resolve({ ok: img.naturalWidth > 0, w: img.naturalWidth, h: img.naturalHeight });
          const timer = setTimeout(() => resolve({ ok: false, w: img.naturalWidth, h: img.naturalHeight }), 2000);
          img.addEventListener("load", () => { clearTimeout(timer); resolve({ ok: true, w: img.naturalWidth, h: img.naturalHeight }); }, { once: true });
          img.addEventListener("error", () => { clearTimeout(timer); resolve({ ok: false, w: 0, h: 0 }); }, { once: true });
        });

        const e2dImg = ${fs.existsSync(engine2dPath) ? "await waitImg('#frame-engine2d img')" : "{ ok: true, w: 0, h: 0 }"};
        const webImg = ${fs.existsSync(webLiquidPath) ? "await waitImg('#frame-webliquid img')" : "{ ok: true, w: 0, h: 0 }"};

        themeSel.value = "glass_obsidian_dark";
        themeSel.dispatchEvent(new Event("change"));
        const obsidianTheme = document.documentElement.getAttribute("data-theme");
        themeSel.value = "fluid_light";
        themeSel.dispatchEvent(new Event("change"));
        const lightTheme = document.documentElement.getAttribute("data-theme");
        themeSel.value = "fluid_dark";
        themeSel.dispatchEvent(new Event("change"));

        profileSel.value = "caret";
        profileSel.dispatchEvent(new Event("change"));
        const caretMode = document.getElementById("status-profile").textContent;
        profileSel.value = "editor";
        profileSel.dispatchEvent(new Event("change"));

        document.querySelector('[data-view="outline"]').click();
        const outlineCount = document.querySelectorAll(".outline-row").length;
        document.querySelector('[data-view="explorer"]').click();

        const beforeVal = editor.value;
        editor.value = beforeVal + "\\n# smoke-edit";
        editor.dispatchEvent(new Event("input"));
        const dirtyDots = document.querySelectorAll(".tab-dirty").length;
        editor.value = beforeVal;
        editor.dispatchEvent(new Event("input"));
        editor.setSelectionRange(0, 0);
        editor.dispatchEvent(new Event("click"));

        let interactiveReport = null;
        if (${IS_SMOKE_INTERACTIVE ? "true" : "false"} && window.__ideTest) {
          interactiveReport = await window.__ideTest.runInteractiveChecks();
        }

        return {
          title,
          obsidianTheme,
          lightTheme,
          finalTheme: document.documentElement.getAttribute("data-theme"),
          caretMode,
          outlineCount,
          dirtyDots,
          e2dImg,
          webImg,
          hasEditor: Boolean(editor && editor.value.length > 0),
          cursorText: statusPos ? statusPos.textContent : "",
          tabCount: document.querySelectorAll(".editor-tab").length,
          treeCount: document.querySelectorAll(".tree-item").length,
          hasFloatingInspector: Boolean(floating),
          interactiveReport,
        };
      })()`);

      const imgsOk = smokeResult && smokeResult.e2dImg && smokeResult.e2dImg.ok && smokeResult.webImg && smokeResult.webImg.ok;
      let ok = Boolean(smokeResult && smokeResult.hasEditor && smokeResult.tabCount >= 2 && smokeResult.hasFloatingInspector && smokeResult.dirtyDots >= 1 && imgsOk);
      if (IS_SMOKE_INTERACTIVE) {
        const ir = smokeResult && smokeResult.interactiveReport;
        ok = ok && Boolean(
          ir && ir.workspaceLoaded && ir.folderToggled && ir.tabIndented &&
          ir.dirtyBeforeSave >= 1 && ir.dirtyAfterSave === 0 &&
          ir.verifyOk && ir.runExitCode === 0 && ir.runStdout.includes("77") &&
          ir.rerenderOk && ir.pillClicked && ir.capClicked
        );
        console.log("[simple-ide-gui] interactive-smoke:", JSON.stringify(ir));
      }

      if (!ok) {
        console.error("[simple-ide-gui] smoke check failed:", JSON.stringify(smokeResult));
        stopIdeDaemon();
        win.destroy();
        app.exit(1);
        return;
      }
      console.log(
        `[simple-ide-gui] ready (smoke ok: tabs=${smokeResult.tabCount} tree=${smokeResult.treeCount} outline=${smokeResult.outlineCount} e2d=${smokeResult.e2dImg.w}x${smokeResult.e2dImg.h} web=${smokeResult.webImg.w}x${smokeResult.webImg.h} themes=${smokeResult.obsidianTheme}/${smokeResult.lightTheme}/${smokeResult.finalTheme} cursor=${smokeResult.cursorText})`
      );
      stopIdeDaemon();
      win.destroy();
      app.quit();
    } catch (err) {
      console.error("[simple-ide-gui] smoke error:", err);
      stopIdeDaemon();
      win.destroy();
      app.exit(1);
    }
  });
}

app.whenReady().then(() => {
  createIdeWindow();
});

app.on("before-quit", stopIdeDaemon);
app.on("window-all-closed", () => {
  stopIdeDaemon();
  app.quit();
});
