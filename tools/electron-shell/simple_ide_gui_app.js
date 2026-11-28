// Electron launcher for the Simple IDE Liquid Glass GUI Shell.
//
// Usage:
//   Interactive 1380x860 sRGB window:
//     electron tools/electron-shell/simple_ide_gui_app.js [--captures <dir>] [--theme fluid_dark] [--profile editor]
//   Offscreen smoke check (prints "[simple-ide-gui] ready" and exits 0):
//     electron tools/electron-shell/simple_ide_gui_app.js --smoke [--captures <dir>]

const fs = require("fs");
const os = require("os");
const path = require("path");
const { app, BrowserWindow } = require("electron");

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

const IS_SMOKE = hasFlag("--smoke") || hasFlag("--headless");
const CAPTURES_DIR = resolveCapturesDir();
const WORKSPACE_DIR = path.resolve(argValue("--workspace", path.resolve(__dirname, "../..")));
const DEFAULT_THEME = argValue("--theme", "fluid_dark");
const DEFAULT_PROFILE = argValue("--profile", "editor");

if (IS_SMOKE && app.dock) {
  app.dock.hide();
}

function createIdeWindow() {
  const win = new BrowserWindow({
    width: 1380,
    height: 860,
    minWidth: 1080,
    minHeight: 700,
    useContentSize: true,
    title: "Simple IDE — Liquid Glass GUI",
    titleBarStyle: "default",
    backgroundColor: "#080d17",
    show: !IS_SMOKE,
    webPreferences: {
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
    if (!IS_SMOKE) {
      console.log(
        `[simple-ide-gui] ready (theme=${DEFAULT_THEME} profile=${DEFAULT_PROFILE} captures=${CAPTURES_DIR})`
      );
      return;
    }

    try {
      const smokeResult = await win.webContents.executeJavaScript(`(async () => {
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
          hasFloatingInspector: Boolean(floating)
        };
      })()`);
      const imgsOk = smokeResult && smokeResult.e2dImg && smokeResult.e2dImg.ok && smokeResult.webImg && smokeResult.webImg.ok;
      if (!smokeResult || !smokeResult.hasEditor || smokeResult.tabCount < 2 || !smokeResult.hasFloatingInspector || smokeResult.dirtyDots < 1 || !imgsOk) {
        console.error("[simple-ide-gui] smoke check failed:", JSON.stringify(smokeResult));
        win.destroy();
        app.exit(1);
        return;
      }
      console.log(
        `[simple-ide-gui] ready (smoke ok: tabs=${smokeResult.tabCount} tree=${smokeResult.treeCount} outline=${smokeResult.outlineCount} e2d=${smokeResult.e2dImg.w}x${smokeResult.e2dImg.h} web=${smokeResult.webImg.w}x${smokeResult.webImg.h} themes=${smokeResult.obsidianTheme}/${smokeResult.lightTheme}/${smokeResult.finalTheme} cursor=${smokeResult.cursorText})`
      );
      win.destroy();
      app.quit();
    } catch (err) {
      console.error("[simple-ide-gui] smoke error:", err);
      win.destroy();
      app.exit(1);
    }
  });
}

app.whenReady().then(() => {
  createIdeWindow();
});

app.on("window-all-closed", () => {
  app.quit();
});
