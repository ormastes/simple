const { contextBridge, ipcRenderer } = require("electron");

contextBridge.exposeInMainWorld("simpleIdeBridge", {
  listWorkspaceFiles: () => ipcRenderer.invoke("ide-list-files"),
  readFile: (relPath) => ipcRenderer.invoke("ide-read-file", relPath),
  saveFile: (payload) => ipcRenderer.invoke("ide-save-file", payload),
  runFile: (payload) => ipcRenderer.invoke("ide-run-file", payload),
  runVerify: (payload) => ipcRenderer.invoke("ide-run-verify", payload),
  rerenderFrames: (payload) => ipcRenderer.invoke("ide-rerender-frames", payload),
});
