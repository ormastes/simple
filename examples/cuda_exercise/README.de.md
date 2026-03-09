# CUDA Übungsprojekt

Ein CUDA-Entwicklungsprojekt-Template mit CMake-Build-System und VS Code-Integration.

**Sprachversionen:** [English](README.md) | [한국어](README.ko.md) | [日本語](README.ja.md) | [Français](README.fr.md) | [中文](README.zh.md) | [Español](README.es.md) | [Italiano](README.it.md) | [Nederlands](README.nl.md) | [Português](README.pt.md) | [Русский](README.ru.md)

## Getestete Konfigurationen

✅ **Erfolgreich getestet mit:**
- Ubuntu 24.04 LTS
- Clang 20
- CUDA Toolkit 13.0
- CMake 3.28+
- Ninja 1.11+

## Voraussetzungen

- CUDA Toolkit (12.0 oder neuer, getestet mit 13.0)
- CMake (3.24 oder neuer)
- Ninja Build System
- Clang/LLVM Compiler (getestet mit Clang 20) oder GCC

## Projekt Build

### Kommandozeile verwenden

```bash
# Build-Verzeichnis erstellen
mkdir build
cd build

# Mit Ninja und Clang konfigurieren
cmake -G Ninja -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug ..

# Build
ninja
```

### VS Code verwenden

1. Projektordner in VS Code öffnen
2. `Ctrl+Shift+P` drücken und "CMake: Select Configure Preset" ausführen
3. "default" für Debug oder "release" für Release Build wählen
4. `F7` drücken zum Build

## Projektstruktur

```
.
├── CMakeLists.txt          # Haupt-CMake-Konfiguration
├── CMakePresets.json       # CMake-Presets für einfache Konfiguration
├── demo/                   # Einfache CUDA-Ausführbare Datei
│   ├── CMakeLists.txt
│   └── src.cu
├── demo_lib/              # CUDA-Bibliothek mit separater Kompilierung
│   ├── CMakeLists.txt
│   ├── kernel.cu
│   ├── kernel.h
│   └── src.cpp
└── .vscode/               # VS Code-Konfiguration
    ├── settings.json      # CMake- und Build-Einstellungen
    └── launch.json        # Debug-Konfigurationen
```

## VS Code-Erweiterungen für CUDA-Entwicklung

### Erforderliche Erweiterungen

1. **C/C++ Extension Pack** (`ms-vscode.cpptools-extension-pack`)
   - Bietet IntelliSense, Debugging und Code-Browsing
   - Enthält C/C++-Themes und CMake Tools

2. **CMake Tools** (`ms-vscode.cmake-tools`)
   - CMake-Integration mit VS Code
   - Build, Konfiguration und Debug von CMake-Projekten

3. **Nsight Visual Studio Code Edition** (`nvidia.nsight-vscode-edition`)
   - CUDA-Debugging-Unterstützung
   - GPU-Kernel-Debugging
   - CUDA-GDB-Integration

4. **Catch2 Test Adapter** (`matepek.vscode-catch2-test-adapter`)
   - Catch2-Tests von VS Code ausführen und debuggen
   - Test-Explorer-Integration
   - Visuelle Test-Status-Anzeigen

### Empfohlene Erweiterungen

5. **CUDA C++** (`kriegalex.vscode-cuda`)
   - CUDA-Syntax-Highlighting
   - Snippets für CUDA-Programmierung

6. **C/C++ Snippets** (`hars.cppsnippets`)
   - Nützliche Code-Snippets für C/C++-Entwicklung

7. **Better C++ Syntax** (`jeff-hykin.better-cpp-syntax`)
   - Verbessertes Syntax-Highlighting für modernes C++

8. **Clangd** (`llvm-vs-code-extensions.vscode-clangd`)
   - Alternative zu Microsoft C++ IntelliSense
   - Bessere Unterstützung für Clang-spezifische Features
   - Genauere Code-Vervollständigung und Diagnostik

9. **LLDB DAP** (`llvm-vs-code-extensions.lldb-dap`)
   - LLDB-Debugger-Integration
   - Bessere Debugging-Erfahrung mit Clang-kompiliertem Code

### Optionale Erweiterungen

10. **Error Lens** (`usernamehw.errorlens`)
    - Zeigt Fehler und Warnungen inline an

11. **GitLens** (`eamodio.gitlens`)
    - Verbesserte Git-Integration

12. **Code Spell Checker** (`streetsidesoftware.code-spell-checker`)
    - Rechtschreibprüfung für Code und Kommentare

## Installation der VS Code-Erweiterungen

### Methode 1: Automatisierte Installationsskripte

**Linux/macOS:**
```bash
./scripts/install-vscode-extensions.sh
```

**Windows:**
```batch
install-vscode-extensions.bat
```

### Methode 2: Über VS Code UI
1. VS Code öffnen
2. Auf Erweiterungen-Symbol klicken (Ctrl+Shift+X)
3. Jede Erweiterung nach Namen suchen
4. Installieren klicken

### Methode 3: Kommandozeile
```bash
# Erforderliche Erweiterungen installieren
code --install-extension ms-vscode.cpptools-extension-pack
code --install-extension nvidia.nsight-vscode-edition
code --install-extension ms-vscode.cmake-tools
code --install-extension matepek.vscode-catch2-test-adapter

# Empfohlene Erweiterungen installieren
code --install-extension kriegalex.vscode-cuda
code --install-extension hars.cppsnippets
code --install-extension jeff-hykin.better-cpp-syntax
code --install-extension llvm-vs-code-extensions.vscode-clangd
code --install-extension llvm-vs-code-extensions.lldb-dap

# Optionale Erweiterungen installieren
code --install-extension usernamehw.errorlens
code --install-extension eamodio.gitlens
code --install-extension streetsidesoftware.code-spell-checker
```

## Debugging

### CUDA-Debugging in VS Code

**Hinweis:** CUDA-Debugging wird derzeit nur unter Linux unterstützt. Windows-Benutzer können CUDA-Code kompilieren und ausführen, können jedoch cuda-gdb nicht zum Debuggen verwenden.

#### Linux
1. Breakpoints in Ihrem CUDA-Code (.cu-Dateien) setzen
2. `F5` drücken oder zu Ausführen und Debuggen gehen
3. "CUDA C++: Launch (cuda-gdb)" Konfiguration auswählen
4. Der Debugger wird an Breakpoints sowohl im Host- als auch im Device-Code anhalten

### Verfügbare Debug-Konfigurationen

- **CUDA C++: Launch (cuda-gdb)**: CUDA-Code mit cuda-gdb debuggen (nur Linux)
- Verwendet CMakes aktuelle Target-Auswahl

## Konfigurationsdateien

### `.vscode/settings.json`
Konfiguriert CMake zur Verwendung von Ninja und Clang:
```json
{
    "cmake.generator": "Ninja",
    "cmake.configureArgs": [
        "-DCMAKE_C_COMPILER=clang",
        "-DCMAKE_CXX_COMPILER=clang++",
        "-DCMAKE_BUILD_TYPE=Debug",
        "-DCMAKE_EXPORT_COMPILE_COMMANDS=TRUE"
    ]
}
```

### `CMakePresets.json`
Definiert Build-Presets für verschiedene Konfigurationen:
- `default`: Debug-Build mit Clang und Ninja
- `release`: Release-Build mit Optimierungen

### `.vscode/launch.json`
Debug-Konfigurationen für CUDA-Anwendungen mit plattformspezifischen Debugger-Pfaden.

## Fehlerbehebung

### Umgebungsspezifische Konfiguration

Beim Ändern Ihrer Entwicklungsumgebung oder CUDA-Version, aktualisieren Sie die folgenden Pfade:

#### 1. debuggerPath in `.vscode/launch.json` aktualisieren (nur Linux)
Für Linux-Benutzer muss der Debugger-Pfad Ihrer CUDA-Installation entsprechen:
```json
"linux": {
    "debuggerPath": "/usr/bin/cuda-gdb"
    // Oder falls an einem anderen Ort installiert:
    // "debuggerPath": "/usr/local/cuda-13.0/bin/cuda-gdb"
}
```

**Windows-Hinweis:** CUDA-Debugging mit cuda-gdb wird unter Windows nicht unterstützt. Windows-Benutzer können CUDA-Anwendungen kompilieren und ausführen, müssen jedoch alternative Debugging-Methoden wie printf-Debugging oder NVIDIA Nsight Systems/Compute für Profiling verwenden.

#### 2. CUDA Toolkit-Pfad überprüfen
Stellen Sie sicher, dass Ihr System-PATH die korrekte CUDA-Version enthält:
- Windows: `C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.0\bin`
- Linux: `/usr/local/cuda-13.0/bin`

### CUDA-Architektur-Warnung
Wenn Sie "Cannot find valid GPU for '-arch=native'" sehen, bedeutet dies, dass CMake Ihre GPU-Architektur nicht erkennen kann. Sie können sie manuell in `CMakeLists.txt` angeben:
```cmake
set(CMAKE_CUDA_ARCHITECTURES "75")  # Für GTX 1660 Ti, RTX 2060-2080
set(CMAKE_CUDA_ARCHITECTURES "86")  # Für RTX 3060-3090
set(CMAKE_CUDA_ARCHITECTURES "89")  # Für RTX 4090
# Oder für Build ohne GPU (unterstützt mehrere Architekturen):
set(CMAKE_CUDA_ARCHITECTURES "75;80;86;89;90")
```

### Clang-Versionskompatibilität
CUDA unterstützt möglicherweise die neuesten Clang-Versionen nicht offiziell. Das Projekt verwendet das `-allow-unsupported-compiler`-Flag, um Versionsprüfungen zu umgehen. Falls Sie Probleme haben, verwenden Sie stattdessen GCC:
```bash
cmake -G Ninja -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++ ..
```

## Lizenz

Dieses Projekt ist unter der MIT-Lizenz lizenziert - siehe die [LICENSE](LICENSE)-Datei für Details.