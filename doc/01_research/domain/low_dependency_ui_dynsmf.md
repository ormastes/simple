# Low Dependency UI dynSMF Domain Research

Date: 2026-06-05

## Comparable Patterns

### Runtime Plugin Loading

Qt's `QPluginLoader` is the closest UI-framework comparison. It loads plugin
libraries at runtime, exposes metadata before full loading, and supports unload
only after every loader instance releases the same physical plugin. It also
documents deployment search paths and version/build-mode compatibility checks.
Sources:

- https://doc.qt.io/qt-6/qpluginloader.html
- https://doc.qt.io/qt-6/deployment-plugins.html

Implication for Simple:

- dynSMF libraries should carry cheap metadata for capability/version decisions.
- unload must be reference-counted or session-scoped, not a blind global drop.
- diagnostics should name the path, requested library, version/capability, and
  opt-out source.

### Dynamic UI Subtree Loading

Qt Quick `Loader` delays creation of a component until needed and unloads the
previous component by clearing the source or component. This maps well to GUI
widgets depending on HTML renderer components only when a widget actually needs
HTML.
Source:

- https://doc.qt.io/qt-6/qml-qtquick-loader.html

Implication for Simple:

- widget-level renderer dependencies should be explicit component capabilities.
- teardown must destroy component state before unloading the underlying dynSMF.

### Web Lazy Loading and Code Splitting

MDN and webpack describe splitting JavaScript, CSS, and HTML into chunks and
loading non-critical resources only when needed, commonly via dynamic imports.
Sources:

- https://developer.mozilla.org/en-US/docs/Web/Performance/Guides/Lazy_loading
- https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/import
- https://webpack.js.org/guides/lazy-loading/

Implication for Simple:

- HTML renderer and CSS implementation closures should be loaded at adapter or
  component boundaries, not by the base UI/TUI startup path.
- dependency tests should verify the negative case: the non-web path does not
  include the HTML/CSS closure.

### Widget-Scoped Styling

GTK 4 separates style providers from widgets and lets applications load CSS from
specific files/resources into a provider and attach it to a display/style
context. GTK also documents CSS nodes per widget.
Sources:

- https://docs.gtk.org/gtk4/class.CssProvider.html
- https://docs.gtk.org/gtk4/iface.StyleProvider.html
- https://gnome.pages.gitlab.gnome.org/gtk/gtk4/css-overview.html

Implication for Simple:

- CSS should be represented as a provider/capability consumed by components that
  use styling; global CSS implementation imports should be avoided in base GUI.
- CSS type contracts can stay common only if parsing/matching/application logic
  remains in a loadable implementation module.

### OS-Level Dynamic Loading

POSIX `dlclose()` tells the system that a previously `dlopen()` handle is no
longer needed; symbols are only valid while the handle remains live. Microsoft
documents the analogous `LoadLibrary`/`FreeLibrary` runtime linking flow.
Sources:

- https://pubs.opengroup.org/onlinepubs/9699919799.orig/functions/dlclose.html
- https://pubs.opengroup.org/onlinepubs/009604299/functions/dlsym.html
- https://learn.microsoft.com/en-us/windows/win32/dlls/using-run-time-dynamic-linking

Implication for Simple:

- dynSMF handles must have clear validity rules after unload.
- interpreter tests should assert symbol invalidation or a defined stale-handle
  error after unload, then successful reload with fresh state.

## Design Principles To Bring Back

- Capability metadata should be readable before heavy implementation load.
- Base UI contracts should be stable and small.
- Implementations should load at adapter/widget/session boundaries.
- Unload should be handle/session aware and should fail predictably if other
  live users still hold the library.
- Negative dependency tests are as important as positive render tests.
