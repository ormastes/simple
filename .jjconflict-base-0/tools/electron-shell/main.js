// Documented Electron shell entrypoint for Simple UI.
//
// The implementation lives in src/app/ui.electron so Simple-side tests and
// tooling use the same bridge code as the package entrypoint.

require('../../src/app/ui.electron/bridge.js');
