// Documented Electron shell entrypoint for Simple UI.
//
// The implementation lives in src/app/ui.electron so Simple-side tests and
// tooling use the same bridge code as the package entrypoint.

if (process.env.SIMPLE_ELECTRON_LIVE_BITMAP === '1') {
    require('../electron-live-bitmap/exact_fixture.js');
} else {
    require('../../src/app/ui.electron/bridge.js');
}
