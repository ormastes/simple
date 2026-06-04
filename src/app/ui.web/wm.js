// Window Manager for Simple Language Web UI — v2 (server-authoritative)
//
// The server is the sole authority over window state (position, z-order,
// focus, visibility). This client:
//   1. Authenticates via POST /ui/login → bearer token.
//   2. Opens WebSocket at /ui/ws?token=<token>.
//   3. Sends hello → open_session (or resume_session on reconnect).
//   4. Forwards raw input events to the server.
//   5. Applies server-sent snapshot / patch_batch via RetainedRenderer.
//
// Optimistic drag/resize: a separate .wm-ghost overlay is shown during drag.
// It is removed when the next patch_batch arrives or when the drag completes.
// The server's patch_batch is the ground truth; the ghost is cosmetic only.

// RetainedRenderer is loaded via dynamic import so this file can remain a
// classic script (html.spl does not set type="module"). If html.spl gains
// type="module", replace the dynamic import with a top-level import.

const PROTOCOL_VERSION = 1;
const RECONNECT_BASE_MS = 1000;
const RECONNECT_MAX_MS  = 16000;
const ACK_INTERVAL_MS   = 500;
const HOST_NATIVE_EVENT_SOURCE = 'native_event';
const NATIVE_SUPPRESSION_TTL_MS = 500;
const NATIVE_BURST_DEBOUNCE_MS = 80;
const WM_EXIT_ANIMATION_MS = 210;
const WM_SNAP_COMMIT_MS = 360;
const WM_MOTION_STORAGE_KEY = 'simple.wm.motion';
const WM_TRANSPARENCY_STORAGE_KEY = 'simple.wm.transparency';
const WM_WALLPAPER_STORAGE_KEY = 'simple.wm.wallpaper';
const WM_ACCENT_STORAGE_KEY = 'simple.wm.accent';
const WM_FOCUS_MODE_STORAGE_KEY = 'simple.wm.focus_mode';
const WM_CONTRAST_STORAGE_KEY = 'simple.wm.contrast';
const WM_FEEDBACK_STORAGE_KEY = 'simple.wm.feedback';
const WM_ENERGY_STORAGE_KEY = 'simple.wm.energy';
const WM_ANIMATION_STYLE_STORAGE_KEY = 'simple.wm.animation_style';
const WM_DOCK_MAGNIFICATION_STORAGE_KEY = 'simple.wm.dock_magnification';
const WM_DOCK_VISIBILITY_STORAGE_KEY = 'simple.wm.dock_visibility';
const WM_SURFACE_DEPTH_STORAGE_KEY = 'simple.wm.surface_depth';
const WM_TRAFFIC_SIDE_STORAGE_KEY = 'simple.wm.traffic_side';
const WM_ICON_MASK_STORAGE_KEY = 'simple.wm.icon_mask';
const WM_CORNER_RADIUS_STORAGE_KEY = 'simple.wm.corner_radius';
const WM_CHROME_VERBOSITY_STORAGE_KEY = 'simple.wm.chrome_verbosity';
const WM_WINDOW_TRANSITION_STORAGE_KEY = 'simple.wm.window_transition';
const WM_DENSITY_STORAGE_KEY = 'simple.wm.density';
const WM_BACKDROP_MOTION_STORAGE_KEY = 'simple.wm.backdrop_motion';
const WM_BACKDROP_INTENSITY_STORAGE_KEY = 'simple.wm.backdrop_intensity';
const WM_QUIET_MODE_STORAGE_KEY = 'simple.wm.quiet_mode';

class SimpleWindowManager {
  constructor(options = {}) {
    this.transport = options.transport || 'websocket';
    this.rendererModuleUrl = options.rendererModuleUrl || './retained_renderer.js';
    this.nativeHostWindows = !!options.nativeHostWindows;

    // DOM roots (populated from server state, not local decisions).
    this.desktop  = document.getElementById('wm-desktop');
    this.taskbar  = document.getElementById('wm-taskbar');

    // Renderer — set after dynamic import resolves.
    this.renderer = null;

    // WebSocket + session state.
    this.ws            = null;
    this.sessionId     = null;
    this.token         = null;
    this.reconnectDelay = RECONNECT_BASE_MS;
    this.reconnecting  = false;

    // Drag/resize ghost state.
    this.dragState     = null;  // { windowEl, startX, startY, origLeft, origTop, ghostEl, timer }
    this.resizeState   = null;  // { windowEl, startX, startY, origRect, ghostEl, timer, direction }

    // Periodic ack timer.
    this._ackTimer = null;
    this._nativeWindowEventSuppressions = new Map();
    this._nativeWindowBurstTimers = new Map();
    this._electronWindows = new Map();
    this._electronActiveWindowId = '';
    this._electronZCounter = 20;
    this._focusAcquiredTimers = new WeakMap();
    this._trafficCommandTimers = new WeakMap();
    this._titleCommandFeedbackTimers = new WeakMap();
    this._commandPalette = null;
    this._commandPaletteInput = null;
    this._commandPaletteList = null;
    this._commandPaletteItems = [];
    this._commandPaletteActiveIndex = 0;
    this._commandRecentFeedbackTimer = 0;
    this._snapPreview = null;
    this._snapLayoutPalette = null;
    this._windowArrangePalette = null;
    this._lastSnapZone = '';
    this._topMenuBar = null;
    this._topMenuFeedbackTimer = 0;
    this._topMenuFeedbackAction = '';
    this._desktopWidgets = null;
    this._desktopItems = null;
    this._desktopItemsFeedbackTimer = 0;
    this._windowOverview = null;
    this._overviewSearchQuery = '';
    this._stageRail = null;
    this._windowSwitcher = null;
    this._windowSwitcherItems = [];
    this._windowSwitcherActiveIndex = 0;
    this._windowSwitcherActivationTimer = 0;
    this._workspaceSwitcher = null;
    this._activeWorkspaceId = 'main';
    this._workspaceSwitcherActiveIndex = 0;
    this._customWorkspaces = null;
    this._workspaceSwitcherActivationTimer = 0;
    this._workspaceTransitionTimer = 0;
    this._clipboardHistory = null;
    this._clipboardHistoryActiveIndex = 0;
    this._clipboardSearchQuery = '';
    this._clipboardKindFilter = 'all';
    this._screenCaptureOverlay = null;
    this._screenCaptureMode = 'selection';
    this._screenCaptureFeedbackTimer = 0;
    this._quickSettings = null;
    this._quickSettingsActiveIndex = 0;
    this._quickSettingsFeedbackTimers = new Map();
    this._notificationCenter = null;
    this._notificationFilter = 'all';
    this._notificationCenterActiveIndex = 0;
    this._notificationActionFeedbackTimers = new Map();
    this._liveActivity = null;
    this._liveActivityPaused = false;
    this._liveActivityActionFeedbackTimer = 0;
    this._hotCorners = null;
    this._hotCornerHint = null;
    this._activeHotCorner = '';
    this._hotCornerFeedbackTimer = 0;
    this._desktopPeekActive = false;
    this._desktopPeekWindowIds = [];
    this._resizeHud = null;
    this._resizeHudTimer = 0;
    this._gestureHints = null;
    this._trackpadGestureAccum = { x: 0, y: 0, lastAt: 0 };
    this._trackpadGestureLastActionAt = 0;
    this._systemHud = null;
    this._systemHudTimer = 0;
    this._privacyIndicator = null;
    this._controlCenter = null;
    this._controlCenterFeedbackTimer = 0;
    this._widgetGallery = null;
    this._widgetGalleryActiveIndex = 0;
    this._wallpaperPicker = null;
    this._wallpaperPickerActiveIndex = 0;
    this._accentPalette = null;
    this._accentPaletteActiveIndex = 0;
    this._accentPaletteFeedbackTimer = 0;
    this._focusMode = 'off';
    this._contrastMode = 'comfortable';
    this._feedbackMode = 'standard';
    this._energyMode = 'standard';
    this._animationStyle = 'spring';
    this._dockMagnificationMode = 'standard';
    this._dockVisibilityMode = 'shown';
    this._surfaceDepthMode = 'layered';
    this._trafficSideMode = 'left';
    this._iconMaskMode = 'circle';
    this._cornerRadiusMode = 'round';
    this._chromeVerbosityMode = 'full';
    this._windowTransitionMode = 'mac';
    this._densityMode = 'comfortable';
    this._backdropMotionMode = 'ambient';
    this._backdropIntensityMode = 'balanced';
    this._quietMode = 'off';
    this._dockStack = null;
    this._dockStackMode = 'fan';
    this._dockStackActiveIndex = 0;
    this._stageRailActiveIndex = 0;
    this._qualityInspector = null;
    this._qualityFilter = 'all';
    this._selectedQualityCheck = 'color';
    this._qualityAuditMode = 'full';
    this._qualityContrastPolicyActiveIndex = 0;
    this._qualityAccentPolicyActiveIndex = 0;
    this._qualityDensityPolicyActiveIndex = 1;
    this._qualitySurfaceDepthPolicyActiveIndex = 0;
    this._qualityTrafficSidePolicyActiveIndex = 0;
    this._qualityWidgetStackPolicyActiveIndex = 0;
    this._qualityIconMaskPolicyActiveIndex = 0;
    this._qualityCornerRadiusPolicyActiveIndex = 0;
    this._qualityMaterialPolicyActiveIndex = 0;
    this._qualityDockMagnificationPolicyActiveIndex = 0;
    this._qualityDockVisibilityPolicyActiveIndex = 0;
    this._qualityBackdropPolicyActiveIndex = 0;
    this._qualityWallpaperPolicyActiveIndex = 0;
    this._qualityTitleCommandPolicyActiveIndex = 1;
    this._qualityWindowTransitionPolicyActiveIndex = 0;
    this._qualityAnimationStylePolicyActiveIndex = 0;
    this._qualityChromeVerbosityPolicyActiveIndex = 0;
    this._qualityFeedbackPolicyActiveIndex = 0;
    this._qualityEnergyPolicyActiveIndex = 0;
    this._taskbarPreview = null;
    this._taskbarPreviewHideTimer = 0;
    this._launchFeedbackTimers = new Map();
    this._widgetActionFeedbackTimers = new WeakMap();
    this._wmTooltip = null;
    this._wmTooltipAnchor = null;
    this._windowContextMenu = null;
    this._windowContextMenuWindowId = '';
    this._titleCommandSuggestionsPanel = null;
    this._titleCommandSuggestionItems = [];
    this._titleCommandSuggestionIndex = 0;
    this._titleCommandSuggestionFeedbackTimer = 0;
    this._desktopBackdropPointer = { x: 50, y: 50 };
    this._desktopBackdropPointerRaf = 0;
    this._appLauncher = null;
    this._appLauncherInput = null;
    this._appLauncherFilters = null;
    this._appLauncherGrid = null;
    this._appLauncherItems = [];
    this._appLauncherActiveIndex = 0;
    this._appLauncherCategory = 'all';
    this._launcherApps = [];
    this._shortcutOverlay = null;
    this._shortcutOverlayActiveIndex = 0;
    this._shortcutOverlayItemsCache = [];
    this._shortcutSearchQuery = '';
    this._shortcutOverlayFeedbackTimer = 0;
    this._quickSettingLevels = { audio: 42, brightness: 68 };

    this._applyMotionPreference(options.motion || '');
    this._applyTransparencyPreference(options.transparency || '');
    this._applyWallpaperPreference(options.wallpaper || '');
    this._applyAccentPreference(options.accent || '');
    this._applyFocusMode(options.focusMode || '');
    this._applyContrastPreference(options.contrast || '');
    this._applyFeedbackPreference(options.feedback || '');
    this._applyEnergyPreference(options.energy || '');
    this._applyAnimationStyle(options.animationStyle || '');
    this._applyDockMagnificationPreference(options.dockMagnification || '');
    this._applyDockVisibilityPreference(options.dockVisibility || '');
    this._applySurfaceDepthPreference(options.surfaceDepth || '');
    this._applyTrafficSidePreference(options.trafficSide || '');
    this._applyIconMaskPreference(options.iconMask || '');
    this._applyCornerRadiusPreference(options.cornerRadius || '');
    this._applyChromeVerbosityPreference(options.chromeVerbosity || '');
    this._applyWindowTransitionPreference(options.windowTransition || '');
    this._applyDensityPreference(options.density || '');
    this._applyBackdropMotionPreference(options.backdropMotion || '');
    this._applyBackdropIntensityPreference(options.backdropIntensity || '');
    this._applyQuietModePreference(options.quietMode || '');
    if (this.desktop) {
      this.desktop.dataset.wmWorkspace = this._activeWorkspaceId;
      this.desktop.dataset.wmWorkspaceTransition = 'idle';
      this.desktop.dataset.wmWorkspaceDirection = 'none';
    }
    window.simpleWmSetMotion = (preference) => this.setMotionPreference(preference);
    window.simpleWmSetTransparency = (preference) => this.setTransparencyPreference(preference);
    window.simpleWmSetWallpaper = (preference) => this.setWallpaperPreference(preference);
    window.simpleWmSetAccent = (preference) => this.setAccentPreference(preference);
    window.simpleWmSetFocusMode = (preference) => this.setFocusMode(preference);
    window.simpleWmSetContrast = (preference) => this.setContrastPreference(preference);
    window.simpleWmSetFeedback = (preference) => this.setFeedbackPreference(preference);
    window.simpleWmSetEnergy = (preference) => this.setEnergyPreference(preference);
    window.simpleWmSetAnimationStyle = (preference) => this.setAnimationStyle(preference);
    window.simpleWmSetDockMagnification = (preference) => this.setDockMagnificationPreference(preference);
    window.simpleWmSetDockVisibility = (preference) => this.setDockVisibilityPreference(preference);
    window.simpleWmSetSurfaceDepth = (preference) => this.setSurfaceDepthPreference(preference);
    window.simpleWmSetTrafficSide = (preference) => this.setTrafficSidePreference(preference);
    window.simpleWmSetIconMask = (preference) => this.setIconMaskPreference(preference);
    window.simpleWmSetCornerRadius = (preference) => this.setCornerRadiusPreference(preference);
    window.simpleWmSetChromeVerbosity = (preference) => this.setChromeVerbosityPreference(preference);
    window.simpleWmSetWindowTransition = (preference) => this.setWindowTransitionPreference(preference);
    window.simpleWmSetDensity = (preference) => this.setDensityPreference(preference);
    window.simpleWmSetBackdropMotion = (preference) => this.setBackdropMotionPreference(preference);
    window.simpleWmSetBackdropIntensity = (preference) => this.setBackdropIntensityPreference(preference);
    window.simpleWmSetQuietMode = (preference) => this.setQuietModePreference(preference);

    // Load renderer then begin auth.
    this._init();
  }

  // -------------------------------------------------------------------------
  // Initialisation
  // -------------------------------------------------------------------------

  async _init() {
    if (this.transport === 'electron-ipc') {
      this._bindGlobalEvents();
      if (window.simpleUI && window.simpleUI.onNativeWindowEvent) {
        window.simpleUI.onNativeWindowEvent((msg) => this._handleNativeWindowEvent(msg || {}));
      }
      this.sessionId = 'electron-ipc';
      if (window.simpleUI && typeof window.simpleUI.notifyWmReady === 'function') {
        window.simpleUI.notifyWmReady();
      }
      await this._loadRenderer(false);
      this._ensureDesktopWidgets();
      return;
    }
    await this._loadRenderer(this.transport !== 'electron-ipc');
    this._bindGlobalEvents();
    this._ensureDesktopWidgets();
    if (window.simpleUI && window.simpleUI.onNativeWindowEvent) {
      window.simpleUI.onNativeWindowEvent((msg) => this._handleNativeWindowEvent(msg || {}));
    }
    await this._authenticate();
  }

  async _loadRenderer(required) {
    try {
      const mod = await import(this.rendererModuleUrl);
      this.renderer = new mod.RetainedRenderer(this.desktop);
      return true;
    } catch (err) {
      if (required) {
        console.error('[WM] retained renderer load failed:', err);
      }
      this.renderer = null;
      return false;
    }
  }

  setMotionPreference(preference) {
    const motion = this._normalizeMotionPreference(preference);
    try {
      window.localStorage.setItem(WM_MOTION_STORAGE_KEY, motion);
    } catch (_) {
      // Storage can be unavailable in restricted webviews; the DOM attribute is enough.
    }
    const applied = this._applyMotionPreference(motion);
    this._showSystemHud('Motion', applied);
    return applied;
  }

  _applyMotionPreference(preference) {
    const motion = this._normalizeMotionPreference(preference || this._readMotionPreference());
    document.documentElement.dataset.wmMotion = motion;
    if (motion === 'off') this._resetDesktopBackdropPointer();
    return motion;
  }

  _readMotionPreference() {
    try {
      return window.localStorage.getItem(WM_MOTION_STORAGE_KEY) || '';
    } catch (_) {
      return '';
    }
  }

  _normalizeMotionPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'off' || value === 'reduced' || value === 'standard') return value;
    return 'standard';
  }

  setTransparencyPreference(preference) {
    const transparency = this._normalizeTransparencyPreference(preference);
    try {
      window.localStorage.setItem(WM_TRANSPARENCY_STORAGE_KEY, transparency);
    } catch (_) {
      // Storage can be unavailable in restricted webviews; the DOM attribute is enough.
    }
    const applied = this._applyTransparencyPreference(transparency);
    this._showSystemHud('Material', applied);
    return applied;
  }

  _applyTransparencyPreference(preference) {
    const transparency = this._normalizeTransparencyPreference(preference || this._readTransparencyPreference());
    document.documentElement.dataset.wmTransparency = transparency;
    return transparency;
  }

  _readTransparencyPreference() {
    try {
      return window.localStorage.getItem(WM_TRANSPARENCY_STORAGE_KEY) || '';
    } catch (_) {
      return '';
    }
  }

  _normalizeTransparencyPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'off' || value === 'reduced' || value === 'standard') return value;
    return 'standard';
  }

  setWallpaperPreference(preference) {
    const wallpaper = this._normalizeWallpaperPreference(preference);
    try {
      window.localStorage.setItem(WM_WALLPAPER_STORAGE_KEY, wallpaper);
    } catch (_) {
      // Storage can be unavailable in restricted webviews; the DOM attribute is enough.
    }
    const applied = this._applyWallpaperPreference(wallpaper);
    this._showSystemHud('Wallpaper', applied);
    return applied;
  }

  _applyWallpaperPreference(preference) {
    const wallpaper = this._normalizeWallpaperPreference(preference || this._readWallpaperPreference());
    document.documentElement.dataset.wmWallpaper = wallpaper;
    return wallpaper;
  }

  _readWallpaperPreference() {
    try {
      return window.localStorage.getItem(WM_WALLPAPER_STORAGE_KEY) || '';
    } catch (_) {
      return '';
    }
  }

  _normalizeWallpaperPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'aurora' || value === 'mesh' || value === 'solid') return value;
    return 'aurora';
  }

  setAccentPreference(preference) {
    const accent = this._normalizeAccentPreference(preference);
    try {
      window.localStorage.setItem(WM_ACCENT_STORAGE_KEY, accent.id);
    } catch (_) {
      // Storage can be unavailable in restricted webviews; the DOM variables are enough.
    }
    const applied = this._applyAccentPreference(accent.id);
    this._showSystemHud('Accent', applied.label);
    return applied.id;
  }

  _applyAccentPreference(preference) {
    const accent = this._normalizeAccentPreference(preference || this._readAccentPreference());
    document.documentElement.dataset.wmAccent = accent.id;
    document.documentElement.style.setProperty('--ui-accent', accent.color);
    document.documentElement.style.setProperty('--ui-accent-rgb', accent.rgb);
    return accent;
  }

  _readAccentPreference() {
    try {
      return window.localStorage.getItem(WM_ACCENT_STORAGE_KEY) || '';
    } catch (_) {
      return '';
    }
  }

  _normalizeAccentPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    return this._accentChoices().find((choice) => choice.id === value) || this._accentChoices()[0];
  }

  setFocusMode(preference) {
    const mode = this._normalizeFocusMode(preference);
    try {
      window.localStorage.setItem(WM_FOCUS_MODE_STORAGE_KEY, mode);
    } catch (_) {
      // Storage can be unavailable in restricted webviews; the DOM mode still applies.
    }
    const applied = this._applyFocusMode(mode);
    this._showSystemHud('Focus', this._focusModeLabel(applied), 1800);
    if (this._topMenuBar) this._renderTopMenuBar();
    if (this._quickSettings && !this._quickSettings.hidden) this._renderQuickSettings();
    if (this._notificationCenter && !this._notificationCenter.hidden) this._renderNotificationCenter();
    if (this._controlCenter && !this._controlCenter.hidden) this._renderControlCenter();
    return applied;
  }

  _applyFocusMode(preference) {
    const mode = this._normalizeFocusMode(preference || this._readFocusMode());
    this._focusMode = mode;
    document.documentElement.dataset.wmFocusMode = mode;
    return mode;
  }

  _readFocusMode() {
    try {
      return window.localStorage.getItem(WM_FOCUS_MODE_STORAGE_KEY) || '';
    } catch (_) {
      return '';
    }
  }

  _normalizeFocusMode(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'work' || value === 'deep' || value === 'off') return value;
    return 'off';
  }

  _focusModeLabel(mode = this._focusMode) {
    if (mode === 'work') return 'Work focus';
    if (mode === 'deep') return 'Deep focus';
    return 'Focus off';
  }

  setContrastPreference(preference) {
    const mode = this._normalizeContrastPreference(preference);
    this._writePreference(WM_CONTRAST_STORAGE_KEY, mode);
    const applied = this._applyContrastPreference(mode);
    this._showSystemHud('Readability', this._contrastLabel(applied), 1600);
    return applied;
  }

  _applyContrastPreference(preference) {
    const mode = this._normalizeContrastPreference(preference || this._readContrastPreference());
    this._contrastMode = mode;
    document.documentElement.dataset.wmContrast = mode;
    return mode;
  }

  _readContrastPreference() {
    return this._readPreference(WM_CONTRAST_STORAGE_KEY);
  }

  _normalizeContrastPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'high' || value === 'comfortable') return value;
    return 'comfortable';
  }

  _contrastLabel(mode = this._contrastMode) {
    if (mode === 'high') return 'High contrast';
    return 'Comfortable contrast';
  }

  setFeedbackPreference(preference) {
    const mode = this._normalizeFeedbackPreference(preference);
    this._writePreference(WM_FEEDBACK_STORAGE_KEY, mode);
    const applied = this._applyFeedbackPreference(mode);
    if (applied !== 'off') this._showSystemHud('Feedback', this._feedbackLabel(applied), 1500);
    return applied;
  }

  _applyFeedbackPreference(preference) {
    const mode = this._normalizeFeedbackPreference(preference || this._readFeedbackPreference());
    this._feedbackMode = mode;
    document.documentElement.dataset.wmFeedback = mode;
    return mode;
  }

  _readFeedbackPreference() {
    return this._readPreference(WM_FEEDBACK_STORAGE_KEY);
  }

  _normalizeFeedbackPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'subtle' || value === 'off' || value === 'standard') return value;
    return 'standard';
  }

  _feedbackLabel(mode = this._feedbackMode) {
    if (mode === 'subtle') return 'Subtle feedback';
    if (mode === 'off') return 'Feedback off';
    return 'Standard feedback';
  }

  _feedbackAllows(level = 'standard') {
    if (this._feedbackMode === 'off') return level === 'critical';
    if (this._feedbackMode === 'subtle') return level !== 'verbose';
    return true;
  }

  setEnergyPreference(preference) {
    const mode = this._normalizeEnergyPreference(preference);
    this._writePreference(WM_ENERGY_STORAGE_KEY, mode);
    const applied = this._applyEnergyPreference(mode);
    this._showSystemHud('Energy policy', this._energyLabel(applied), 1500);
    return applied;
  }

  _applyEnergyPreference(preference) {
    const mode = this._normalizeEnergyPreference(preference || this._readEnergyPreference());
    this._energyMode = mode;
    document.documentElement.dataset.wmEnergy = mode;
    if (mode === 'critical') this._resetDesktopBackdropPointer();
    return mode;
  }

  _readEnergyPreference() {
    return this._readPreference(WM_ENERGY_STORAGE_KEY);
  }

  _normalizeEnergyPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'low' || value === 'low-power' || value === 'low_power') return 'low';
    if (value === 'critical' || value === 'critical-saver' || value === 'critical_saver') return 'critical';
    if (value === 'standard') return value;
    return 'standard';
  }

  _energyLabel(mode = this._energyMode) {
    if (mode === 'low') return 'Low power';
    if (mode === 'critical') return 'Critical saver';
    return 'Standard energy';
  }

  setAnimationStyle(preference) {
    const mode = this._normalizeAnimationStyle(preference);
    this._writePreference(WM_ANIMATION_STYLE_STORAGE_KEY, mode);
    const applied = this._applyAnimationStyle(mode);
    this._showSystemHud('Animation', applied);
    return applied;
  }

  _applyAnimationStyle(preference) {
    const mode = this._normalizeAnimationStyle(preference || this._readAnimationStyle());
    this._animationStyle = mode;
    document.documentElement.dataset.wmAnimationStyle = mode;
    return mode;
  }

  _readAnimationStyle() {
    return this._readPreference(WM_ANIMATION_STYLE_STORAGE_KEY);
  }

  _normalizeAnimationStyle(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'calm' || value === 'snappy' || value === 'spring') return value;
    return 'spring';
  }

  setDockMagnificationPreference(preference) {
    const mode = this._normalizeDockMagnificationPreference(preference);
    this._writePreference(WM_DOCK_MAGNIFICATION_STORAGE_KEY, mode);
    const applied = this._applyDockMagnificationPreference(mode);
    this._showSystemHud('Dock', this._dockMagnificationLabel(applied));
    return applied;
  }

  _applyDockMagnificationPreference(preference) {
    const mode = this._normalizeDockMagnificationPreference(preference || this._readDockMagnificationPreference());
    this._dockMagnificationMode = mode;
    document.documentElement.dataset.wmDockMagnification = mode;
    return mode;
  }

  _readDockMagnificationPreference() {
    return this._readPreference(WM_DOCK_MAGNIFICATION_STORAGE_KEY);
  }

  _normalizeDockMagnificationPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'subtle' || value === 'off' || value === 'standard') return value;
    return 'standard';
  }

  _dockMagnificationLabel(mode = this._dockMagnificationMode) {
    if (mode === 'subtle') return 'Subtle dock';
    if (mode === 'off') return 'Dock magnification off';
    return 'Standard dock';
  }

  setDockVisibilityPreference(preference) {
    const mode = this._normalizeDockVisibilityPreference(preference);
    this._writePreference(WM_DOCK_VISIBILITY_STORAGE_KEY, mode);
    const applied = this._applyDockVisibilityPreference(mode);
    this._showSystemHud('Dock visibility', this._dockVisibilityLabel(applied));
    return applied;
  }

  _applyDockVisibilityPreference(preference) {
    const mode = this._normalizeDockVisibilityPreference(preference || this._readDockVisibilityPreference());
    this._dockVisibilityMode = mode;
    document.documentElement.dataset.wmDockVisibility = mode;
    return mode;
  }

  _readDockVisibilityPreference() {
    return this._readPreference(WM_DOCK_VISIBILITY_STORAGE_KEY);
  }

  _normalizeDockVisibilityPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'auto' || value === 'hidden' || value === 'shown') return value;
    return 'shown';
  }

  _dockVisibilityLabel(mode = this._dockVisibilityMode) {
    if (mode === 'auto') return 'Auto-hide';
    if (mode === 'hidden') return 'Hidden';
    return 'Shown';
  }

  setSurfaceDepthPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'layered', 'subtle', 'flat');
    this._writePreference(WM_SURFACE_DEPTH_STORAGE_KEY, mode);
    this._surfaceDepthMode = mode;
    document.documentElement.dataset.wmSurfaceDepth = mode;
    this._showSystemHud('Surface depth', mode);
    return mode;
  }

  _applySurfaceDepthPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readSurfaceDepthPreference(), 'layered', 'subtle', 'flat');
    this._surfaceDepthMode = mode;
    document.documentElement.dataset.wmSurfaceDepth = mode;
    return mode;
  }

  _readSurfaceDepthPreference() {
    return this._readPreference(WM_SURFACE_DEPTH_STORAGE_KEY);
  }

  setTrafficSidePreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'left', 'right', 'left');
    this._writePreference(WM_TRAFFIC_SIDE_STORAGE_KEY, mode);
    this._trafficSideMode = mode;
    document.documentElement.dataset.wmTrafficSide = mode;
    this._showSystemHud('Traffic controls', mode);
    return mode;
  }

  _applyTrafficSidePreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readTrafficSidePreference(), 'left', 'right', 'left');
    this._trafficSideMode = mode;
    document.documentElement.dataset.wmTrafficSide = mode;
    return mode;
  }

  _readTrafficSidePreference() {
    return this._readPreference(WM_TRAFFIC_SIDE_STORAGE_KEY);
  }

  setIconMaskPreference(preference) {
    const mode = this._normalizeIconMaskPreference(preference);
    this._writePreference(WM_ICON_MASK_STORAGE_KEY, mode);
    this._iconMaskMode = mode;
    document.documentElement.dataset.wmIconMask = mode;
    this._showSystemHud('Icon mask', mode);
    return mode;
  }

  _applyIconMaskPreference(preference) {
    const mode = this._normalizeIconMaskPreference(preference || this._readIconMaskPreference());
    this._iconMaskMode = mode;
    document.documentElement.dataset.wmIconMask = mode;
    return mode;
  }

  _readIconMaskPreference() {
    return this._readPreference(WM_ICON_MASK_STORAGE_KEY);
  }

  _normalizeIconMaskPreference(preference) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === 'circle' || value === 'rounded' || value === 'square') return value;
    return 'circle';
  }

  setCornerRadiusPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'round', 'soft', 'square');
    this._writePreference(WM_CORNER_RADIUS_STORAGE_KEY, mode);
    const applied = this._applyCornerRadiusPreference(mode);
    this._showSystemHud('Corner radius', applied);
    return applied;
  }

  _applyCornerRadiusPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readCornerRadiusPreference(), 'round', 'soft', 'square');
    this._cornerRadiusMode = mode;
    document.documentElement.dataset.wmCornerRadius = mode;
    return mode;
  }

  _readCornerRadiusPreference() {
    return this._readPreference(WM_CORNER_RADIUS_STORAGE_KEY);
  }

  setChromeVerbosityPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'full', 'compact', 'minimal');
    this._writePreference(WM_CHROME_VERBOSITY_STORAGE_KEY, mode);
    this._chromeVerbosityMode = mode;
    document.documentElement.dataset.wmChromeVerbosity = mode;
    this._showSystemHud('Chrome verbosity', mode);
    return mode;
  }

  _applyChromeVerbosityPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readChromeVerbosityPreference(), 'full', 'compact', 'minimal');
    this._chromeVerbosityMode = mode;
    document.documentElement.dataset.wmChromeVerbosity = mode;
    return mode;
  }

  _readChromeVerbosityPreference() {
    return this._readPreference(WM_CHROME_VERBOSITY_STORAGE_KEY);
  }

  setWindowTransitionPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'mac', 'fade', 'none');
    this._writePreference(WM_WINDOW_TRANSITION_STORAGE_KEY, mode);
    this._windowTransitionMode = mode;
    document.documentElement.dataset.wmWindowTransition = mode;
    this._showSystemHud('Window motion', mode);
    return mode;
  }

  _applyWindowTransitionPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readWindowTransitionPreference(), 'mac', 'fade', 'none');
    this._windowTransitionMode = mode;
    document.documentElement.dataset.wmWindowTransition = mode;
    return mode;
  }

  _readWindowTransitionPreference() {
    return this._readPreference(WM_WINDOW_TRANSITION_STORAGE_KEY);
  }

  setDensityPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'comfortable', 'compact', 'spacious');
    this._writePreference(WM_DENSITY_STORAGE_KEY, mode);
    this._densityMode = mode;
    document.documentElement.dataset.wmDensity = mode;
    this._showSystemHud('Layout density', mode);
    return mode;
  }

  _applyDensityPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readDensityPreference(), 'comfortable', 'compact', 'spacious');
    this._densityMode = mode;
    document.documentElement.dataset.wmDensity = mode;
    return mode;
  }

  _readDensityPreference() {
    return this._readPreference(WM_DENSITY_STORAGE_KEY);
  }

  setBackdropMotionPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'ambient', 'subtle', 'static');
    this._writePreference(WM_BACKDROP_MOTION_STORAGE_KEY, mode);
    this._backdropMotionMode = mode;
    document.documentElement.dataset.wmBackdropMotion = mode;
    if (mode === 'static') this._resetDesktopBackdropPointer();
    this._showSystemHud('Backdrop motion', mode);
    return mode;
  }

  _applyBackdropMotionPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readBackdropMotionPreference(), 'ambient', 'subtle', 'static');
    this._backdropMotionMode = mode;
    document.documentElement.dataset.wmBackdropMotion = mode;
    if (mode === 'static') this._resetDesktopBackdropPointer();
    return mode;
  }

  _readBackdropMotionPreference() {
    return this._readPreference(WM_BACKDROP_MOTION_STORAGE_KEY);
  }

  setBackdropIntensityPreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'balanced', 'vivid', 'quiet');
    this._writePreference(WM_BACKDROP_INTENSITY_STORAGE_KEY, mode);
    this._backdropIntensityMode = mode;
    document.documentElement.dataset.wmBackdropIntensity = mode;
    if (mode === 'quiet') this._resetDesktopBackdropPointer();
    this._showSystemHud('Backdrop intensity', this._backdropIntensityLabel(mode));
    return mode;
  }

  _applyBackdropIntensityPreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readBackdropIntensityPreference(), 'balanced', 'vivid', 'quiet');
    this._backdropIntensityMode = mode;
    document.documentElement.dataset.wmBackdropIntensity = mode;
    if (mode === 'quiet') this._resetDesktopBackdropPointer();
    return mode;
  }

  _readBackdropIntensityPreference() {
    return this._readPreference(WM_BACKDROP_INTENSITY_STORAGE_KEY);
  }

  _backdropIntensityLabel(mode) {
    if (mode === 'vivid') return 'Vivid backdrop';
    if (mode === 'quiet') return 'Quiet backdrop';
    return 'Balanced backdrop';
  }

  setQuietModePreference(preference) {
    const mode = this._normalizeThreeMode(preference, 'off', 'on', 'off');
    this._writePreference(WM_QUIET_MODE_STORAGE_KEY, mode);
    const applied = this._applyQuietModePreference(mode);
    this._showSystemHud('Quiet mode', applied === 'on' ? 'on' : 'off');
    return applied;
  }

  _applyQuietModePreference(preference) {
    const mode = this._normalizeThreeMode(preference || this._readQuietModePreference(), 'off', 'on', 'off');
    this._quietMode = mode;
    document.documentElement.dataset.wmQuietMode = mode;
    if (mode === 'on') this._resetDesktopBackdropPointer();
    return mode;
  }

  _readQuietModePreference() {
    return this._readPreference(WM_QUIET_MODE_STORAGE_KEY);
  }

  _normalizeThreeMode(preference, first, second, third) {
    const value = String(preference || '').trim().toLowerCase();
    if (value === first || value === second || value === third) return value;
    return first;
  }

  _writePreference(key, value) {
    try {
      window.localStorage.setItem(key, value);
    } catch (_) {
      // Storage can be unavailable in restricted webviews; the DOM mode still applies.
    }
  }

  _readPreference(key) {
    try {
      return window.localStorage.getItem(key) || '';
    } catch (_) {
      return '';
    }
  }

  _desktopBackdropPointerEnabled() {
    const root = document.documentElement.dataset;
    return this.desktop &&
      root.wmMotion !== 'off' &&
      root.wmBackdropMotion !== 'static' &&
      root.wmBackdropIntensity !== 'quiet' &&
      root.wmQuietMode !== 'on' &&
      root.wmEnergy !== 'critical';
  }

  _updateDesktopBackdropPointer(event) {
    if (!this._desktopBackdropPointerEnabled()) return false;
    const rect = this.desktop.getBoundingClientRect();
    if (!rect.width || !rect.height) return false;
    const x = Math.max(0, Math.min(100, ((event.clientX - rect.left) / rect.width) * 100));
    const y = Math.max(0, Math.min(100, ((event.clientY - rect.top) / rect.height) * 100));
    this._desktopBackdropPointer = { x, y };
    if (this._desktopBackdropPointerRaf) return true;
    this._desktopBackdropPointerRaf = window.requestAnimationFrame(() => {
      this._desktopBackdropPointerRaf = 0;
      const current = this._desktopBackdropPointer || { x: 50, y: 50 };
      document.documentElement.style.setProperty('--ui-backdrop-pointer-x', current.x.toFixed(1) + '%');
      document.documentElement.style.setProperty('--ui-backdrop-pointer-y', current.y.toFixed(1) + '%');
    });
    return true;
  }

  _resetDesktopBackdropPointer() {
    this._desktopBackdropPointer = { x: 50, y: 50 };
    if (this._desktopBackdropPointerRaf) {
      window.cancelAnimationFrame(this._desktopBackdropPointerRaf);
      this._desktopBackdropPointerRaf = 0;
    }
    document.documentElement.style.setProperty('--ui-backdrop-pointer-x', '50%');
    document.documentElement.style.setProperty('--ui-backdrop-pointer-y', '50%');
    return true;
  }

  _toggleFocusMode() {
    return this.setFocusMode(this._focusMode === 'off' ? 'work' : 'off');
  }

  async _authenticate() {
    try {
      const resp = await fetch('/ui/login', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ capability_grant: 'dev' })
      });
      if (!resp.ok) throw new Error('login failed: ' + resp.status);
      const data = await resp.json();
      this.token = data.token;
      this._connect();
    } catch (err) {
      console.error('[WM] auth error:', err);
      setTimeout(() => this._authenticate(), this.reconnectDelay);
    }
  }

  // -------------------------------------------------------------------------
  // WebSocket connection
  // -------------------------------------------------------------------------

  _connect() {
    const proto = location.protocol === 'https:' ? 'wss' : 'ws';
    const url   = `${proto}://${location.host}/ui/ws?token=${encodeURIComponent(this.token)}`;
    this.ws = new WebSocket(url);

    this.ws.onopen = () => {
      this.reconnectDelay = RECONNECT_BASE_MS;
      this.reconnecting   = false;
      this._send({ t: 'hello', v: PROTOCOL_VERSION, s: null,
                   payload: { protocol_version: PROTOCOL_VERSION, client_caps: 0 } });
    };

    this.ws.onmessage = (e) => {
      let frame;
      try { frame = JSON.parse(e.data); } catch { return; }
      this._dispatch(frame);
    };

    this.ws.onclose = (e) => {
      this._stopAckTimer();
      if (e.code === 1002) {
        // Protocol mismatch — do not retry without software upgrade.
        console.error('[WM] protocol version mismatch — cannot reconnect');
        return;
      }
      this._scheduleReconnect();
    };

    this.ws.onerror = () => {
      this.ws.close();
    };
  }

  _scheduleReconnect() {
    if (this.reconnecting) return;
    this.reconnecting = true;
    setTimeout(() => {
      this.reconnecting = false;
      this._reconnect();
    }, this.reconnectDelay);
    this.reconnectDelay = Math.min(this.reconnectDelay * 2, RECONNECT_MAX_MS);
  }

  _reconnect() {
    // Send resume_session after reconnect so server can diff-patch instead of
    // sending a full snapshot whenever possible (§8 of the protocol doc).
    const rev = this.renderer ? this.renderer.snapshotRevision : 0;
    const seq = this.renderer ? this.renderer.lastSequence : -1;

    const proto = location.protocol === 'https:' ? 'wss' : 'ws';
    const url   = `${proto}://${location.host}/ui/ws?token=${encodeURIComponent(this.token)}`;
    this.ws = new WebSocket(url);

    this.ws.onopen = () => {
      this.reconnectDelay = RECONNECT_BASE_MS;
      this.reconnecting   = false;
      // hello first, then resume.
      this._send({ t: 'hello', v: PROTOCOL_VERSION, s: null,
                   payload: { protocol_version: PROTOCOL_VERSION, client_caps: 0 } });
      // After capabilities response we send resume_session — handled in _dispatch.
      // Store resume params so _dispatch can use them.
      this._pendingResume = { session_id: this.sessionId, snapshot_revision: rev, last_sequence: seq };
    };

    this.ws.onmessage = (e) => {
      let frame;
      try { frame = JSON.parse(e.data); } catch { return; }
      this._dispatch(frame);
    };

    this.ws.onclose = (e) => {
      this._stopAckTimer();
      if (e.code === 1002) {
        console.error('[WM] protocol version mismatch — cannot reconnect');
        return;
      }
      this._scheduleReconnect();
    };

    this.ws.onerror = () => { this.ws.close(); };
  }

  // -------------------------------------------------------------------------
  // Frame dispatch (S→C)
  // -------------------------------------------------------------------------

  _dispatch(frame) {
    // Update session id from any server frame that carries one.
    if (frame.s && !this.sessionId) {
      this.sessionId = frame.s;
    }

    switch (frame.t) {
      case 'capabilities':
        // Server has greeted us. Send open_session or resume_session.
        if (this._pendingResume) {
          this._send({
            t: 'resume_session', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
            payload: this._pendingResume
          });
          this._pendingResume = null;
        } else {
          const vp = { x: 0, y: 0, w: window.innerWidth, h: window.innerHeight };
          this._send({
            t: 'open_session', v: PROTOCOL_VERSION, s: null, seq: null,
            payload: { viewport: vp }
          });
        }
        this._startAckTimer();
        break;

      case 'snapshot':
        if (!this.renderer) break;
        this.sessionId = frame.s ?? this.sessionId;
        this.renderer.applySnapshot(this._unwrapSnapshotPayload(frame.payload));
        this._cancelGhost();
        this._renderTopMenuBar();
        break;

      case 'patch_batch':
        if (!this.renderer) break;
        this.renderer.applyPatchBatch(this._unwrapPatchPayload(frame.payload));
        this._cancelGhost();
        this._renderTopMenuBar();
        break;

      case 'taskbar_model':
        this.renderTaskbarModel(frame.payload || {});
        this._renderTopMenuBar();
        break;

      case 'host_window_command':
        this._handleHostWindowCommand(frame.payload || {});
        break;

      case 'focus_changed':
        if (!this.renderer) break;
        this.renderer.setFocus(
          frame.payload.surface_id,
          frame.payload.widget_id
        );
        break;

      case 'ping':
        this._send({ t: 'pong', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
                     payload: { nonce: frame.payload.nonce } });
        break;

      case 'error':
        console.error('[WM] server error:', frame.payload.code, frame.payload.message);
        this._showToast(frame.payload.message);
        if (frame.payload.retry_after_ms > 0) {
          this.reconnectDelay = frame.payload.retry_after_ms;
        }
        break;

      default:
        // Unknown message type — ignore silently.
        break;
    }
  }

  _unwrapSnapshotPayload(payload) {
    if (payload && payload.type === 'snapshot' && payload.snapshot) {
      return payload.snapshot;
    }
    return payload;
  }

  _unwrapPatchPayload(payload) {
    if (payload && payload.type === 'patch' && payload.patches) {
      if (Array.isArray(payload.patches)) {
        return {
          snapshot_revision: payload.revision ?? this.renderer?.snapshotRevision ?? 0,
          from_sequence: payload.from_sequence,
          to_sequence: payload.to_sequence,
          patches: payload.patches
        };
      }
      return payload.patches;
    }
    return payload;
  }

  // -------------------------------------------------------------------------
  // Sending (C→S)
  // -------------------------------------------------------------------------

  _send(frame) {
    if (this.transport === 'electron-ipc') {
      if (window.simpleUI && typeof window.simpleUI.sendFrame === 'function') {
        window.simpleUI.sendFrame(frame);
      }
      return;
    }
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify(frame));
    }
  }

  _sendInputEvent(surfaceId, widgetId, event) {
    this._send({
      t: 'input_event', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
      payload: { surface_id: surfaceId, widget_id: widgetId, event }
    });
  }

  _sendWindowCmd(kind, extra) {
    this._send({
      t: 'window_cmd', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
      payload: { cmd_type: kind, kind, ...extra }
    });
  }

  _sendHostWmPointer(e, kind = 'down') {
    const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0, width: window.innerWidth, height: window.innerHeight };
    const button = e.button === 2 ? 'right' : (e.button === 1 ? 'middle' : 'left');
    this._send({
      t: 'host_wm_pointer', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
      payload: {
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top),
        width: Math.round(r.width || window.innerWidth || 1280),
        height: Math.round(r.height || window.innerHeight || 720),
        button,
        kind
      }
    });
  }

  _sendLaunch(appId, sourceEl = null) {
    this._markLaunchFeedback(appId, sourceEl);
    this._sendWindowCmd('launch', { app_id: appId });
  }

  _markLaunchFeedback(appId, sourceEl = null) {
    const id = String(appId || '').trim();
    if (!id) return;
    this._clearLaunchFeedback(id);
    const selector = `[data-app-id="${CSS.escape(id)}"]`;
    const targets = new Set(Array.from(document.querySelectorAll(selector)));
    if (sourceEl instanceof Element) targets.add(sourceEl);
    targets.forEach((el) => {
      el.classList.add('launching');
      el.dataset.launchFeedback = 'active';
      el.setAttribute('aria-busy', 'true');
    });
    const timer = window.setTimeout(() => this._clearLaunchFeedback(id), 760);
    this._launchFeedbackTimers.set(id, timer);
  }

  _clearLaunchFeedback(appId) {
    const id = String(appId || '').trim();
    if (!id) return;
    const timer = this._launchFeedbackTimers.get(id);
    if (timer) window.clearTimeout(timer);
    this._launchFeedbackTimers.delete(id);
    const selector = `[data-app-id="${CSS.escape(id)}"]`;
    document.querySelectorAll(selector).forEach((el) => {
      el.classList.remove('launching');
      delete el.dataset.launchFeedback;
      el.removeAttribute('aria-busy');
    });
  }

  _ensureTopMenuBar() {
    if (this._topMenuBar && this._topMenuBar.isConnected) return this._topMenuBar;
    const bar = document.createElement('header');
    bar.className = 'wm-top-menu-bar';
    bar.setAttribute('role', 'menubar');
    bar.setAttribute('aria-label', 'Simple desktop menu bar');
    bar.addEventListener('click', (event) => {
      const target = event.target && event.target.closest ? event.target : null;
      const item = target ? target.closest('[data-menu-action]') : null;
      if (!item || !bar.contains(item)) return;
      const action = item.dataset.menuAction || '';
      this._activateTopMenuAction(action);
      this._renderTopMenuBar();
      this._markTopMenuFeedback(action);
    });
    document.body.appendChild(bar);
    this._topMenuBar = bar;
    this._renderTopMenuBar();
    return bar;
  }

  _renderTopMenuBar() {
    const bar = this._topMenuBar && this._topMenuBar.isConnected ? this._topMenuBar : null;
    if (!bar) return;
    bar.innerHTML = '';
    const left = document.createElement('nav');
    left.className = 'wm-top-menu-left';
    left.setAttribute('aria-label', 'Application menu');
    left.appendChild(this._makeTopMenuButton('Simple', 'launcher', true));
    left.appendChild(this._makeTopMenuButton(this._activeWindowTitle(), 'command_palette', false));
    left.appendChild(this._makeTopMenuButton('Widgets', 'widgets', false));
    bar.appendChild(left);

    const right = document.createElement('nav');
    right.className = 'wm-top-menu-right';
    right.setAttribute('aria-label', 'System menu');
    right.appendChild(this._makeTopMenuButton('Wi-Fi', 'quick_settings', false));
    right.appendChild(this._makeTopMenuButton('Battery 96%', 'quick_settings', false));
    right.appendChild(this._makeTopMenuButton(this._focusModeLabel(), 'focus_mode', false));
    right.appendChild(this._makeTopMenuButton('Notifications', 'notifications', false));
    right.appendChild(this._makeTopMenuButton(this._topMenuTimeLabel(), 'control_center', false));
    bar.appendChild(right);
  }

  _makeTopMenuButton(label, action, primary) {
    const button = document.createElement('button');
    button.type = 'button';
    const feedback = action && action === this._topMenuFeedbackAction;
    button.className = 'wm-top-menu-item' + (primary ? ' primary' : '') + (feedback ? ' action-feedback' : '');
    button.dataset.menuAction = action;
    if (feedback) button.dataset.menuFeedback = 'activate';
    button.setAttribute('role', 'menuitem');
    button.textContent = label;
    return button;
  }

  _markTopMenuFeedback(action) {
    if (!this._topMenuBar || !this._topMenuBar.isConnected || !this._feedbackAllows('standard')) return;
    const value = String(action || '').trim();
    if (!value) return;
    window.clearTimeout(this._topMenuFeedbackTimer);
    this._topMenuFeedbackAction = value;
    this._topMenuBar.dataset.menuFeedback = 'activate';
    this._topMenuBar.dataset.menuFeedbackAction = value;
    this._topMenuBar.classList.add('action-feedback');
    const safeValue = typeof CSS !== 'undefined' && CSS.escape ? CSS.escape(value) : value.replace(/["\\]/g, '\\$&');
    const selector = `.wm-top-menu-item[data-menu-action="${safeValue}"]`;
    this._topMenuBar.querySelectorAll(selector).forEach((item) => {
      item.dataset.menuFeedback = 'activate';
      item.classList.add('action-feedback');
    });
    this._topMenuFeedbackTimer = window.setTimeout(() => this._clearTopMenuFeedback(), 560);
  }

  _clearTopMenuFeedback() {
    window.clearTimeout(this._topMenuFeedbackTimer);
    this._topMenuFeedbackTimer = 0;
    this._topMenuFeedbackAction = '';
    if (!this._topMenuBar) return;
    delete this._topMenuBar.dataset.menuFeedback;
    delete this._topMenuBar.dataset.menuFeedbackAction;
    this._topMenuBar.classList.remove('action-feedback');
    this._topMenuBar.querySelectorAll('.wm-top-menu-item.action-feedback').forEach((item) => {
      item.classList.remove('action-feedback');
      delete item.dataset.menuFeedback;
    });
  }

  _activeWindowTitle() {
    const focused = document.querySelector('.wm-window.focused, .wm-window.active');
    const title = focused?.querySelector('.wm-title')?.textContent || focused?.dataset.title || '';
    return String(title || 'Desktop').trim() || 'Desktop';
  }

  _topMenuTimeLabel() {
    const now = new Date();
    return now.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
  }

  _activateTopMenuAction(action) {
    if (action === 'launcher') this._toggleAppLauncher(true);
    else if (action === 'command_palette') this._toggleCommandPalette(true);
    else if (action === 'widgets') this._toggleWidgetGallery(true);
    else if (action === 'quick_settings') this._toggleQuickSettings(true);
    else if (action === 'focus_mode') this._toggleFocusMode();
    else if (action === 'notifications') this._toggleNotificationCenter(true);
    else if (action === 'control_center') this._toggleControlCenter(true);
    this._sendWindowCmd('top_menu_action', { menu_action: action });
  }

  _ensureCommandPalette() {
    if (this._commandPalette) return this._commandPalette;
    const palette = document.createElement('aside');
    palette.className = 'wm-command-palette';
    palette.hidden = true;
    palette.setAttribute('role', 'dialog');
    palette.setAttribute('aria-label', 'Simple command palette');

    const input = document.createElement('input');
    input.className = 'wm-command-palette-input';
    input.type = 'text';
    input.placeholder = 'Run a command';
    input.setAttribute('aria-label', 'Global command');
    input.setAttribute('aria-controls', 'wm-command-palette-list');
    input.setAttribute('aria-activedescendant', 'wm-command-item-0');
    palette.appendChild(input);

    const list = document.createElement('div');
    list.id = 'wm-command-palette-list';
    list.className = 'wm-command-palette-list';
    list.setAttribute('role', 'listbox');
    list.setAttribute('aria-label', 'Available commands');
    list.setAttribute('aria-activedescendant', 'wm-command-item-0');
    palette.appendChild(list);
    document.body.appendChild(palette);

    this._commandPalette = palette;
    this._commandPaletteInput = input;
    this._commandPaletteList = list;
    input.addEventListener('input', () => {
      this._commandPaletteActiveIndex = 0;
      this._renderCommandPaletteItems();
    });
    input.addEventListener('keydown', (event) => this._handleCommandPaletteKeydown(event, false));
    list.addEventListener('click', (event) => {
      const target = event.target && event.target.closest ? event.target : null;
      const item = target ? target.closest('.wm-command-item, .wm-command-recent') : null;
      if (!item || !list.contains(item)) return;
      const index = Number(item.dataset.commandIndex || 0);
      this._commandPaletteActiveIndex = index;
      if (item.classList.contains('wm-command-recent')) {
        this._executeCommandPaletteRecent(index);
        return;
      }
      this._executeCommandPaletteAction();
    });
    list.addEventListener('keydown', (event) => this._handleCommandPaletteKeydown(event, true));
    this._renderCommandPaletteItems();
    return palette;
  }

  _commandPaletteCommands() {
    return [
      { label: 'Open Simple IDE', category: 'Apps', shortcut: 'Enter', icon: 'I', action: () => this._sendLaunch('simple.ide') },
      { label: 'Open app launcher', category: 'Apps', shortcut: 'Cmd Space', icon: 'A', action: () => this._toggleAppLauncher(true) },
      { label: 'Show keyboard shortcuts', category: 'Help', shortcut: 'Cmd /', icon: '?', action: () => this._toggleShortcutOverlay(true) },
      { label: 'Open control center', category: 'System', shortcut: 'Cmd ,', icon: 'C', action: () => this._toggleControlCenter(true) },
      { label: 'Show system HUD', category: 'System', shortcut: 'Cmd Shift H', icon: 'H', action: () => this._showSystemHud('System', 'ready', 2600) },
      { label: 'Show privacy status', category: 'System', shortcut: 'Cmd Shift P', icon: 'P', action: () => this._togglePrivacyIndicator(true) },
      { label: 'Show window overview', category: 'Windows', shortcut: 'Cmd O', icon: 'O', action: () => this._toggleWindowOverview(true) },
      { label: 'Arrange windows', category: 'Windows', shortcut: 'Cmd Shift L', icon: 'L', action: () => this._toggleWindowArrangePalette(true) },
      { label: 'Peek desktop', category: 'Windows', shortcut: 'Cmd Shift M', icon: 'P', action: () => this._toggleDesktopPeek() },
      { label: 'Show stage rail', category: 'Windows', shortcut: 'Cmd Shift O', icon: 'R', action: () => this._toggleStageRail(true) },
      { label: 'Show window switcher', category: 'Windows', shortcut: 'Cmd Tab', icon: 'T', action: () => this._toggleWindowSwitcher(true) },
      { label: 'Switch workspace', category: 'Workspace', shortcut: 'Cmd Shift W', icon: 'S', action: () => this._toggleWorkspaceSwitcher(true) },
      { label: 'Show clipboard history', category: 'Workspace', shortcut: 'Cmd Shift V', icon: 'V', action: () => this._toggleClipboardHistory(true) },
      { label: 'Open screen capture', category: 'Workspace', shortcut: 'Cmd Shift S', icon: 'C', action: () => this._toggleScreenCapture(true) },
      { label: 'Open quick settings', category: 'System', shortcut: 'Cmd Shift Q', icon: 'Q', action: () => this._toggleQuickSettings(true) },
      { label: 'Show notification center', category: 'System', shortcut: 'Cmd Shift N', icon: 'N', action: () => this._toggleNotificationCenter(true) },
      { label: 'Show live activity', category: 'System', shortcut: 'Cmd Shift A', icon: 'A', action: () => this._toggleLiveActivity(true) },
      { label: 'Show gesture hints', category: 'Help', shortcut: 'Cmd Shift G', icon: 'G', action: () => this._toggleGestureHints(true) },
      { label: 'Open Dock stack', category: 'Apps', shortcut: 'Cmd Shift D', icon: 'D', action: () => this._toggleDockStack(true) },
      { label: 'Open quality inspector', category: 'Quality', shortcut: 'Cmd Shift I', icon: 'Q', action: () => this._toggleQualityInspector(true) },
      { label: 'Open accent palette', category: 'Appearance', shortcut: 'Cmd Shift C', icon: 'A', action: () => this._toggleAccentPalette(true) },
      { label: 'Toggle Focus mode', category: 'System', shortcut: 'Cmd Shift F', icon: 'F', action: () => this._toggleFocusMode() },
      { label: 'Toggle desktop widgets', category: 'Workspace', shortcut: 'Cmd W', icon: 'W', action: () => this._toggleDesktopWidgets() },
      { label: 'Toggle desktop items', category: 'Workspace', shortcut: 'Cmd Shift E', icon: 'E', action: () => this._toggleDesktopItems() },
      { label: 'Set motion: standard', category: 'Appearance', shortcut: 'Cmd 1', icon: 'S', action: () => this.setMotionPreference('standard') },
      { label: 'Set motion: reduced', category: 'Appearance', shortcut: 'Cmd 2', icon: 'M', action: () => this.setMotionPreference('reduced') },
      { label: 'Set motion: off', category: 'Appearance', shortcut: 'Cmd 3', icon: 'O', action: () => this.setMotionPreference('off') },
      { label: 'Set transparency: standard', category: 'Appearance', shortcut: 'Cmd 4', icon: 'G', action: () => this.setTransparencyPreference('standard') },
      { label: 'Set transparency: reduced', category: 'Appearance', shortcut: 'Cmd 5', icon: 'R', action: () => this.setTransparencyPreference('reduced') },
      { label: 'Set transparency: off', category: 'Appearance', shortcut: 'Cmd 6', icon: 'S', action: () => this.setTransparencyPreference('off') },
      { label: 'Set accent: blue', category: 'Appearance', shortcut: '', icon: 'B', action: () => this._setAccentFromControlCenter('blue') },
      { label: 'Set accent: green', category: 'Appearance', shortcut: '', icon: 'G', action: () => this._setAccentFromControlCenter('green') },
      { label: 'Set accent: rose', category: 'Appearance', shortcut: '', icon: 'R', action: () => this._setAccentFromControlCenter('rose') },
      { label: 'Set accent: amber', category: 'Appearance', shortcut: '', icon: 'A', action: () => this._setAccentFromControlCenter('amber') },
      { label: 'Set accent: violet', category: 'Appearance', shortcut: '', icon: 'V', action: () => this._setAccentFromControlCenter('violet') },
      { label: 'Set contrast: comfortable', category: 'Appearance', shortcut: '', icon: 'C', action: () => this.setContrastPreference('comfortable') },
      { label: 'Set contrast: high', category: 'Appearance', shortcut: '', icon: 'H', action: () => this.setContrastPreference('high') },
      { label: 'Set feedback: standard', category: 'Appearance', shortcut: '', icon: 'F', action: () => this.setFeedbackPreference('standard') },
      { label: 'Set feedback: subtle', category: 'Appearance', shortcut: '', icon: 'F', action: () => this.setFeedbackPreference('subtle') },
      { label: 'Set feedback: off', category: 'Appearance', shortcut: '', icon: 'F', action: () => this.setFeedbackPreference('off') },
      { label: 'Set energy: standard', category: 'Appearance', shortcut: '', icon: 'E', action: () => this.setEnergyPreference('standard') },
      { label: 'Set energy: low power', category: 'Appearance', shortcut: '', icon: 'E', action: () => this.setEnergyPreference('low') },
      { label: 'Set energy: critical saver', category: 'Appearance', shortcut: '', icon: 'E', action: () => this.setEnergyPreference('critical') },
      { label: 'Set backdrop intensity: vivid', category: 'Appearance', shortcut: '', icon: 'V', action: () => this.setBackdropIntensityPreference('vivid') },
      { label: 'Set backdrop intensity: balanced', category: 'Appearance', shortcut: '', icon: 'B', action: () => this.setBackdropIntensityPreference('balanced') },
      { label: 'Set backdrop intensity: quiet', category: 'Appearance', shortcut: '', icon: 'Q', action: () => this.setBackdropIntensityPreference('quiet') },
      { label: 'Set animation style: spring', category: 'Appearance', shortcut: '', icon: 'S', action: () => this.setAnimationStyle('spring') },
      { label: 'Set animation style: calm', category: 'Appearance', shortcut: '', icon: 'C', action: () => this.setAnimationStyle('calm') },
      { label: 'Set animation style: snappy', category: 'Appearance', shortcut: '', icon: 'N', action: () => this.setAnimationStyle('snappy') },
      { label: 'Set dock magnification: standard', category: 'Appearance', shortcut: '', icon: 'D', action: () => this.setDockMagnificationPreference('standard') },
      { label: 'Set dock magnification: subtle', category: 'Appearance', shortcut: '', icon: 'D', action: () => this.setDockMagnificationPreference('subtle') },
      { label: 'Set dock magnification: off', category: 'Appearance', shortcut: '', icon: 'D', action: () => this.setDockMagnificationPreference('off') },
      { label: 'Set dock visibility: shown', category: 'Appearance', shortcut: '', icon: 'D', action: () => this.setDockVisibilityPreference('shown') },
      { label: 'Set dock visibility: auto-hide', category: 'Appearance', shortcut: '', icon: 'D', action: () => this.setDockVisibilityPreference('auto') },
      { label: 'Set dock visibility: hidden', category: 'Appearance', shortcut: '', icon: 'D', action: () => this.setDockVisibilityPreference('hidden') },
      { label: 'Set corner radius: round', category: 'Appearance', shortcut: '', icon: 'R', action: () => this.setCornerRadiusPreference('round') },
      { label: 'Set corner radius: soft', category: 'Appearance', shortcut: '', icon: 'S', action: () => this.setCornerRadiusPreference('soft') },
      { label: 'Set corner radius: square', category: 'Appearance', shortcut: '', icon: 'Q', action: () => this.setCornerRadiusPreference('square') },
      { label: 'Set chrome verbosity: full', category: 'Appearance', shortcut: '', icon: 'F', action: () => this.setChromeVerbosityPreference('full') },
      { label: 'Set chrome verbosity: compact', category: 'Appearance', shortcut: '', icon: 'C', action: () => this.setChromeVerbosityPreference('compact') },
      { label: 'Set chrome verbosity: minimal', category: 'Appearance', shortcut: '', icon: 'M', action: () => this.setChromeVerbosityPreference('minimal') },
      { label: 'Set window motion: mac', category: 'Appearance', shortcut: '', icon: 'M', action: () => this.setWindowTransitionPreference('mac') },
      { label: 'Set window motion: fade', category: 'Appearance', shortcut: '', icon: 'F', action: () => this.setWindowTransitionPreference('fade') },
      { label: 'Set window motion: none', category: 'Appearance', shortcut: '', icon: 'N', action: () => this.setWindowTransitionPreference('none') },
      { label: 'Set quiet mode: off', category: 'Appearance', shortcut: '', icon: 'Q', action: () => this.setQuietModePreference('off') },
      { label: 'Set quiet mode: on', category: 'Appearance', shortcut: '', icon: 'Q', action: () => this.setQuietModePreference('on') },
      { label: 'Open wallpaper picker', category: 'Appearance', shortcut: 'Cmd Shift B', icon: 'B', action: () => this._toggleWallpaperPicker(true) },
      { label: 'Set wallpaper: aurora', category: 'Appearance', shortcut: 'Cmd 7', icon: 'A', action: () => this.setWallpaperPreference('aurora') },
      { label: 'Set wallpaper: mesh', category: 'Appearance', shortcut: 'Cmd 8', icon: 'M', action: () => this.setWallpaperPreference('mesh') },
      { label: 'Set wallpaper: solid', category: 'Appearance', shortcut: 'Cmd 9', icon: 'D', action: () => this.setWallpaperPreference('solid') },
      { label: 'Open widget gallery', category: 'Workspace', shortcut: 'Cmd G', icon: 'W', action: () => this._toggleWidgetGallery(true) }
    ];
  }

  _renderCommandPaletteItems() {
    if (!this._commandPaletteList) return;
    this._clearCommandRecentFeedback();
    const query = String(this._commandPaletteInput?.value || '').trim().toLowerCase();
    const commands = this._commandPaletteCommands()
      .filter((command) => !query || command.label.toLowerCase().includes(query));
    this._commandPaletteItems = commands;
    this._commandPaletteActiveIndex = Math.min(this._commandPaletteActiveIndex, Math.max(commands.length - 1, 0));
    this._commandPaletteList.innerHTML = '';
    if (commands.length) {
      this._commandPaletteList.setAttribute('aria-activedescendant', `wm-command-item-${this._commandPaletteActiveIndex}`);
      this._commandPaletteInput?.setAttribute('aria-activedescendant', `wm-command-item-${this._commandPaletteActiveIndex}`);
    } else {
      this._commandPaletteList.removeAttribute('aria-activedescendant');
      this._commandPaletteInput?.removeAttribute('aria-activedescendant');
    }
    if (!query) this._renderCommandPaletteRecents(commands);
    let lastCategory = '';
    commands.forEach((command, index) => {
      const active = index === this._commandPaletteActiveIndex;
      const category = command.category || 'Commands';
      if (category !== lastCategory) {
        const heading = document.createElement('div');
        heading.className = 'wm-command-section';
        heading.textContent = category;
        this._commandPaletteList.appendChild(heading);
        lastCategory = category;
      }
      const item = document.createElement('button');
      item.type = 'button';
      item.id = `wm-command-item-${index}`;
      item.className = 'wm-command-item' + (active ? ' active' : '');
      item.dataset.commandIndex = String(index);
      item.dataset.commandCategory = category;
      item.tabIndex = active ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', active ? 'true' : 'false');
      item.setAttribute('aria-label', command.label);
      item.appendChild(this._makeRoundIcon('wm-taskbar-icon', command.icon));
      const label = document.createElement('span');
      label.textContent = command.label;
      item.appendChild(label);
      const shortcut = document.createElement('span');
      shortcut.className = 'wm-command-shortcut';
      shortcut.textContent = command.shortcut;
      item.appendChild(shortcut);
      this._commandPaletteList.appendChild(item);
    });
  }

  _renderCommandPaletteRecents(commands) {
    const recents = commands.filter((command) => ['Open Simple IDE', 'Open control center', 'Open quality inspector'].includes(command.label));
    if (!recents.length) return;
    const rail = document.createElement('div');
    rail.className = 'wm-command-recents';
    rail.setAttribute('aria-label', 'Recent commands');
    recents.forEach((command) => {
      const chip = document.createElement('button');
      chip.type = 'button';
      chip.className = 'wm-command-recent';
      chip.dataset.commandIndex = String(commands.indexOf(command));
      chip.dataset.commandCategory = command.category || 'Commands';
      chip.setAttribute('aria-label', command.label);
      chip.appendChild(this._makeRoundIcon('wm-command-recent-icon', command.icon));
      const label = document.createElement('span');
      label.textContent = command.label;
      chip.appendChild(label);
      rail.appendChild(chip);
    });
    this._commandPaletteList.appendChild(rail);
  }

  _toggleCommandPalette(open = null) {
    const palette = this._ensureCommandPalette();
    const shouldOpen = open == null ? palette.hidden : open;
    palette.hidden = !shouldOpen;
    if (shouldOpen) {
      this._commandPaletteInput.value = '';
      this._commandPaletteActiveIndex = 0;
      this._renderCommandPaletteItems();
      this._commandPaletteInput.focus();
    }
  }

  _moveCommandPaletteSelection(delta) {
    if (!this._commandPalette || this._commandPalette.hidden) return;
    const count = this._commandPaletteItems.length;
    if (!count) return;
    this._commandPaletteActiveIndex = (this._commandPaletteActiveIndex + delta + count) % count;
    this._syncCommandPaletteSelection(false);
  }

  _setCommandPaletteSelection(index, shouldFocus = false) {
    if (!this._commandPalette || this._commandPalette.hidden) return;
    const count = this._commandPaletteItems.length;
    if (!count) return;
    this._commandPaletteActiveIndex = Math.max(0, Math.min(count - 1, index));
    this._syncCommandPaletteSelection(shouldFocus);
  }

  _syncCommandPaletteSelection(shouldFocus = false) {
    if (!this._commandPaletteList) return;
    const items = Array.from(this._commandPaletteList.querySelectorAll('.wm-command-item'));
    if (!items.length) return;
    const activeIndex = Math.max(0, Math.min(items.length - 1, this._commandPaletteActiveIndex));
    this._commandPaletteActiveIndex = activeIndex;
    const activeId = `wm-command-item-${activeIndex}`;
    this._commandPaletteList.setAttribute('aria-activedescendant', activeId);
    this._commandPaletteInput?.setAttribute('aria-activedescendant', activeId);
    items.forEach((item, index) => {
      const active = index === activeIndex;
      item.classList.toggle('active', active);
      item.setAttribute('aria-selected', active ? 'true' : 'false');
      item.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) item.focus();
    });
  }

  _handleCommandPaletteKeydown(event, shouldFocus = false) {
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      this._moveCommandPaletteSelection(1);
      if (shouldFocus) this._syncCommandPaletteSelection(true);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      this._moveCommandPaletteSelection(-1);
      if (shouldFocus) this._syncCommandPaletteSelection(true);
    } else if (event.key === 'Home') {
      event.preventDefault();
      this._setCommandPaletteSelection(0, shouldFocus);
    } else if (event.key === 'End') {
      event.preventDefault();
      this._setCommandPaletteSelection(this._commandPaletteItems.length - 1, shouldFocus);
    } else if (event.key === 'Enter') {
      event.preventDefault();
      this._executeCommandPaletteAction();
    } else if (event.key === 'Escape') {
      event.preventDefault();
      this._toggleCommandPalette(false);
    }
  }

  _executeCommandPaletteAction() {
    if (!this._commandPalette || this._commandPalette.hidden) return;
    const command = this._commandPaletteItems[this._commandPaletteActiveIndex];
    if (!command) return;
    command.action();
    this._toggleCommandPalette(false);
  }

  _executeCommandPaletteRecent(index) {
    if (!this._commandPalette || this._commandPalette.hidden) return;
    const command = this._commandPaletteItems[index];
    if (!command) return;
    this._commandPaletteActiveIndex = index;
    this._markCommandRecentFeedback(index, command);
    this._sendWindowCmd('command_palette_recent', {
      command_label: command.label,
      command_category: command.category || 'Commands'
    });
    window.setTimeout(() => {
      if (!this._commandPalette || this._commandPalette.hidden) return;
      command.action();
      this._toggleCommandPalette(false);
    }, 180);
  }

  _markCommandRecentFeedback(index, command) {
    if (!this._commandPalette || !this._feedbackAllows('standard')) return;
    window.clearTimeout(this._commandRecentFeedbackTimer);
    this._clearCommandRecentFeedback();
    const palette = this._commandPalette;
    palette.dataset.commandRecentFeedback = 'activate';
    palette.dataset.commandRecentIndex = String(index);
    palette.classList.add('action-feedback');
    const chip = palette.querySelector(`.wm-command-recent[data-command-index="${index}"]`);
    if (chip) {
      chip.dataset.commandFeedback = 'recent';
      chip.classList.add('action-feedback');
      chip.setAttribute('aria-label', `${command.label}, activated`);
      const icon = chip.querySelector('.wm-command-recent-icon');
      if (icon) icon.classList.add('action-feedback');
    }
    this._commandRecentFeedbackTimer = window.setTimeout(() => this._clearCommandRecentFeedback(), 560);
  }

  _clearCommandRecentFeedback() {
    window.clearTimeout(this._commandRecentFeedbackTimer);
    this._commandRecentFeedbackTimer = 0;
    if (!this._commandPalette) return;
    delete this._commandPalette.dataset.commandRecentFeedback;
    delete this._commandPalette.dataset.commandRecentIndex;
    this._commandPalette.classList.remove('action-feedback');
    this._commandPalette.querySelectorAll('.wm-command-recent.action-feedback, .wm-command-recent-icon.action-feedback').forEach((node) => {
      node.classList.remove('action-feedback');
      if (node.dataset && node.dataset.commandFeedback) delete node.dataset.commandFeedback;
      if (node.classList.contains('wm-command-recent')) {
        const labelEl = Array.from(node.children).find((child) => child.tagName === 'SPAN' && !child.classList.contains('wm-command-recent-icon'));
        const label = labelEl ? labelEl.textContent || '' : '';
        if (label) node.setAttribute('aria-label', label);
      }
    });
  }

  _ensureShortcutOverlay() {
    if (this._shortcutOverlay) return this._shortcutOverlay;
    const overlay = document.createElement('aside');
    overlay.className = 'wm-shortcut-overlay';
    overlay.hidden = true;
    overlay.setAttribute('role', 'dialog');
    overlay.setAttribute('aria-label', 'Keyboard shortcuts');

    const title = document.createElement('div');
    title.className = 'wm-shortcut-title';
    title.textContent = 'Keyboard shortcuts';
    overlay.appendChild(title);

    const search = document.createElement('input');
    search.className = 'wm-shortcut-search';
    search.type = 'search';
    search.placeholder = 'Search shortcuts';
    search.setAttribute('aria-label', 'Search keyboard shortcuts');
    search.setAttribute('aria-controls', 'wm-shortcut-grid');
    search.setAttribute('aria-activedescendant', 'wm-shortcut-row-0');
    overlay.appendChild(search);

    const grid = document.createElement('div');
    grid.id = 'wm-shortcut-grid';
    grid.className = 'wm-shortcut-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Available keyboard shortcuts');
    grid.setAttribute('aria-activedescendant', 'wm-shortcut-row-0');
    overlay.appendChild(grid);

    document.body.appendChild(overlay);
    overlay.addEventListener('click', (event) => {
      if (event.target === overlay) this._toggleShortcutOverlay(false);
    });
    search.addEventListener('input', () => {
      this._shortcutSearchQuery = search.value || '';
      this._shortcutOverlayActiveIndex = 0;
      this._renderShortcutOverlay();
    });
    search.addEventListener('keydown', (event) => this._handleShortcutOverlayKeydown(event, false));
    grid.addEventListener('keydown', (event) => this._handleShortcutOverlayKeydown(event, true));
    grid.addEventListener('click', (event) => {
      const target = event.target && event.target.closest ? event.target : null;
      const row = target ? target.closest('.wm-shortcut-row') : null;
      if (!row || !grid.contains(row)) return;
      this._activateShortcutOverlaySelection(Number(row.dataset.shortcutIndex || '0'));
    });
    this._shortcutOverlay = overlay;
    this._renderShortcutOverlay();
    return overlay;
  }

  _toggleShortcutOverlay(open = null) {
    const overlay = this._ensureShortcutOverlay();
    const shouldOpen = open == null ? overlay.hidden : open;
    overlay.hidden = !shouldOpen;
    if (shouldOpen) {
      const search = overlay.querySelector('.wm-shortcut-search');
      if (search) {
        search.value = this._shortcutSearchQuery;
        search.focus();
      }
      this._renderShortcutOverlay();
    }
  }

  _shortcutOverlayItems() {
    const commandItems = this._commandPaletteCommands()
      .filter((command) => command.shortcut)
      .map((command) => ({ label: command.label, key: command.shortcut, category: command.category || 'Commands' }));
    return commandItems.concat([
      { label: 'Command palette', key: 'Cmd K', category: 'Help' },
      { label: 'Title command', key: 'Cmd L', category: 'Windows' },
      { label: 'Close panels', key: 'Esc', category: 'System' }
    ]);
  }

  _filteredShortcutOverlayItems() {
    const query = String(this._shortcutSearchQuery || '').trim().toLowerCase();
    const order = ['Apps', 'Windows', 'Workspace', 'System', 'Appearance', 'Quality', 'Help'];
    return this._shortcutOverlayItems().filter((item) => {
      if (!query) return true;
      return item.label.toLowerCase().includes(query) || item.key.toLowerCase().includes(query) || item.category.toLowerCase().includes(query);
    }).sort((a, b) => {
      const left = order.indexOf(a.category);
      const right = order.indexOf(b.category);
      const leftRank = left < 0 ? order.length : left;
      const rightRank = right < 0 ? order.length : right;
      if (leftRank !== rightRank) return leftRank - rightRank;
      return a.label.localeCompare(b.label);
    });
  }

  _renderShortcutOverlay() {
    if (!this._shortcutOverlay) return;
    const grid = this._shortcutOverlay.querySelector('.wm-shortcut-grid');
    if (!grid) return;
    this._clearShortcutOverlayFeedback();
    const items = this._filteredShortcutOverlayItems();
    this._shortcutOverlayItemsCache = items;
    this._shortcutOverlayActiveIndex = Math.min(this._shortcutOverlayActiveIndex, Math.max(items.length - 1, 0));
    grid.innerHTML = '';
    if (!items.length) {
      grid.removeAttribute('aria-activedescendant');
      this._shortcutOverlay.querySelector('.wm-shortcut-search')?.removeAttribute('aria-activedescendant');
      const empty = document.createElement('div');
      empty.className = 'wm-shortcut-empty';
      empty.textContent = 'No matching shortcuts';
      grid.appendChild(empty);
      return;
    }
    grid.setAttribute('aria-activedescendant', `wm-shortcut-row-${this._shortcutOverlayActiveIndex}`);
    this._shortcutOverlay.querySelector('.wm-shortcut-search')?.setAttribute('aria-activedescendant', `wm-shortcut-row-${this._shortcutOverlayActiveIndex}`);
    let lastCategory = '';
    items.forEach((item, index) => {
      if (item.category !== lastCategory) {
        const section = document.createElement('div');
        section.className = 'wm-shortcut-section';
        section.textContent = item.category;
        grid.appendChild(section);
        lastCategory = item.category;
      }
      grid.appendChild(this._makeShortcutOverlayRow(item, index));
    });
  }

  _makeShortcutOverlayRow(item, index) {
    const active = index === this._shortcutOverlayActiveIndex;
    const row = document.createElement('button');
    row.type = 'button';
    row.id = `wm-shortcut-row-${index}`;
    row.className = 'wm-shortcut-row' + (active ? ' active' : '');
    row.dataset.shortcutCategory = item.category;
    row.dataset.shortcutIndex = String(index);
    row.dataset.shortcutKey = item.key;
    row.tabIndex = active ? 0 : -1;
    row.setAttribute('role', 'option');
    row.setAttribute('aria-selected', active ? 'true' : 'false');
    row.setAttribute('aria-label', `${item.label}: ${item.key}`);
    const name = document.createElement('span');
    name.className = 'wm-shortcut-label';
    name.textContent = item.label;
    const badge = document.createElement('kbd');
    badge.className = 'wm-shortcut-key';
    badge.textContent = item.key;
    row.appendChild(name);
    row.appendChild(badge);
    return row;
  }

  _handleShortcutOverlayKeydown(event, shouldFocus = false) {
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      this._moveShortcutOverlaySelection(1, shouldFocus);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      this._moveShortcutOverlaySelection(-1, shouldFocus);
    } else if (event.key === 'Home') {
      event.preventDefault();
      this._setShortcutOverlaySelection(0, shouldFocus);
    } else if (event.key === 'End') {
      event.preventDefault();
      this._setShortcutOverlaySelection(this._shortcutOverlayItemsCache.length - 1, shouldFocus);
    } else if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      this._activateShortcutOverlaySelection(this._shortcutOverlayActiveIndex);
    } else if (event.key === 'Escape') {
      event.preventDefault();
      this._toggleShortcutOverlay(false);
    }
  }

  _activateShortcutOverlaySelection(index = this._shortcutOverlayActiveIndex) {
    if (!this._shortcutOverlay || this._shortcutOverlay.hidden) return;
    const count = this._shortcutOverlayItemsCache.length;
    if (!count) return;
    const activeIndex = Math.max(0, Math.min(count - 1, index));
    this._shortcutOverlayActiveIndex = activeIndex;
    this._syncShortcutOverlaySelection(false);
    const item = this._shortcutOverlayItemsCache[activeIndex];
    if (!item) return;
    this._markShortcutOverlayFeedback(activeIndex, item);
    this._sendWindowCmd('shortcut_overlay_activate', {
      shortcut_label: item.label,
      shortcut_key: item.key,
      shortcut_category: item.category
    });
  }

  _markShortcutOverlayFeedback(index, item) {
    if (!this._shortcutOverlay || !this._feedbackAllows('standard')) return;
    const overlay = this._shortcutOverlay;
    window.clearTimeout(this._shortcutOverlayFeedbackTimer);
    this._clearShortcutOverlayFeedback();
    overlay.dataset.shortcutFeedback = 'activate';
    overlay.dataset.shortcutFeedbackIndex = String(index);
    overlay.classList.add('action-feedback');
    const row = overlay.querySelector(`.wm-shortcut-row[data-shortcut-index="${index}"]`);
    if (row) {
      row.dataset.shortcutFeedback = 'activate';
      row.classList.add('action-feedback');
      row.setAttribute('aria-label', `${item.label}: ${item.key}, activated`);
      const key = row.querySelector('.wm-shortcut-key');
      if (key) key.classList.add('action-feedback');
    }
    this._shortcutOverlayFeedbackTimer = window.setTimeout(() => this._clearShortcutOverlayFeedback(), 560);
  }

  _clearShortcutOverlayFeedback() {
    if (!this._shortcutOverlay) return;
    window.clearTimeout(this._shortcutOverlayFeedbackTimer);
    this._shortcutOverlayFeedbackTimer = 0;
    delete this._shortcutOverlay.dataset.shortcutFeedback;
    delete this._shortcutOverlay.dataset.shortcutFeedbackIndex;
    this._shortcutOverlay.classList.remove('action-feedback');
    this._shortcutOverlay.querySelectorAll('.wm-shortcut-row.action-feedback, .wm-shortcut-key.action-feedback').forEach((node) => {
      node.classList.remove('action-feedback');
      if (node.dataset && node.dataset.shortcutFeedback) delete node.dataset.shortcutFeedback;
      if (node.classList.contains('wm-shortcut-row')) {
        const label = node.querySelector('.wm-shortcut-label')?.textContent || '';
        const key = node.querySelector('.wm-shortcut-key')?.textContent || '';
        if (label && key) node.setAttribute('aria-label', `${label}: ${key}`);
      }
    });
  }

  _moveShortcutOverlaySelection(delta, shouldFocus = false) {
    if (!this._shortcutOverlay || this._shortcutOverlay.hidden) return;
    const count = this._shortcutOverlayItemsCache.length;
    if (!count) return;
    this._shortcutOverlayActiveIndex = (this._shortcutOverlayActiveIndex + delta + count) % count;
    this._syncShortcutOverlaySelection(shouldFocus);
  }

  _setShortcutOverlaySelection(index, shouldFocus = false) {
    if (!this._shortcutOverlay || this._shortcutOverlay.hidden) return;
    const count = this._shortcutOverlayItemsCache.length;
    if (!count) return;
    this._shortcutOverlayActiveIndex = Math.max(0, Math.min(count - 1, index));
    this._syncShortcutOverlaySelection(shouldFocus);
  }

  _syncShortcutOverlaySelection(shouldFocus = false) {
    if (!this._shortcutOverlay) return;
    const grid = this._shortcutOverlay.querySelector('.wm-shortcut-grid');
    const rows = grid ? Array.from(grid.querySelectorAll('.wm-shortcut-row')) : [];
    if (!grid || !rows.length) return;
    const activeIndex = Math.max(0, Math.min(rows.length - 1, this._shortcutOverlayActiveIndex));
    this._shortcutOverlayActiveIndex = activeIndex;
    const activeId = `wm-shortcut-row-${activeIndex}`;
    grid.setAttribute('aria-activedescendant', activeId);
    this._shortcutOverlay.querySelector('.wm-shortcut-search')?.setAttribute('aria-activedescendant', activeId);
    rows.forEach((row, index) => {
      const active = index === activeIndex;
      row.classList.toggle('active', active);
      row.setAttribute('aria-selected', active ? 'true' : 'false');
      row.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) row.focus();
    });
  }

  _ensureWmTooltip() {
    if (this._wmTooltip) return this._wmTooltip;
    const tooltip = document.createElement('div');
    tooltip.className = 'wm-tooltip';
    tooltip.hidden = true;
    tooltip.setAttribute('role', 'tooltip');
    document.body.appendChild(tooltip);
    this._wmTooltip = tooltip;
    return tooltip;
  }

  _tooltipAnchorFromEvent(event) {
    const target = event.target instanceof Element ? event.target : event.target?.parentElement;
    if (!target) return null;
    return target.closest('[data-wm-tooltip], .wm-traffic-lights button, .wm-taskbar-item, .wm-taskbar-preview-action, .wm-widget-control, .wm-hot-corner-zone');
  }

  _tooltipTextForAnchor(anchor) {
    if (!anchor) return '';
    return String(anchor.dataset.wmTooltip || anchor.getAttribute('aria-label') || '').trim();
  }

  _showWmTooltipForEvent(event) {
    const anchor = this._tooltipAnchorFromEvent(event);
    const label = this._tooltipTextForAnchor(anchor);
    if (!anchor || !label) return;
    const tooltip = this._ensureWmTooltip();
    this._wmTooltipAnchor = anchor;
    tooltip.textContent = label;
    tooltip.hidden = false;
    this._positionWmTooltip(anchor, event);
  }

  _positionWmTooltipForEvent(event) {
    if (!this._wmTooltip || this._wmTooltip.hidden || !this._wmTooltipAnchor) return;
    this._positionWmTooltip(this._wmTooltipAnchor, event);
  }

  _hideWmTooltipForEvent(event) {
    const anchor = this._tooltipAnchorFromEvent(event);
    if (!anchor || anchor !== this._wmTooltipAnchor) return;
    const related = event.relatedTarget instanceof Element ? event.relatedTarget : null;
    if (related && anchor.contains(related)) return;
    this._hideWmTooltip();
  }

  _positionWmTooltip(anchor, event) {
    const tooltip = this._ensureWmTooltip();
    const rect = anchor.getBoundingClientRect();
    const x = event && Number.isFinite(event.clientX) ? event.clientX : rect.left + rect.width / 2;
    const y = event && Number.isFinite(event.clientY) ? event.clientY : rect.top;
    const left = Math.max(12, Math.min(window.innerWidth - 12, Math.round(x)));
    const top = Math.max(12, Math.min(window.innerHeight - 12, Math.round(y - 14)));
    tooltip.style.left = `${left}px`;
    tooltip.style.top = `${top}px`;
  }

  _hideWmTooltip() {
    if (!this._wmTooltip) return;
    this._wmTooltip.hidden = true;
    this._wmTooltipAnchor = null;
  }

  // Install one persistent click listener on the taskbar that dispatches
  // by data-action. Idempotent — rendering can clear innerHTML without
  // losing the handler. Call once after this.taskbar is bound.
  _installTaskbarDelegation() {
    if (!this.taskbar || this._taskbarDelegationInstalled) return;
    this._taskbarDelegationInstalled = true;
    this.taskbar.addEventListener('click', (ev) => {
      const el = ev.target.closest('[data-action]');
      if (!el || !this.taskbar.contains(el)) return;
      this._activateTaskbarItem(el, ev);
    });
    this.taskbar.addEventListener('keydown', (ev) => {
      if (ev.key !== 'Enter' && ev.key !== ' ') return;
      const el = ev.target.closest('[data-action]');
      if (!el || !this.taskbar.contains(el)) return;
      ev.preventDefault();
      this._activateTaskbarItem(el, ev);
    });
  }

  _activateTaskbarItem(el, ev) {
    const action = el.dataset.action;
    if (action === 'launch' && el.dataset.appId) {
      this._markLaunchFeedback(el.dataset.appId, el);
      this._sendHostWmPointer(ev, 'down');
    } else if (action === 'focus' && el.dataset.windowIdHint) {
      if (this.transport === 'electron-ipc' && this._electronWindows.has(el.dataset.windowIdHint)) {
        this._electronFocusWindow(el.dataset.windowIdHint);
      }
      this._sendHostWmPointer(ev, 'down');
    }
  }

  // Render a TaskbarModel { pinned, running, tray } into the taskbar
  // element. Click handling is via the delegated listener above, so
  // replacing innerHTML does not lose dispatch.
  renderTaskbarModel(model) {
    if (!this.taskbar) return;
    this._installTaskbarDelegation();
    this.taskbar.innerHTML = '';
    this.taskbar.setAttribute('role', 'navigation');
    this.taskbar.setAttribute('aria-label', 'Window taskbar');
    this._launcherApps = (model.pinned || []).map((app) => ({
      app_id: app.app_id || app.id || app.display_name || '',
      display_name: app.display_name || app.name || app.app_id || 'App',
      icon: app.icon || app.display_name || app.app_id || 'A',
      category: app.category || this._appLauncherCategoryForApp(app.app_id || app.id || app.display_name || '', app.display_name || app.name || '')
    })).filter((app) => !!app.app_id);

    const pinned = document.createElement('div');
    pinned.className = 'wm-taskbar-section pinned';
    for (const a of (model.pinned || [])) {
      const item = document.createElement('div');
      item.className = 'wm-taskbar-item pinned';
      item.setAttribute('role', 'button');
      item.setAttribute('tabindex', '0');
      const label = a.display_name || a.app_id;
      const badgeCount = this._taskbarBadgeCount(a);
      item.setAttribute('aria-label', `Launch ${label}${badgeCount ? ', ' + badgeCount + ' notifications' : ''}`);
      item.appendChild(this._makeTaskbarIcon(a.icon || a.display_name || a.app_id));
      item.appendChild(this._makeTaskbarLabel(label));
      this._decorateTaskbarAttention(item, a);
      item.dataset.action = 'launch';
      item.dataset.appId = a.app_id;
      pinned.appendChild(item);
    }
    this.taskbar.appendChild(pinned);

    const running = document.createElement('div');
    running.className = 'wm-taskbar-section running';
    for (const w of (model.running || [])) {
      const item = document.createElement('div');
      item.className = 'wm-taskbar-item running'
        + (w.active ? ' active' : '')
        + (w.minimized ? ' minimized' : '');
      const label = w.title || w.window_id;
      const badgeCount = this._taskbarBadgeCount(w);
      item.setAttribute('role', 'button');
      item.setAttribute('tabindex', '0');
      item.setAttribute('aria-label', `${w.minimized ? 'Restore' : 'Focus'} ${label}${badgeCount ? ', ' + badgeCount + ' notifications' : ''}`);
      item.appendChild(this._makeTaskbarIcon(w.icon || w.title || w.app_id || w.window_id));
      item.appendChild(this._makeTaskbarLabel((w.minimized ? '[-] ' : '') + label));
      this._decorateTaskbarAttention(item, w);
      item.dataset.action = 'focus';
      item.dataset.windowIdHint = w.window_id;
      item.addEventListener('mouseenter', () => this._showTaskbarPreview(w, item));
      item.addEventListener('focus', () => this._showTaskbarPreview(w, item));
      item.addEventListener('mouseleave', () => this._hideTaskbarPreviewSoon());
      item.addEventListener('blur', () => this._hideTaskbarPreviewSoon());
      running.appendChild(item);
    }
    this.taskbar.appendChild(running);

    const tray = document.createElement('div');
    tray.className = 'wm-taskbar-section tray';
    for (const t of (model.tray || [])) {
      const item = document.createElement('div');
      item.className = 'wm-taskbar-tray';
      item.textContent = t.label;
      tray.appendChild(item);
    }
    this.taskbar.appendChild(tray);
  }

  _makeTaskbarIcon(raw) {
    return this._makeRoundIcon('wm-taskbar-icon', raw);
  }

  _ensureTaskbarPreview() {
    if (this._taskbarPreview && this._taskbarPreview.isConnected) return this._taskbarPreview;
    const preview = document.createElement('aside');
    preview.className = 'wm-taskbar-preview';
    preview.hidden = true;
    preview.setAttribute('role', 'tooltip');
    preview.setAttribute('aria-label', 'Taskbar window preview');
    preview.addEventListener('mouseenter', () => this._clearTaskbarPreviewHideTimer());
    preview.addEventListener('mouseleave', () => this._hideTaskbarPreviewSoon());
    preview.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const action = target?.closest('.wm-taskbar-preview-action');
      if (!action || !preview.contains(action)) return;
      event.preventDefault();
      this._activateTaskbarPreviewAction(action.dataset.previewAction || '', preview.dataset.windowId || '', event);
    });
    document.body.appendChild(preview);
    this._taskbarPreview = preview;
    return preview;
  }

  _showTaskbarPreview(entry, anchor) {
    const preview = this._ensureTaskbarPreview();
    this._clearTaskbarPreviewHideTimer();
    const label = entry.title || entry.window_id || 'Window';
    const status = entry.minimized ? 'Minimized' : (entry.active ? 'Active' : 'Open');
    preview.dataset.windowId = entry.window_id || '';
    preview.dataset.previewTitle = label;
    preview.dataset.previewStatus = status;
    preview.innerHTML = '';
    preview.appendChild(this._makeRoundIcon('wm-taskbar-preview-icon', entry.icon || entry.title || entry.app_id || entry.window_id));
    const body = document.createElement('div');
    body.className = 'wm-taskbar-preview-body';
    const title = document.createElement('span');
    title.className = 'wm-taskbar-preview-title';
    title.textContent = label;
    const meta = document.createElement('span');
    meta.className = 'wm-taskbar-preview-meta';
    meta.textContent = entry.app_id || entry.subtitle || entry.path || 'Desktop window';
    const statusEl = document.createElement('span');
    statusEl.className = 'wm-taskbar-preview-status';
    statusEl.textContent = status;
    body.appendChild(title);
    body.appendChild(meta);
    body.appendChild(statusEl);
    preview.appendChild(body);
    const actions = document.createElement('div');
    actions.className = 'wm-taskbar-preview-actions';
    actions.setAttribute('aria-label', 'Taskbar preview actions');
    actions.appendChild(this._makeTaskbarPreviewAction('focus', 'Focus window', 'F'));
    actions.appendChild(this._makeTaskbarPreviewAction('minimize', 'Minimize window', '-'));
    actions.appendChild(this._makeTaskbarPreviewAction('close', 'Close window', 'X'));
    preview.appendChild(actions);
    const rect = anchor.getBoundingClientRect();
    const left = Math.max(12, Math.min(window.innerWidth - 332, rect.left + rect.width / 2 - 160));
    preview.style.left = `${left}px`;
    preview.style.bottom = `${Math.max(64, window.innerHeight - rect.top + 10)}px`;
    preview.hidden = false;
  }

  _makeTaskbarPreviewAction(action, label, glyph) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-taskbar-preview-action';
    button.dataset.previewAction = action;
    button.setAttribute('aria-label', label);
    button.textContent = glyph;
    return button;
  }

  _activateTaskbarPreviewAction(action, windowId, event) {
    if (!action || !windowId) return;
    if (this.transport === 'electron-ipc' && this._electronWindows.has(windowId)) {
      if (action === 'focus') this._electronFocusWindow(windowId);
      if (action === 'minimize') this._electronMinimizeWindow(windowId);
      if (action === 'close') this._electronCloseWindow(windowId);
    }
    this._sendWindowCmd('taskbar_preview_action', { action, window_id: windowId });
    this._sendHostWmPointer(event, 'down');
    this._hideTaskbarPreview();
  }

  _clearTaskbarPreviewHideTimer() {
    if (!this._taskbarPreviewHideTimer) return;
    clearTimeout(this._taskbarPreviewHideTimer);
    this._taskbarPreviewHideTimer = 0;
  }

  _hideTaskbarPreviewSoon() {
    this._clearTaskbarPreviewHideTimer();
    this._taskbarPreviewHideTimer = setTimeout(() => this._hideTaskbarPreview(), 180);
  }

  _hideTaskbarPreview() {
    this._clearTaskbarPreviewHideTimer();
    if (this._taskbarPreview) this._taskbarPreview.hidden = true;
  }

  _taskbarBadgeCount(entry) {
    const raw = entry?.badge_count ?? entry?.unread_count ?? entry?.notification_count ?? entry?.badgeCount ?? 0;
    const count = Number(raw) || 0;
    return Math.max(0, Math.min(99, Math.round(count)));
  }

  _taskbarNeedsAttention(entry) {
    return !!(entry?.attention || entry?.needs_attention || entry?.urgent || this._taskbarBadgeCount(entry) > 0);
  }

  _decorateTaskbarAttention(item, entry) {
    const count = this._taskbarBadgeCount(entry);
    const attention = this._taskbarNeedsAttention(entry);
    item.dataset.taskbarAttention = attention ? 'true' : 'false';
    if (attention) item.classList.add('attention');
    if (count > 0) this._appendTaskbarBadge(item, count);
  }

  _appendTaskbarBadge(item, count) {
    const badge = document.createElement('span');
    badge.className = 'wm-taskbar-badge';
    badge.dataset.taskbarBadge = String(count);
    badge.setAttribute('aria-hidden', 'true');
    badge.textContent = count > 9 ? '9+' : String(count);
    item.appendChild(badge);
  }

  _makeRoundIcon(baseClass, raw) {
    const icon = document.createElement('span');
    icon.className = `${baseClass} wm-round-icon`;
    const value = String(raw || 'S');
    icon.dataset.iconSource = value;
    icon.dataset.iconMask = this._iconMaskMode || 'circle';
    if (this._isImageIcon(value)) {
      icon.classList.add('wm-icon-normalized-square');
      icon.dataset.iconNormalized = this._iconMaskMode === 'square' ? 'square-preserved' : this._iconMaskMode === 'rounded' ? 'square-to-rounded' : 'square-to-round';
      const img = document.createElement('img');
      img.className = 'wm-icon-image';
      img.src = value;
      img.alt = '';
      icon.appendChild(img);
    } else {
      icon.dataset.iconNormalized = 'glyph-to-round';
      const glyph = document.createElement('span');
      glyph.className = 'wm-icon-glyph';
      glyph.textContent = value.trim().slice(0, 1).toUpperCase() || 'S';
      icon.appendChild(glyph);
    }
    return icon;
  }

  _ensureDesktopWidgets() {
    if (this._desktopWidgets && this._desktopWidgets.isConnected) return this._desktopWidgets;
    if (!this.desktop) return null;
    const shelf = document.createElement('section');
    shelf.className = 'wm-desktop-widgets';
    shelf.setAttribute('aria-label', 'Desktop widgets');
    shelf.addEventListener('pointerdown', (event) => event.stopPropagation());
    shelf.addEventListener('mousedown', (event) => event.stopPropagation());
    shelf.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const button = target?.closest('.wm-widget-control');
      if (!button || !shelf.contains(button)) return;
      const widget = button.closest('.wm-desktop-widget');
      if (!widget) return;
      const action = button.dataset.widgetControl || '';
      if (action === 'remove') this._removeDesktopWidget(widget);
      if (action === 'pin') this._pinDesktopWidget(widget);
    });
    shelf.appendChild(this._makeDesktopWidget('wm-widget-clock', 'Local', this._desktopClockLabel(), 'Clock'));
    shelf.appendChild(this._makeDesktopWidget('wm-widget-system', 'Motion', this._normalizeMotionPreference(this._readMotionPreference()), 'Settings'));
    shelf.appendChild(this._makeDesktopWidget('wm-widget-workspace', 'Workspace', 'Simple WM', 'Active'));
    this.desktop.appendChild(shelf);
    this._desktopWidgets = shelf;
    return shelf;
  }

  _makeDesktopWidget(kind, label, value, meta) {
    const widget = document.createElement('article');
    widget.className = `wm-desktop-widget ${kind}`;
    widget.setAttribute('role', 'group');
    widget.setAttribute('aria-label', `${label} widget`);
    widget.dataset.widgetKind = kind.replace(/^wm-widget-/, '');
    const labelEl = document.createElement('span');
    labelEl.className = 'wm-desktop-widget-label';
    labelEl.textContent = label;
    const valueEl = document.createElement('strong');
    valueEl.className = 'wm-desktop-widget-value';
    valueEl.textContent = value;
    const metaEl = document.createElement('span');
    metaEl.className = 'wm-desktop-widget-meta';
    metaEl.textContent = meta;
    widget.appendChild(labelEl);
    widget.appendChild(valueEl);
    widget.appendChild(metaEl);
    widget.appendChild(this._makeDesktopWidgetControls());
    return widget;
  }

  _makeDesktopWidgetControls() {
    const controls = document.createElement('span');
    controls.className = 'wm-widget-controls';
    controls.setAttribute('role', 'group');
    controls.setAttribute('aria-label', 'Widget controls');
    controls.appendChild(this._makeWidgetControlButton('pin', 'Pin widget', 'P'));
    controls.appendChild(this._makeWidgetControlButton('remove', 'Remove widget', 'X'));
    return controls;
  }

  _makeWidgetControlButton(action, label, glyph) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-widget-control';
    button.dataset.widgetControl = action;
    button.setAttribute('aria-label', label);
    button.textContent = glyph;
    return button;
  }

  _pinDesktopWidget(widget) {
    widget.classList.toggle('pinned');
    this._markDesktopWidgetAction(widget, widget.classList.contains('pinned') ? 'pin' : 'unpin');
    this._sendWindowCmd('widget_pin', {
      widget_kind: widget.dataset.widgetKind || 'widget',
      pinned: widget.classList.contains('pinned')
    });
    return widget.classList.contains('pinned');
  }

  _removeDesktopWidget(widget) {
    const kind = widget.dataset.widgetKind || 'widget';
    widget.classList.add('removing');
    this._markDesktopWidgetAction(widget, 'remove');
    this._sendWindowCmd('widget_remove', { widget_kind: kind });
    window.setTimeout(() => {
      if (widget.isConnected) widget.remove();
    }, this._normalizeMotionPreference(this._readMotionPreference()) === 'off' ? 0 : 160);
    return true;
  }

  _markDesktopWidgetAction(widget, action = '') {
    if (!widget) return;
    const kind = String(action || 'update').trim() || 'update';
    const prior = this._widgetActionFeedbackTimers.get(widget);
    if (prior) window.clearTimeout(prior);
    widget.classList.remove('action-feedback');
    void widget.offsetWidth;
    widget.classList.add('action-feedback');
    widget.dataset.widgetFeedback = kind;
    const timer = window.setTimeout(() => {
      widget.classList.remove('action-feedback');
      if (widget.dataset.widgetFeedback === kind) delete widget.dataset.widgetFeedback;
      this._widgetActionFeedbackTimers.delete(widget);
    }, 520);
    this._widgetActionFeedbackTimers.set(widget, timer);
  }

  _desktopClockLabel() {
    try {
      return new Intl.DateTimeFormat([], { hour: '2-digit', minute: '2-digit' }).format(new Date());
    } catch (_) {
      return '09:41';
    }
  }

  _toggleDesktopWidgets() {
    const shelf = this._ensureDesktopWidgets();
    if (!shelf) return false;
    shelf.classList.toggle('collapsed');
    return !shelf.classList.contains('collapsed');
  }

  _ensureDesktopItems() {
    if (this._desktopItems && this._desktopItems.isConnected) return this._desktopItems;
    if (!this.desktop) return null;
    const shelf = document.createElement('section');
    shelf.className = 'wm-desktop-items';
    shelf.setAttribute('aria-label', 'Desktop items');
    shelf.addEventListener('pointerdown', (event) => event.stopPropagation());
    shelf.addEventListener('mousedown', (event) => event.stopPropagation());
    shelf.addEventListener('click', (event) => {
      const target = event.target && event.target.closest ? event.target : null;
      const item = target ? target.closest('.wm-desktop-item') : null;
      if (item && shelf.contains(item)) {
        this._activateDesktopItem(item.dataset.desktopItem || '');
        return;
      }
      const drop = target ? target.closest('.wm-desktop-drop-target') : null;
      if (drop && shelf.contains(drop)) this._activateDesktopDropTarget();
    });
    shelf.addEventListener('keydown', (event) => {
      if (event.key !== 'Enter' && event.key !== ' ') return;
      const target = event.target && event.target.closest ? event.target : null;
      const item = target ? target.closest('.wm-desktop-item') : null;
      const drop = target ? target.closest('.wm-desktop-drop-target') : null;
      if ((!item || !shelf.contains(item)) && (!drop || !shelf.contains(drop))) return;
      event.preventDefault();
      if (item) this._activateDesktopItem(item.dataset.desktopItem || '');
      else this._activateDesktopDropTarget();
    });
    shelf.appendChild(this._makeDesktopItem('report', 'Quality report', 'Markdown', 'R'));
    shelf.appendChild(this._makeDesktopItem('screenshot', 'Screenshot', 'PNG image', 'S'));
    shelf.appendChild(this._makeDesktopDropTarget());
    this.desktop.appendChild(shelf);
    this._desktopItems = shelf;
    return shelf;
  }

  _makeDesktopItem(id, label, meta, icon) {
    const item = document.createElement('button');
    item.type = 'button';
    item.className = 'wm-desktop-item';
    item.dataset.desktopItem = id;
    item.setAttribute('aria-label', `${label}, ${meta}`);
    item.appendChild(this._makeRoundIcon('wm-desktop-item-icon', icon || label));
    const name = document.createElement('span');
    name.className = 'wm-desktop-item-label';
    name.textContent = label;
    item.appendChild(name);
    const detail = document.createElement('span');
    detail.className = 'wm-desktop-item-meta';
    detail.textContent = meta;
    item.appendChild(detail);
    return item;
  }

  _makeDesktopDropTarget() {
    const target = document.createElement('div');
    target.className = 'wm-desktop-drop-target';
    target.dataset.dropTarget = 'desktop';
    target.setAttribute('role', 'button');
    target.setAttribute('aria-label', 'Drop files on desktop');
    target.tabIndex = 0;
    target.appendChild(this._makeRoundIcon('wm-desktop-drop-icon', '+'));
    const label = document.createElement('span');
    label.className = 'wm-desktop-drop-label';
    label.textContent = 'Drop files';
    target.appendChild(label);
    return target;
  }

  _activateDesktopItem(itemId) {
    const id = String(itemId || 'report');
    this._markDesktopItemFeedback('open', id);
    this._sendWindowCmd('desktop_item_open', { desktop_item: id });
  }

  _activateDesktopDropTarget() {
    this._markDesktopItemFeedback('drop', 'desktop');
    this._sendWindowCmd('desktop_drop_target', { drop_target: 'desktop' });
  }

  _markDesktopItemFeedback(action, targetId) {
    if (!this._desktopItems || !this._desktopItems.isConnected || !this._feedbackAllows('standard')) return;
    const shelf = this._desktopItems;
    const kind = String(action || 'open');
    const id = String(targetId || '');
    window.clearTimeout(this._desktopItemsFeedbackTimer);
    this._clearDesktopItemFeedback();
    shelf.dataset.desktopFeedback = kind;
    shelf.dataset.desktopFeedbackId = id;
    shelf.classList.add('action-feedback');
    const safeId = typeof CSS !== 'undefined' && CSS.escape ? CSS.escape(id) : id.replace(/["\\]/g, '\\$&');
    const selector = kind === 'drop'
      ? `.wm-desktop-drop-target[data-drop-target="${safeId}"]`
      : `.wm-desktop-item[data-desktop-item="${safeId}"]`;
    const target = shelf.querySelector(selector);
    if (target) {
      target.dataset.desktopFeedback = kind;
      target.classList.add('action-feedback');
      const icon = target.querySelector('.wm-desktop-item-icon, .wm-desktop-drop-icon');
      if (icon) icon.classList.add('action-feedback');
    }
    this._desktopItemsFeedbackTimer = window.setTimeout(() => this._clearDesktopItemFeedback(), 560);
  }

  _clearDesktopItemFeedback() {
    if (!this._desktopItems) return;
    window.clearTimeout(this._desktopItemsFeedbackTimer);
    this._desktopItemsFeedbackTimer = 0;
    delete this._desktopItems.dataset.desktopFeedback;
    delete this._desktopItems.dataset.desktopFeedbackId;
    this._desktopItems.classList.remove('action-feedback');
    this._desktopItems.querySelectorAll('.action-feedback[data-desktop-feedback], .wm-desktop-item-icon.action-feedback, .wm-desktop-drop-icon.action-feedback').forEach((node) => {
      node.classList.remove('action-feedback');
      if (node.dataset && node.dataset.desktopFeedback) delete node.dataset.desktopFeedback;
    });
  }

  _toggleDesktopItems() {
    const shelf = this._ensureDesktopItems();
    if (!shelf) return false;
    shelf.classList.toggle('collapsed');
    return !shelf.classList.contains('collapsed');
  }

  _ensureWindowOverview() {
    if (this._windowOverview && this._windowOverview.isConnected) return this._windowOverview;
    const overview = document.createElement('aside');
    overview.className = 'wm-window-overview';
    overview.hidden = true;
    overview.setAttribute('role', 'dialog');
    overview.setAttribute('aria-label', 'Window overview');
    overview.addEventListener('pointerdown', (event) => event.stopPropagation());
    overview.addEventListener('mousedown', (event) => event.stopPropagation());
    overview.addEventListener('input', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const search = target?.closest('.wm-overview-search');
      if (!search || !overview.contains(search)) return;
      this._overviewSearchQuery = String(search.value || '');
      this._renderWindowOverview();
    });
    overview.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const card = target?.closest('.wm-overview-card');
      if (!card || !overview.contains(card)) return;
      this._focusWindowById(card.dataset.windowIdHint || '');
      this._toggleWindowOverview(false);
    });
    document.body.appendChild(overview);
    this._windowOverview = overview;
    return overview;
  }

  _toggleWindowOverview(open = null) {
    const overview = this._ensureWindowOverview();
    const shouldOpen = open == null ? overview.hidden : open;
    overview.hidden = !shouldOpen;
    if (shouldOpen) {
      this._overviewSearchQuery = '';
      this._renderWindowOverview();
      overview.querySelector('.wm-overview-search')?.focus();
    }
    return shouldOpen;
  }

  _renderWindowOverview() {
    const overview = this._ensureWindowOverview();
    overview.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-overview-title';
    title.textContent = 'Window overview';
    overview.appendChild(title);
    const search = document.createElement('input');
    search.className = 'wm-overview-search';
    search.type = 'search';
    search.value = this._overviewSearchQuery;
    search.placeholder = 'Search windows';
    search.setAttribute('aria-label', 'Search window overview');
    overview.appendChild(search);
    const grid = document.createElement('div');
    grid.className = 'wm-overview-grid';
    const windows = this._filteredOverviewWindows();
    for (const win of windows) grid.appendChild(this._makeOverviewCard(win));
    if (!windows.length) {
      const empty = document.createElement('div');
      empty.className = 'wm-overview-empty';
      empty.textContent = this._overviewSearchQuery.trim() ? 'No matching windows' : 'No open windows';
      grid.appendChild(empty);
    }
    overview.appendChild(grid);
  }

  _filteredOverviewWindows() {
    const query = this._overviewSearchQuery.trim().toLowerCase();
    const windows = this._overviewWindows();
    if (!query) return windows;
    return windows.filter((win) => `${win.title || ''} ${win.id || ''} ${win.minimized ? 'minimized' : ''} ${win.active ? 'active' : 'open'}`.toLowerCase().includes(query));
  }

  _overviewWindows() {
    const items = [];
    if (this.transport === 'electron-ipc' && this._electronWindows.size) {
      for (const [windowId, entry] of this._electronWindows.entries()) {
        items.push({
          id: windowId,
          title: entry.titleText || windowId,
          active: windowId === this._electronActiveWindowId,
          minimized: !!entry.minimized
        });
      }
      return items;
    }
    if (!this.desktop) return items;
    for (const win of this.desktop.querySelectorAll('.wm-window')) {
      const id = win.dataset.surfaceId || win.dataset.canonicalId || '';
      if (!id) continue;
      const title = win.querySelector('.wm-title')?.textContent || id;
      items.push({
        id,
        title,
        active: win.classList.contains('focused'),
        minimized: win.classList.contains('minimized')
      });
    }
    return items;
  }

  _makeOverviewCard(win) {
    const card = document.createElement('button');
    card.type = 'button';
    card.className = 'wm-overview-card' + (win.active ? ' active' : '') + (win.minimized ? ' minimized' : '');
    card.dataset.windowIdHint = win.id;
    card.setAttribute('aria-label', `${win.minimized ? 'Restore' : 'Focus'} ${win.title}`);
    card.appendChild(this._makeRoundIcon('wm-overview-icon', win.title || win.id));
    const title = document.createElement('span');
    title.className = 'wm-overview-card-title';
    title.textContent = win.title || win.id;
    card.appendChild(title);
    const meta = document.createElement('span');
    meta.className = 'wm-overview-card-meta';
    meta.textContent = win.minimized ? 'Minimized' : (win.active ? 'Active' : 'Open');
    card.appendChild(meta);
    return card;
  }

  _focusWindowById(windowId) {
    const id = String(windowId || '');
    if (!id) return;
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(id);
    if (isElectronWindow) this._electronFocusWindow(id);
    this._sendWindowCmd('focus', {
      window_id_hint: id,
      ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
    });
  }

  _ensureWindowSwitcher() {
    if (this._windowSwitcher && this._windowSwitcher.isConnected) return this._windowSwitcher;
    const switcher = document.createElement('aside');
    switcher.className = 'wm-window-switcher';
    switcher.hidden = true;
    switcher.setAttribute('role', 'dialog');
    switcher.setAttribute('aria-label', 'Window switcher');
    switcher.dataset.switcherShortcut = 'Meta Tab';
    switcher.addEventListener('pointerdown', (event) => event.stopPropagation());
    switcher.addEventListener('mousedown', (event) => event.stopPropagation());
    switcher.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const card = target?.closest('.wm-window-switcher-card');
      if (!card || !switcher.contains(card)) return;
      const index = Number(card.dataset.switcherIndex || 0);
      this._windowSwitcherActiveIndex = index;
      this._activateWindowSwitcherSelection();
    });
    switcher.addEventListener('keydown', (event) => this._handleWindowSwitcherKeydown(event));
    document.body.appendChild(switcher);
    this._windowSwitcher = switcher;
    return switcher;
  }

  _toggleWindowSwitcher(open = null) {
    const switcher = this._ensureWindowSwitcher();
    const shouldOpen = open == null ? switcher.hidden : open;
    switcher.hidden = !shouldOpen;
    if (shouldOpen) {
      this._renderWindowSwitcher();
      this._focusWindowSwitcherActiveCard();
    } else {
      if (this._windowSwitcherActivationTimer) clearTimeout(this._windowSwitcherActivationTimer);
      this._windowSwitcherActivationTimer = 0;
      this._clearWindowSwitcherActivationFeedback();
    }
    return shouldOpen;
  }

  _renderWindowSwitcher() {
    const switcher = this._ensureWindowSwitcher();
    switcher.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-window-switcher-title';
    title.textContent = 'Windows';
    switcher.appendChild(title);
    const list = document.createElement('div');
    list.className = 'wm-window-switcher-list';
    list.setAttribute('role', 'listbox');
    list.setAttribute('aria-label', 'Open windows');
    const windows = this._windowSwitcherWindows();
    this._windowSwitcherItems = windows;
    this._windowSwitcherActiveIndex = Math.min(this._windowSwitcherActiveIndex, Math.max(windows.length - 1, 0));
    if (windows.length) list.setAttribute('aria-activedescendant', 'wm-window-switcher-card-' + this._windowSwitcherActiveIndex);
    for (const [index, win] of windows.entries()) list.appendChild(this._makeWindowSwitcherCard(win, index));
    if (!windows.length) {
      const empty = document.createElement('div');
      empty.className = 'wm-window-switcher-empty';
      empty.textContent = 'No windows';
      list.appendChild(empty);
    }
    switcher.appendChild(list);
  }

  _windowSwitcherWindows() {
    const windows = this._overviewWindows();
    if (windows.length) return windows;
    return [
      { id: 'simple.ide', title: 'Simple IDE', active: true, minimized: false },
      { id: 'simple.browser', title: 'Browser', active: false, minimized: false },
      { id: 'simple.terminal', title: 'Terminal', active: false, minimized: true }
    ];
  }

  _makeWindowSwitcherCard(win, index) {
    const card = document.createElement('button');
    card.type = 'button';
    card.id = 'wm-window-switcher-card-' + index;
    card.className = 'wm-window-switcher-card' + (index === this._windowSwitcherActiveIndex ? ' active' : '') + (win.minimized ? ' minimized' : '');
    card.dataset.switcherIndex = String(index);
    card.dataset.switchWindow = win.id;
    card.setAttribute('role', 'option');
    card.setAttribute('aria-selected', index === this._windowSwitcherActiveIndex ? 'true' : 'false');
    card.setAttribute('aria-label', `${win.minimized ? 'Restore' : 'Focus'} ${win.title}`);
    card.appendChild(this._makeRoundIcon('wm-switcher-icon', win.title || win.id));
    const body = document.createElement('span');
    body.className = 'wm-switcher-body';
    const title = document.createElement('strong');
    title.className = 'wm-switcher-title';
    title.textContent = win.title || win.id;
    body.appendChild(title);
    const meta = document.createElement('span');
    meta.className = 'wm-switcher-meta';
    meta.textContent = win.minimized ? 'Minimized' : (win.active ? 'Active' : 'Open');
    body.appendChild(meta);
    card.appendChild(body);
    return card;
  }

  _handleWindowSwitcherKeydown(event) {
    if (!this._windowSwitcher || this._windowSwitcher.hidden) return;
    if (event.key === 'Escape') {
      event.preventDefault();
      this._toggleWindowSwitcher(false);
      return;
    }
    if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      this._activateWindowSwitcherSelection();
      return;
    }
    if (event.key === 'Tab') {
      event.preventDefault();
      this._moveWindowSwitcherSelection(event.shiftKey ? -1 : 1);
      return;
    }
    if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
      event.preventDefault();
      this._moveWindowSwitcherSelection(1);
      return;
    }
    if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
      event.preventDefault();
      this._moveWindowSwitcherSelection(-1);
    }
  }

  _moveWindowSwitcherSelection(delta) {
    if (!this._windowSwitcher || this._windowSwitcher.hidden) return;
    const count = this._windowSwitcherItems.length;
    if (!count) return;
    this._windowSwitcherActiveIndex = (this._windowSwitcherActiveIndex + delta + count) % count;
    this._renderWindowSwitcher();
    this._focusWindowSwitcherActiveCard();
  }

  _focusWindowSwitcherActiveCard() {
    if (!this._windowSwitcher || this._windowSwitcher.hidden) return;
    const card = this._windowSwitcher.querySelector('.wm-window-switcher-card.active');
    if (card) card.focus({ preventScroll: true });
  }

  _activateWindowSwitcherSelection() {
    if (!this._windowSwitcher || this._windowSwitcher.hidden) return;
    const win = this._windowSwitcherItems[this._windowSwitcherActiveIndex];
    if (!win) return;
    if (!this._feedbackAllows('standard')) {
      this._focusAndCloseWindowSwitcher(win);
      return;
    }
    this._markWindowSwitcherActivationFeedback(win.id);
    if (this._windowSwitcherActivationTimer) clearTimeout(this._windowSwitcherActivationTimer);
    this._windowSwitcherActivationTimer = setTimeout(() => {
      this._windowSwitcherActivationTimer = 0;
      this._focusAndCloseWindowSwitcher(win);
    }, 160);
  }

  _markWindowSwitcherActivationFeedback(windowId) {
    if (!this._windowSwitcher || !this._windowSwitcher.isConnected) return;
    const id = String(windowId || '');
    if (!id) return;
    const switcher = this._windowSwitcher;
    this._clearWindowSwitcherActivationFeedback();
    const card = switcher.querySelector(`.wm-window-switcher-card[data-switch-window="${id}"]`);
    switcher.dataset.switcherFeedback = 'activate';
    switcher.dataset.switcherFeedbackWindow = id;
    if (!card) return;
    card.classList.remove('action-feedback');
    void card.offsetWidth;
    card.classList.add('action-feedback');
    card.dataset.switcherFeedback = 'activate';
  }

  _clearWindowSwitcherActivationFeedback() {
    if (!this._windowSwitcher || !this._windowSwitcher.isConnected) return;
    const switcher = this._windowSwitcher;
    delete switcher.dataset.switcherFeedback;
    delete switcher.dataset.switcherFeedbackWindow;
    const cards = switcher.querySelectorAll('.wm-window-switcher-card.action-feedback');
    cards.forEach((card) => {
      card.classList.remove('action-feedback');
      delete card.dataset.switcherFeedback;
    });
  }

  _focusAndCloseWindowSwitcher(win) {
    if (!win) return;
    this._focusWindowById(win.id);
    this._toggleWindowSwitcher(false);
  }

  _ensureStageRail() {
    if (this._stageRail && this._stageRail.isConnected) return this._stageRail;
    const rail = document.createElement('aside');
    rail.className = 'wm-stage-rail';
    rail.hidden = true;
    rail.setAttribute('role', 'dialog');
    rail.setAttribute('aria-label', 'Window stage rail');
    rail.addEventListener('pointerdown', (event) => event.stopPropagation());
    rail.addEventListener('mousedown', (event) => event.stopPropagation());
    rail.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const action = target?.closest('[data-stage-action]');
      if (action && rail.contains(action)) {
        this._stageRailActiveIndex = Number(action.closest('.wm-stage-rail-item')?.dataset.stageIndex || '0') || 0;
        this._activateStageRailAction(action.dataset.stageAction || '', action.closest('.wm-stage-rail-item')?.dataset.windowIdHint || '');
        return;
      }
      const item = target?.closest('.wm-stage-rail-focus');
      if (!item || !rail.contains(item)) return;
      const row = item.closest('.wm-stage-rail-item');
      this._stageRailActiveIndex = Number(row?.dataset.stageIndex || '0') || 0;
      const windowId = row?.dataset.windowIdHint || '';
      if (windowId) this._focusWindowById(windowId);
    });
    rail.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowDown' || event.key === 'ArrowRight') {
        event.preventDefault();
        this._moveStageRailSelection(1);
      } else if (event.key === 'ArrowUp' || event.key === 'ArrowLeft') {
        event.preventDefault();
        this._moveStageRailSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._moveStageRailSelection(-999);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._moveStageRailSelection(999);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateStageRailSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleStageRail(false);
      }
    });
    document.body.appendChild(rail);
    this._stageRail = rail;
    return rail;
  }

  _toggleStageRail(open = null) {
    const rail = this._ensureStageRail();
    const shouldOpen = open == null ? rail.hidden : open;
    rail.hidden = !shouldOpen;
    if (shouldOpen) this._renderStageRail();
    return shouldOpen;
  }

  _renderStageRail() {
    const rail = this._ensureStageRail();
    rail.innerHTML = '';
    const windows = this._overviewWindows().slice(0, 5);
    const activeIndex = windows.findIndex((win) => win.active);
    if (activeIndex >= 0) this._stageRailActiveIndex = activeIndex;
    if (this._stageRailActiveIndex >= windows.length) this._stageRailActiveIndex = Math.max(0, windows.length - 1);
    rail.setAttribute('aria-activedescendant', `wm-stage-rail-item-${this._stageRailActiveIndex}`);
    rail.dataset.stageActiveIndex = String(this._stageRailActiveIndex);
    const title = document.createElement('div');
    title.className = 'wm-stage-rail-title';
    title.textContent = 'Stage';
    rail.appendChild(title);
    windows.forEach((win, index) => rail.appendChild(this._makeStageRailItem(win, index)));
    if (!windows.length) {
      const empty = document.createElement('div');
      empty.className = 'wm-stage-rail-empty';
      empty.textContent = 'No windows';
      rail.appendChild(empty);
    }
  }

  _makeStageRailItem(win, index) {
    const item = document.createElement('div');
    const active = index === this._stageRailActiveIndex;
    item.id = `wm-stage-rail-item-${index}`;
    item.className = 'wm-stage-rail-item' + (active ? ' active' : '') + (win.minimized ? ' minimized' : '');
    item.dataset.windowIdHint = win.id;
    item.dataset.stageIndex = String(index);
    item.setAttribute('role', 'option');
    item.setAttribute('aria-selected', active ? 'true' : 'false');
    const focus = document.createElement('button');
    focus.type = 'button';
    focus.className = 'wm-stage-rail-focus';
    focus.tabIndex = active ? 0 : -1;
    focus.setAttribute('aria-label', `${win.minimized ? 'Restore' : 'Focus'} ${win.title}`);
    focus.appendChild(this._makeRoundIcon('wm-stage-rail-icon', win.title || win.id));
    const label = document.createElement('span');
    label.className = 'wm-stage-rail-label';
    label.textContent = win.title || win.id;
    focus.appendChild(label);
    item.appendChild(focus);
    const actions = document.createElement('span');
    actions.className = 'wm-stage-rail-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', `${win.title || win.id} stage actions`);
    actions.appendChild(this._makeStageRailAction('minimize', 'Minimize', '-'));
    actions.appendChild(this._makeStageRailAction('close', 'Close', 'x'));
    item.appendChild(actions);
    return item;
  }

  _makeStageRailAction(action, label, glyph) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-stage-rail-action';
    button.dataset.stageAction = action;
    button.setAttribute('aria-label', label);
    button.textContent = glyph;
    return button;
  }

  _moveStageRailSelection(delta) {
    const rail = this._ensureStageRail();
    const items = Array.from(rail.querySelectorAll('.wm-stage-rail-item'));
    if (!items.length) return;
    const max = items.length - 1;
    this._stageRailActiveIndex = Math.max(0, Math.min(max, this._stageRailActiveIndex + delta));
    this._syncStageRailSelection(true);
  }

  _syncStageRailSelection(shouldFocus = true) {
    const rail = this._ensureStageRail();
    const items = Array.from(rail.querySelectorAll('.wm-stage-rail-item'));
    if (!items.length) return;
    const activeIndex = Math.max(0, Math.min(items.length - 1, this._stageRailActiveIndex));
    this._stageRailActiveIndex = activeIndex;
    rail.setAttribute('aria-activedescendant', `wm-stage-rail-item-${activeIndex}`);
    rail.dataset.stageActiveIndex = String(activeIndex);
    items.forEach((item, index) => {
      const active = index === activeIndex;
      item.classList.toggle('active', active);
      item.setAttribute('aria-selected', active ? 'true' : 'false');
      const focus = item.querySelector('.wm-stage-rail-focus');
      if (focus) {
        focus.tabIndex = active ? 0 : -1;
        if (active && shouldFocus) focus.focus();
      }
    });
  }

  _activateStageRailSelection() {
    const rail = this._ensureStageRail();
    const item = rail.querySelector(`.wm-stage-rail-item[data-stage-index="${this._stageRailActiveIndex}"]`);
    const windowId = item?.dataset.windowIdHint || '';
    if (windowId) this._focusWindowById(windowId);
  }

  _activateStageRailAction(action, windowId) {
    const id = String(windowId || '');
    if (!id) return;
    if (action === 'minimize' || action === 'close') {
      this._sendWindowCmd(action, { window_id_hint: id });
      if (action === 'close') this._renderStageRail();
    }
  }

  _ensureWorkspaceSwitcher() {
    if (this._workspaceSwitcher && this._workspaceSwitcher.isConnected) return this._workspaceSwitcher;
    const switcher = document.createElement('aside');
    switcher.className = 'wm-workspace-switcher';
    switcher.hidden = true;
    switcher.setAttribute('role', 'dialog');
    switcher.setAttribute('aria-label', 'Workspace switcher');
    switcher.addEventListener('pointerdown', (event) => event.stopPropagation());
    switcher.addEventListener('mousedown', (event) => event.stopPropagation());
    switcher.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const action = target?.closest('[data-workspace-action]');
      if (action && switcher.contains(action)) {
        this._workspaceSwitcherActiveIndex = Number(action.closest('.wm-workspace-card')?.dataset.workspaceIndex || '0') || 0;
        this._activateWorkspaceAction(action.dataset.workspaceAction || '', action.closest('.wm-workspace-card')?.dataset.workspaceId || 'main');
        return;
      }
      const item = target?.closest('.wm-workspace-switch');
      if (!item || !switcher.contains(item)) return;
      const card = item.closest('.wm-workspace-card');
      this._workspaceSwitcherActiveIndex = Number(card?.dataset.workspaceIndex || '0') || 0;
      this._activateWorkspaceSwitcherSelection();
    });
    switcher.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveWorkspaceSwitcherSelection(1);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveWorkspaceSwitcherSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._moveWorkspaceSwitcherSelection(-999);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._moveWorkspaceSwitcherSelection(999);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateWorkspaceSwitcherSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleWorkspaceSwitcher(false);
      }
    });
    document.body.appendChild(switcher);
    this._workspaceSwitcher = switcher;
    return switcher;
  }

  _toggleWorkspaceSwitcher(open = null) {
    const switcher = this._ensureWorkspaceSwitcher();
    const shouldOpen = open == null ? switcher.hidden : open;
    switcher.hidden = !shouldOpen;
    if (shouldOpen) this._renderWorkspaceSwitcher();
    if (!shouldOpen) {
      if (this._workspaceSwitcherActivationTimer) window.clearTimeout(this._workspaceSwitcherActivationTimer);
      this._workspaceSwitcherActivationTimer = 0;
      this._clearWorkspaceSwitcherActivationFeedback();
    }
    return shouldOpen;
  }

  _renderWorkspaceSwitcher() {
    const switcher = this._ensureWorkspaceSwitcher();
    switcher.innerHTML = '';
    const items = this._workspaceItems();
    const activeIndex = items.findIndex((workspace) => workspace.id === this._activeWorkspaceId);
    if (activeIndex >= 0) this._workspaceSwitcherActiveIndex = activeIndex;
    if (this._workspaceSwitcherActiveIndex >= items.length) this._workspaceSwitcherActiveIndex = Math.max(0, items.length - 1);
    switcher.setAttribute('aria-activedescendant', `wm-workspace-card-${this._workspaceSwitcherActiveIndex}`);
    switcher.dataset.workspaceActiveIndex = String(this._workspaceSwitcherActiveIndex);
    const title = document.createElement('div');
    title.className = 'wm-workspace-title';
    title.textContent = 'Workspaces';
    switcher.appendChild(title);
    const grid = document.createElement('div');
    grid.className = 'wm-workspace-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Available workspaces');
    for (let index = 0; index < items.length; index += 1) grid.appendChild(this._makeWorkspaceCard(items[index], index));
    switcher.appendChild(grid);
  }

  _workspaceItems() {
    if (this._customWorkspaces) return this._customWorkspaces;
    return [
      { id: 'main', label: 'Main', meta: 'Windows and editor' },
      { id: 'focus', label: 'Focus', meta: 'Quiet workspace' },
      { id: 'review', label: 'Review', meta: 'Docs and previews' }
    ];
  }

  _workspaceIndex(workspaceId) {
    const items = this._workspaceItems();
    const index = items.findIndex((workspace) => workspace.id === workspaceId);
    return index >= 0 ? index : 0;
  }

  _makeWorkspaceCard(workspace, index) {
    const card = document.createElement('div');
    const active = index === this._workspaceSwitcherActiveIndex;
    card.id = `wm-workspace-card-${index}`;
    card.className = 'wm-workspace-card' + (active ? ' active' : '');
    card.dataset.workspaceId = workspace.id;
    card.dataset.workspaceIndex = String(index);
    card.setAttribute('role', 'option');
    card.setAttribute('aria-selected', active ? 'true' : 'false');
    const switchButton = document.createElement('button');
    switchButton.type = 'button';
    switchButton.className = 'wm-workspace-switch';
    switchButton.tabIndex = active ? 0 : -1;
    switchButton.setAttribute('aria-label', `Switch to ${workspace.label} workspace`);
    switchButton.appendChild(this._makeRoundIcon('wm-workspace-icon', workspace.label));
    const label = document.createElement('span');
    label.className = 'wm-workspace-label';
    label.textContent = workspace.label;
    switchButton.appendChild(label);
    const meta = document.createElement('span');
    meta.className = 'wm-workspace-meta';
    meta.textContent = workspace.meta;
    switchButton.appendChild(meta);
    card.appendChild(switchButton);
    const actions = document.createElement('span');
    actions.className = 'wm-workspace-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', `${workspace.label} workspace actions`);
    actions.appendChild(this._makeWorkspaceAction('rename', 'Rename'));
    actions.appendChild(this._makeWorkspaceAction('duplicate', 'Duplicate'));
    actions.appendChild(this._makeWorkspaceAction('close', 'Close'));
    card.appendChild(actions);
    return card;
  }

  _makeWorkspaceAction(action, label) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-workspace-action';
    button.dataset.workspaceAction = action;
    button.textContent = label;
    return button;
  }

  _moveWorkspaceSwitcherSelection(delta) {
    const switcher = this._ensureWorkspaceSwitcher();
    const cards = Array.from(switcher.querySelectorAll('.wm-workspace-card'));
    if (!cards.length) return;
    const max = cards.length - 1;
    this._workspaceSwitcherActiveIndex = Math.max(0, Math.min(max, this._workspaceSwitcherActiveIndex + delta));
    this._syncWorkspaceSwitcherSelection(true);
  }

  _syncWorkspaceSwitcherSelection(shouldFocus = true) {
    const switcher = this._ensureWorkspaceSwitcher();
    const cards = Array.from(switcher.querySelectorAll('.wm-workspace-card'));
    if (!cards.length) return;
    const activeIndex = Math.max(0, Math.min(cards.length - 1, this._workspaceSwitcherActiveIndex));
    this._workspaceSwitcherActiveIndex = activeIndex;
    switcher.setAttribute('aria-activedescendant', `wm-workspace-card-${activeIndex}`);
    switcher.dataset.workspaceActiveIndex = String(activeIndex);
    cards.forEach((card, index) => {
      const active = index === activeIndex;
      card.classList.toggle('active', active);
      card.setAttribute('aria-selected', active ? 'true' : 'false');
      const button = card.querySelector('.wm-workspace-switch');
      if (button) {
        button.tabIndex = active ? 0 : -1;
        if (active && shouldFocus) button.focus();
      }
    });
  }

  _activateWorkspaceSwitcherSelection() {
    const switcher = this._ensureWorkspaceSwitcher();
    if (switcher.hidden) return;
    const card = switcher.querySelector(`.wm-workspace-card[data-workspace-index="${this._workspaceSwitcherActiveIndex}"]`);
    const workspaceId = card?.dataset.workspaceId || 'main';
    if (!this._feedbackAllows('standard')) {
      this._switchAndCloseWorkspaceSwitcher(workspaceId);
      return;
    }
    this._markWorkspaceSwitcherActivationFeedback(workspaceId);
    if (this._workspaceSwitcherActivationTimer) window.clearTimeout(this._workspaceSwitcherActivationTimer);
    this._workspaceSwitcherActivationTimer = window.setTimeout(() => {
      this._workspaceSwitcherActivationTimer = 0;
      this._switchAndCloseWorkspaceSwitcher(workspaceId);
    }, 160);
  }

  _markWorkspaceSwitcherActivationFeedback(workspaceId) {
    const switcher = this._ensureWorkspaceSwitcher();
    const id = String(workspaceId || 'main');
    this._clearWorkspaceSwitcherActivationFeedback();
    const card = switcher.querySelector(`.wm-workspace-card[data-workspace-id="${id}"]`);
    switcher.dataset.workspaceFeedback = 'activate';
    switcher.dataset.workspaceFeedbackId = id;
    if (!card) return;
    card.classList.remove('action-feedback');
    void card.offsetWidth;
    card.classList.add('action-feedback');
    card.dataset.workspaceFeedback = 'activate';
  }

  _clearWorkspaceSwitcherActivationFeedback() {
    if (!this._workspaceSwitcher || !this._workspaceSwitcher.isConnected) return;
    const switcher = this._workspaceSwitcher;
    delete switcher.dataset.workspaceFeedback;
    delete switcher.dataset.workspaceFeedbackId;
    const cards = switcher.querySelectorAll('.wm-workspace-card.action-feedback');
    cards.forEach((card) => {
      card.classList.remove('action-feedback');
      delete card.dataset.workspaceFeedback;
    });
  }

  _switchAndCloseWorkspaceSwitcher(workspaceId) {
    this._switchWorkspace(workspaceId);
    this._toggleWorkspaceSwitcher(false);
  }

  _activateWorkspaceAction(action, workspaceId) {
    const id = String(workspaceId || 'main');
    if (action === 'rename') {
      this._renameWorkspace(id);
      return;
    }
    if (action === 'duplicate') {
      this._duplicateWorkspace(id);
      return;
    }
    if (action === 'close') {
      this._closeWorkspace(id);
    }
  }

  _renameWorkspace(workspaceId) {
    const items = this._workspaceItems().map((workspace) => workspace.id === workspaceId ? { ...workspace, label: workspace.label + ' *', meta: 'Renamed workspace' } : workspace);
    this._customWorkspaces = items;
    this._sendWindowCmd('workspace_rename', { workspace_id: workspaceId });
    this._renderWorkspaceSwitcher();
  }

  _duplicateWorkspace(workspaceId) {
    const source = this._workspaceItems().find((workspace) => workspace.id === workspaceId);
    if (!source) return;
    const duplicate = { id: workspaceId + '-copy', label: source.label + ' Copy', meta: 'Duplicated workspace' };
    this._customWorkspaces = this._workspaceItems().concat([duplicate]);
    this._sendWindowCmd('workspace_duplicate', { workspace_id: workspaceId, duplicate_id: duplicate.id });
    this._renderWorkspaceSwitcher();
  }

  _closeWorkspace(workspaceId) {
    if (workspaceId === 'main') return;
    this._customWorkspaces = this._workspaceItems().filter((workspace) => workspace.id !== workspaceId);
    if (this._activeWorkspaceId === workspaceId) this._activeWorkspaceId = 'main';
    this._sendWindowCmd('workspace_close', { workspace_id: workspaceId });
    this._renderWorkspaceSwitcher();
  }

  _switchWorkspace(workspaceId) {
    const id = String(workspaceId || 'main');
    const previousId = this._activeWorkspaceId;
    this._activeWorkspaceId = id;
    document.documentElement.dataset.wmWorkspace = id;
    this._startWorkspaceTransition(previousId, id);
    this._sendWindowCmd('switch_workspace', { workspace_id: id });
    this._showSystemHud('Workspace', id, 1800);
  }

  _startWorkspaceTransition(previousId, nextId) {
    if (!this.desktop) return;
    const previousIndex = this._workspaceIndex(previousId);
    const nextIndex = this._workspaceIndex(nextId);
    const direction = nextIndex < previousIndex ? 'back' : nextIndex > previousIndex ? 'forward' : 'same';
    this.desktop.dataset.wmWorkspace = nextId;
    this.desktop.dataset.wmWorkspaceTransition = 'enter';
    this.desktop.dataset.wmWorkspaceDirection = direction;
    if (this._workspaceTransitionTimer) window.clearTimeout(this._workspaceTransitionTimer);
    this._workspaceTransitionTimer = window.setTimeout(() => {
      if (!this.desktop) return;
      this.desktop.dataset.wmWorkspaceTransition = 'idle';
      this.desktop.dataset.wmWorkspaceDirection = 'none';
    }, 260);
  }

  _ensureClipboardHistory() {
    if (this._clipboardHistory && this._clipboardHistory.isConnected) return this._clipboardHistory;
    const panel = document.createElement('aside');
    panel.className = 'wm-clipboard-history';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Clipboard history');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const action = target?.closest('[data-clipboard-action]');
      if (action && panel.contains(action)) {
        const item = action.closest('.wm-clipboard-item');
        const id = item?.dataset.clipboardId || '';
        if (item) this._clipboardHistoryActiveIndex = Number(item.dataset.clipboardIndex || '0') || 0;
        if (action.dataset.clipboardAction === 'paste') this._pasteClipboardItem(id);
        if (action.dataset.clipboardAction === 'pin') this._pinClipboardItem(id);
        if (action.dataset.clipboardAction === 'clear') this._clearClipboardHistory();
        if (action.dataset.clipboardAction === 'filter') this._setClipboardKindFilter(action.dataset.clipboardFilter || 'all');
        return;
      }
      const item = target?.closest('.wm-clipboard-item');
      if (!item || !panel.contains(item)) return;
      this._clipboardHistoryActiveIndex = Number(item.dataset.clipboardIndex || '0') || 0;
      this._pasteClipboardItem(item.dataset.clipboardId || '');
    });
    panel.addEventListener('keydown', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleClipboardHistory(false);
        return;
      }
      const searchHasFocus = Boolean(target?.closest('.wm-clipboard-search'));
      if (target?.closest('.wm-clipboard-filter, .wm-clipboard-action') && !searchHasFocus) return;
      if (event.key === 'ArrowDown' || event.key === 'ArrowRight') {
        event.preventDefault();
        this._moveClipboardHistorySelection(1);
      } else if (event.key === 'ArrowUp' || event.key === 'ArrowLeft') {
        event.preventDefault();
        this._moveClipboardHistorySelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._setClipboardHistorySelection(0);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._setClipboardHistorySelection(this._filteredClipboardItems().length - 1);
      } else if (!searchHasFocus && event.key === 'Enter') {
        event.preventDefault();
        this._activateClipboardHistorySelection('paste');
      } else if (!searchHasFocus && event.key === ' ') {
        event.preventDefault();
        this._activateClipboardHistorySelection('pin');
      }
    });
    panel.addEventListener('input', (event) => {
      const input = event.target?.closest?.('.wm-clipboard-search');
      if (!input || !panel.contains(input)) return;
      this._clipboardSearchQuery = input.value || '';
      this._clipboardHistoryActiveIndex = 0;
      this._renderClipboardHistory();
    });
    document.body.appendChild(panel);
    this._clipboardHistory = panel;
    return panel;
  }

  _toggleClipboardHistory(open = null) {
    const panel = this._ensureClipboardHistory();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderClipboardHistory();
    return shouldOpen;
  }

  _renderClipboardHistory() {
    const panel = this._ensureClipboardHistory();
    const items = this._filteredClipboardItems();
    if (this._clipboardHistoryActiveIndex >= items.length) this._clipboardHistoryActiveIndex = Math.max(0, items.length - 1);
    panel.innerHTML = '';
    if (items.length) {
      panel.setAttribute('aria-activedescendant', `wm-clipboard-item-${this._clipboardHistoryActiveIndex}`);
      panel.dataset.clipboardActiveIndex = String(this._clipboardHistoryActiveIndex);
    } else {
      panel.removeAttribute('aria-activedescendant');
      delete panel.dataset.clipboardActiveIndex;
    }
    const title = document.createElement('div');
    title.className = 'wm-clipboard-title';
    title.textContent = 'Clipboard';
    panel.appendChild(title);
    const search = document.createElement('input');
    search.className = 'wm-clipboard-search';
    search.type = 'search';
    search.value = this._clipboardSearchQuery;
    search.placeholder = 'Search clipboard';
    search.setAttribute('aria-label', 'Search clipboard history');
    panel.appendChild(search);
    const filters = document.createElement('div');
    filters.className = 'wm-clipboard-filters';
    filters.setAttribute('aria-label', 'Clipboard filters');
    for (const filter of this._clipboardKindFilters()) filters.appendChild(this._makeClipboardFilterButton(filter));
    panel.appendChild(filters);
    const list = document.createElement('div');
    list.className = 'wm-clipboard-list';
    list.setAttribute('role', 'listbox');
    list.setAttribute('aria-label', 'Clipboard entries');
    if (items.length) list.setAttribute('aria-activedescendant', `wm-clipboard-item-${this._clipboardHistoryActiveIndex}`);
    for (let index = 0; index < items.length; index += 1) list.appendChild(this._makeClipboardItem(items[index], index));
    if (!items.length) {
      const empty = document.createElement('div');
      empty.className = 'wm-clipboard-empty';
      empty.textContent = 'No matching clips';
      list.appendChild(empty);
    }
    panel.appendChild(list);
    const actions = document.createElement('div');
    actions.className = 'wm-clipboard-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', 'Clipboard controls');
    const clear = document.createElement('button');
    clear.type = 'button';
    clear.className = 'wm-clipboard-action';
    clear.dataset.clipboardAction = 'clear';
    clear.textContent = 'Clear';
    actions.appendChild(clear);
    panel.appendChild(actions);
  }

  _clipboardItems() {
    return [
      { id: 'command', kind: 'command', label: 'Run build check', value: 'simple check src/app/ui.web', pinned: true },
      { id: 'code', kind: 'code', label: 'Window CSS', value: 'border-radius: var(--ui-wm-window-radius);', pinned: false },
      { id: 'link', kind: 'link', label: 'Preview link', value: 'build/simple_wm_modern_preview.html', pinned: false }
    ];
  }

  _clipboardKindFilters() {
    return [
      { id: 'all', label: 'All' },
      { id: 'command', label: 'Commands' },
      { id: 'code', label: 'Code' },
      { id: 'link', label: 'Links' }
    ];
  }

  _filteredClipboardItems() {
    const query = String(this._clipboardSearchQuery || '').trim().toLowerCase();
    const kind = String(this._clipboardKindFilter || 'all');
    return this._clipboardItems().filter((item) => {
      const kindOk = kind === 'all' || item.kind === kind;
      const haystack = `${item.label} ${item.value} ${item.kind}`.toLowerCase();
      return kindOk && (!query || haystack.includes(query));
    });
  }

  _makeClipboardFilterButton(filter) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-clipboard-filter' + (filter.id === this._clipboardKindFilter ? ' active' : '');
    button.dataset.clipboardAction = 'filter';
    button.dataset.clipboardFilter = filter.id;
    button.setAttribute('aria-pressed', filter.id === this._clipboardKindFilter ? 'true' : 'false');
    button.textContent = filter.label;
    return button;
  }

  _setClipboardKindFilter(kind) {
    const value = String(kind || 'all');
    this._clipboardKindFilter = ['command', 'code', 'link'].includes(value) ? value : 'all';
    this._clipboardHistoryActiveIndex = 0;
    this._renderClipboardHistory();
  }

  _makeClipboardItem(item, index) {
    const row = document.createElement('button');
    row.type = 'button';
    const active = index === this._clipboardHistoryActiveIndex;
    row.id = `wm-clipboard-item-${index}`;
    row.className = 'wm-clipboard-item' + (item.pinned ? ' pinned' : '') + (active ? ' active' : '');
    row.dataset.clipboardId = item.id;
    row.dataset.clipboardKind = item.kind;
    row.dataset.clipboardIndex = String(index);
    row.tabIndex = active ? 0 : -1;
    row.setAttribute('role', 'option');
    row.setAttribute('aria-selected', active ? 'true' : 'false');
    row.setAttribute('aria-label', `${item.label}: ${item.value}`);
    row.appendChild(this._makeRoundIcon('wm-clipboard-icon', item.kind));
    const body = document.createElement('span');
    body.className = 'wm-clipboard-body';
    const label = document.createElement('strong');
    label.className = 'wm-clipboard-label';
    label.textContent = item.label;
    body.appendChild(label);
    const value = document.createElement('span');
    value.className = 'wm-clipboard-value';
    value.textContent = item.value;
    body.appendChild(value);
    row.appendChild(body);
    const paste = document.createElement('span');
    paste.className = 'wm-clipboard-mini-action';
    paste.dataset.clipboardAction = 'paste';
    paste.textContent = 'Paste';
    row.appendChild(paste);
    const pin = document.createElement('span');
    pin.className = 'wm-clipboard-mini-action';
    pin.dataset.clipboardAction = 'pin';
    pin.textContent = item.pinned ? 'Pinned' : 'Pin';
    row.appendChild(pin);
    return row;
  }

  _pasteClipboardItem(itemId) {
    const item = this._clipboardItems().find((entry) => entry.id === itemId);
    if (!item) return;
    if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
      navigator.clipboard.writeText(item.value).catch(() => {});
    }
    this._sendWindowCmd('clipboard_paste', { clipboard_id: item.id, clipboard_kind: item.kind, text: item.value });
    this._showSystemHud('Clipboard', item.kind, 1800);
    this._toggleClipboardHistory(false);
  }

  _pinClipboardItem(itemId) {
    const row = this._clipboardHistory?.querySelector(`[data-clipboard-id="${itemId}"]`);
    if (row) row.classList.toggle('pinned');
    this._sendWindowCmd('clipboard_pin', { clipboard_id: itemId });
    this._showSystemHud('Clipboard', 'pinned', 1400);
  }

  _moveClipboardHistorySelection(delta) {
    if (!this._clipboardHistory || this._clipboardHistory.hidden) return;
    const max = this._filteredClipboardItems().length - 1;
    if (max < 0) return;
    this._clipboardHistoryActiveIndex = Math.max(0, Math.min(max, this._clipboardHistoryActiveIndex + delta));
    this._syncClipboardHistorySelection(true);
  }

  _setClipboardHistorySelection(index) {
    if (!this._clipboardHistory || this._clipboardHistory.hidden) return;
    const max = this._filteredClipboardItems().length - 1;
    if (max < 0) return;
    this._clipboardHistoryActiveIndex = Math.max(0, Math.min(max, index));
    this._syncClipboardHistorySelection(true);
  }

  _syncClipboardHistorySelection(shouldFocus = true) {
    if (!this._clipboardHistory) return;
    const list = this._clipboardHistory.querySelector('.wm-clipboard-list');
    const items = list ? Array.from(list.querySelectorAll('.wm-clipboard-item')) : [];
    if (!list || !items.length) return;
    const activeIndex = Math.max(0, Math.min(items.length - 1, this._clipboardHistoryActiveIndex));
    this._clipboardHistoryActiveIndex = activeIndex;
    const activeId = `wm-clipboard-item-${activeIndex}`;
    this._clipboardHistory.setAttribute('aria-activedescendant', activeId);
    this._clipboardHistory.dataset.clipboardActiveIndex = String(activeIndex);
    list.setAttribute('aria-activedescendant', activeId);
    items.forEach((item, index) => {
      const active = index === activeIndex;
      item.classList.toggle('active', active);
      item.tabIndex = active ? 0 : -1;
      item.setAttribute('aria-selected', active ? 'true' : 'false');
      if (active && shouldFocus) item.focus();
    });
  }

  _activateClipboardHistorySelection(action = 'paste') {
    if (!this._clipboardHistory || this._clipboardHistory.hidden) return;
    const item = this._clipboardHistory.querySelector(`.wm-clipboard-item[data-clipboard-index="${this._clipboardHistoryActiveIndex}"]`);
    const clipboardId = item?.dataset.clipboardId || '';
    if (!clipboardId) return;
    if (action === 'pin') this._pinClipboardItem(clipboardId);
    else this._pasteClipboardItem(clipboardId);
  }

  _clearClipboardHistory() {
    this._sendWindowCmd('clipboard_clear', {});
    this._showSystemHud('Clipboard', 'cleared', 1400);
    this._toggleClipboardHistory(false);
  }

  _ensureScreenCapture() {
    if (this._screenCaptureOverlay && this._screenCaptureOverlay.isConnected) return this._screenCaptureOverlay;
    const overlay = document.createElement('aside');
    overlay.className = 'wm-screen-capture-overlay';
    overlay.hidden = true;
    overlay.setAttribute('role', 'dialog');
    overlay.setAttribute('aria-label', 'Screen capture');
    overlay.addEventListener('pointerdown', (event) => event.stopPropagation());
    overlay.addEventListener('mousedown', (event) => event.stopPropagation());
    overlay.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const mode = target?.closest('[data-capture-mode]');
      if (mode && overlay.contains(mode)) {
        this._setScreenCaptureMode(mode.dataset.captureMode || 'selection');
        return;
      }
      const action = target?.closest('[data-capture-action]');
      if (!action || !overlay.contains(action)) return;
      if (action.dataset.captureAction === 'capture') this._captureScreenSelection();
      if (action.dataset.captureAction === 'cancel') this._cancelScreenCapture();
    });
    document.body.appendChild(overlay);
    this._screenCaptureOverlay = overlay;
    return overlay;
  }

  _toggleScreenCapture(open = null) {
    const overlay = this._ensureScreenCapture();
    const shouldOpen = open == null ? overlay.hidden : open;
    overlay.hidden = !shouldOpen;
    if (shouldOpen) this._renderScreenCapture();
    return shouldOpen;
  }

  _renderScreenCapture() {
    const overlay = this._ensureScreenCapture();
    overlay.innerHTML = '';
    const selection = document.createElement('div');
    selection.className = 'wm-capture-selection';
    selection.setAttribute('role', 'img');
    selection.setAttribute('aria-label', 'Capture selection preview');
    overlay.appendChild(selection);
    const toolbar = document.createElement('div');
    toolbar.className = 'wm-capture-toolbar';
    toolbar.setAttribute('role', 'toolbar');
    toolbar.setAttribute('aria-label', 'Capture controls');
    for (const mode of this._screenCaptureModes()) toolbar.appendChild(this._makeCaptureModeButton(mode));
    toolbar.appendChild(this._makeCaptureActionButton('capture', 'Capture'));
    toolbar.appendChild(this._makeCaptureActionButton('cancel', 'Cancel'));
    overlay.appendChild(toolbar);
  }

  _screenCaptureModes() {
    return [
      { id: 'selection', label: 'Selection' },
      { id: 'window', label: 'Window' },
      { id: 'screen', label: 'Screen' }
    ];
  }

  _makeCaptureModeButton(mode) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-capture-mode' + (mode.id === this._screenCaptureMode ? ' active' : '');
    button.dataset.captureMode = mode.id;
    button.setAttribute('aria-pressed', mode.id === this._screenCaptureMode ? 'true' : 'false');
    button.textContent = mode.label;
    return button;
  }

  _makeCaptureActionButton(action, label) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-capture-action' + (action === 'capture' ? ' active' : '');
    button.dataset.captureAction = action;
    button.textContent = label;
    return button;
  }

  _setScreenCaptureMode(mode) {
    const value = String(mode || 'selection');
    this._screenCaptureMode = value === 'window' || value === 'screen' ? value : 'selection';
    this._renderScreenCapture();
    this._markScreenCaptureFeedback('mode', this._screenCaptureMode);
  }

  _captureScreenSelection() {
    this._markScreenCaptureFeedback('capture', this._screenCaptureMode);
    this._sendWindowCmd('screen_capture', { capture_mode: this._screenCaptureMode });
    this._showSystemHud('Capture', this._screenCaptureMode, 1800);
    setTimeout(() => this._toggleScreenCapture(false), 180);
  }

  _cancelScreenCapture() {
    this._markScreenCaptureFeedback('cancel', 'cancel');
    setTimeout(() => this._toggleScreenCapture(false), 180);
  }

  _markScreenCaptureFeedback(feedback, value = '') {
    if (!this._screenCaptureOverlay || !this._screenCaptureOverlay.isConnected) return;
    const overlay = this._screenCaptureOverlay;
    const kind = String(feedback || 'capture');
    const targetValue = String(value || '');
    if (this._screenCaptureFeedbackTimer) clearTimeout(this._screenCaptureFeedbackTimer);
    const targets = [];
    const selection = overlay.querySelector('.wm-capture-selection');
    if (selection) targets.push(selection);
    const mode = targetValue ? overlay.querySelector(`.wm-capture-mode[data-capture-mode="${targetValue}"]`) : null;
    if (mode) targets.push(mode);
    const action = overlay.querySelector(`.wm-capture-action[data-capture-action="${kind === 'cancel' ? 'cancel' : 'capture'}"]`);
    if (action) targets.push(action);
    overlay.dataset.captureFeedback = kind;
    overlay.dataset.captureFeedbackValue = targetValue;
    for (const target of targets) {
      target.classList.remove('action-feedback');
      void target.offsetWidth;
      target.classList.add('action-feedback');
      target.dataset.captureFeedback = kind;
    }
    this._screenCaptureFeedbackTimer = setTimeout(() => {
      delete overlay.dataset.captureFeedback;
      delete overlay.dataset.captureFeedbackValue;
      for (const target of targets) {
        target.classList.remove('action-feedback');
        delete target.dataset.captureFeedback;
      }
      this._screenCaptureFeedbackTimer = 0;
    }, 560);
  }

  _ensureQuickSettings() {
    if (this._quickSettings && this._quickSettings.isConnected) return this._quickSettings;
    const panel = document.createElement('aside');
    panel.className = 'wm-quick-settings';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Quick settings');
    panel.dataset.commandLaneSource = 'right-icons';
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const item = target?.closest('.wm-quick-setting');
      if (!item || !panel.contains(item)) return;
      this._quickSettingsActiveIndex = Number(item.dataset.settingIndex || '0') || 0;
      this._activateQuickSetting(item.dataset.setting || '');
    });
    panel.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveQuickSettingsSelection(1);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveQuickSettingsSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._setQuickSettingsSelection(0);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._setQuickSettingsSelection(this._quickSettingItems().length - 1);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateQuickSettingsSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleQuickSettings(false);
      }
    });
    panel.addEventListener('input', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const slider = target?.closest('.wm-quick-slider');
      if (!slider || !panel.contains(slider)) return;
      this._setQuickSettingLevel(slider.dataset.setting || '', Number(slider.value || 0));
    });
    document.body.appendChild(panel);
    this._quickSettings = panel;
    return panel;
  }

  _toggleQuickSettings(open = null) {
    const panel = this._ensureQuickSettings();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderQuickSettings();
    return shouldOpen;
  }

  _renderQuickSettings() {
    const panel = this._ensureQuickSettings();
    const items = this._quickSettingItems();
    if (this._quickSettingsActiveIndex >= items.length) this._quickSettingsActiveIndex = Math.max(0, items.length - 1);
    panel.innerHTML = '';
    panel.setAttribute('aria-activedescendant', `wm-quick-setting-${this._quickSettingsActiveIndex}`);
    panel.dataset.quickActiveIndex = String(this._quickSettingsActiveIndex);
    const title = document.createElement('div');
    title.className = 'wm-quick-title';
    title.textContent = 'Quick settings';
    panel.appendChild(title);
    const grid = document.createElement('div');
    grid.className = 'wm-quick-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Quick setting toggles');
    grid.setAttribute('aria-activedescendant', `wm-quick-setting-${this._quickSettingsActiveIndex}`);
    for (let index = 0; index < items.length; index += 1) grid.appendChild(this._makeQuickSetting(items[index], index));
    panel.appendChild(grid);
    const sliders = document.createElement('div');
    sliders.className = 'wm-quick-sliders';
    sliders.setAttribute('aria-label', 'Quick setting levels');
    for (const setting of this._quickSliderItems()) sliders.appendChild(this._makeQuickSlider(setting));
    panel.appendChild(sliders);
  }

  _quickSettingItems() {
    return [
      { id: 'wifi', label: 'Wi-Fi', value: 'Connected' },
      { id: 'audio', label: 'Audio', value: `${this._quickSettingLevels.audio}%` },
      { id: 'battery', label: 'Battery', value: '83%' },
      { id: 'brightness', label: 'Brightness', value: `${this._quickSettingLevels.brightness}%` },
      { id: 'focus', label: 'Focus', value: this._focusModeLabel() }
    ];
  }

  _quickSliderItems() {
    return [
      { id: 'audio', label: 'Audio', value: this._quickSettingLevels.audio },
      { id: 'brightness', label: 'Brightness', value: this._quickSettingLevels.brightness }
    ];
  }

  _makeQuickSetting(setting, index) {
    const button = document.createElement('button');
    button.type = 'button';
    const active = setting.id === 'wifi' || (setting.id === 'focus' && this._focusMode !== 'off');
    const selected = index === this._quickSettingsActiveIndex;
    button.id = `wm-quick-setting-${index}`;
    button.className = 'wm-quick-setting' + (active ? ' active' : '') + (selected ? ' selected' : '');
    button.dataset.setting = setting.id;
    button.dataset.settingIndex = String(index);
    button.tabIndex = selected ? 0 : -1;
    button.setAttribute('role', 'option');
    button.setAttribute('aria-selected', selected ? 'true' : 'false');
    button.setAttribute('aria-pressed', active ? 'true' : 'false');
    button.appendChild(this._makeRoundIcon('wm-quick-icon', setting.label));
    const body = document.createElement('span');
    body.className = 'wm-quick-body';
    const label = document.createElement('strong');
    label.className = 'wm-quick-label';
    label.textContent = setting.label;
    body.appendChild(label);
    const value = document.createElement('span');
    value.className = 'wm-quick-value';
    value.textContent = setting.value;
    body.appendChild(value);
    button.appendChild(body);
    return button;
  }

  _makeQuickSlider(setting) {
    const row = document.createElement('label');
    row.className = 'wm-quick-slider-row';
    row.dataset.setting = setting.id;
    const head = document.createElement('span');
    head.className = 'wm-quick-slider-head';
    const label = document.createElement('span');
    label.className = 'wm-quick-slider-label';
    label.textContent = setting.label;
    const value = document.createElement('span');
    value.className = 'wm-quick-slider-value';
    value.setAttribute('aria-live', 'polite');
    value.textContent = `${setting.value}%`;
    head.appendChild(label);
    head.appendChild(value);
    row.appendChild(head);
    const slider = document.createElement('input');
    slider.className = 'wm-quick-slider';
    slider.type = 'range';
    slider.min = '0';
    slider.max = '100';
    slider.value = String(setting.value);
    slider.dataset.setting = setting.id;
    slider.setAttribute('aria-label', `${setting.label} level`);
    slider.setAttribute('aria-valuetext', `${setting.value}%`);
    row.appendChild(slider);
    return row;
  }

  _setQuickSettingLevel(settingId, level) {
    const id = String(settingId || '');
    if (id !== 'audio' && id !== 'brightness') return;
    const value = Math.max(0, Math.min(100, Math.round(Number.isFinite(level) ? level : 0)));
    this._quickSettingLevels[id] = value;
    this._sendWindowCmd('quick_setting_level', { setting: id, level: value });
    this._showSystemHud(id === 'audio' ? 'Audio' : 'Brightness', `${value}%`, 900);
    this._updateQuickSettingLevelDom(id, value);
    this._markQuickSettingFeedback(id, 'level');
  }

  _updateQuickSettingLevelDom(settingId, value) {
    if (!this._quickSettings || !this._quickSettings.isConnected) return;
    const label = `${value}%`;
    for (const slider of this._quickSettings.querySelectorAll(`.wm-quick-slider[data-setting="${settingId}"]`)) {
      slider.value = String(value);
      slider.setAttribute('aria-valuetext', label);
    }
    for (const row of this._quickSettings.querySelectorAll(`.wm-quick-slider-row[data-setting="${settingId}"] .wm-quick-slider-value`)) {
      row.textContent = label;
    }
    const setting = this._quickSettings.querySelector(`.wm-quick-setting[data-setting="${settingId}"] .wm-quick-value`);
    if (setting) setting.textContent = label;
  }

  _activateQuickSetting(settingId) {
    const id = String(settingId || '');
    if (!id) return;
    if (id === 'focus') {
      this._toggleFocusMode();
      this._markQuickSettingFeedback(id, 'toggle');
      return;
    }
    this._sendWindowCmd('quick_setting', { setting: id });
    this._showSystemHud('Quick setting', id, 1600);
    this._markQuickSettingFeedback(id, 'toggle');
  }

  _markQuickSettingFeedback(settingId, feedback) {
    if (!this._quickSettings || !this._quickSettings.isConnected) return;
    const id = String(settingId || '');
    if (!id) return;
    const value = String(feedback || 'toggle');
    const key = `${id}:${value}`;
    const existing = this._quickSettingsFeedbackTimers.get(key);
    if (existing) clearTimeout(existing);
    const targets = [
      ...this._quickSettings.querySelectorAll(`.wm-quick-setting[data-setting="${id}"]`),
      ...this._quickSettings.querySelectorAll(`.wm-quick-slider-row[data-setting="${id}"]`)
    ];
    for (const target of targets) {
      target.classList.remove('changed');
      void target.offsetWidth;
      target.classList.add('changed');
      target.dataset.quickFeedback = value;
    }
    const timer = setTimeout(() => {
      for (const target of targets) {
        target.classList.remove('changed');
        delete target.dataset.quickFeedback;
      }
      this._quickSettingsFeedbackTimers.delete(key);
    }, 520);
    this._quickSettingsFeedbackTimers.set(key, timer);
  }

  _moveQuickSettingsSelection(delta) {
    if (!this._quickSettings || this._quickSettings.hidden) return;
    const max = this._quickSettingItems().length - 1;
    this._quickSettingsActiveIndex = Math.max(0, Math.min(max, this._quickSettingsActiveIndex + delta));
    this._syncQuickSettingsSelection(true);
  }

  _setQuickSettingsSelection(index) {
    if (!this._quickSettings || this._quickSettings.hidden) return;
    const max = this._quickSettingItems().length - 1;
    this._quickSettingsActiveIndex = Math.max(0, Math.min(max, index));
    this._syncQuickSettingsSelection(true);
  }

  _syncQuickSettingsSelection(shouldFocus = true) {
    if (!this._quickSettings) return;
    const grid = this._quickSettings.querySelector('.wm-quick-grid');
    const settings = grid ? Array.from(grid.querySelectorAll('.wm-quick-setting')) : [];
    if (!grid || !settings.length) return;
    const activeIndex = Math.max(0, Math.min(settings.length - 1, this._quickSettingsActiveIndex));
    this._quickSettingsActiveIndex = activeIndex;
    const activeId = `wm-quick-setting-${activeIndex}`;
    this._quickSettings.setAttribute('aria-activedescendant', activeId);
    this._quickSettings.dataset.quickActiveIndex = String(activeIndex);
    grid.setAttribute('aria-activedescendant', activeId);
    settings.forEach((setting, index) => {
      const selected = index === activeIndex;
      setting.classList.toggle('selected', selected);
      setting.tabIndex = selected ? 0 : -1;
      setting.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && shouldFocus) setting.focus();
    });
  }

  _activateQuickSettingsSelection() {
    if (!this._quickSettings || this._quickSettings.hidden) return;
    const setting = this._quickSettings.querySelector(`.wm-quick-setting[data-setting-index="${this._quickSettingsActiveIndex}"]`);
    this._activateQuickSetting(setting?.dataset.setting || '');
  }

  _ensureNotificationCenter() {
    if (this._notificationCenter && this._notificationCenter.isConnected) return this._notificationCenter;
    const panel = document.createElement('aside');
    panel.className = 'wm-notification-center';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Notification center');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const filter = target?.closest('[data-notification-filter]');
      if (filter && panel.contains(filter)) {
        this._setNotificationFilter(filter.dataset.notificationFilter || 'all');
        return;
      }
      const action = target?.closest('[data-notification-action]');
      if (!action || !panel.contains(action)) return;
      const notificationId = action.closest('.wm-notification-card')?.dataset.notificationId || '';
      if (action.dataset.notificationAction === 'open') this._openNotification(notificationId);
      if (action.dataset.notificationAction === 'snooze') this._snoozeNotification(notificationId);
      if (action.dataset.notificationAction === 'ack') this._ackNotification(notificationId);
      if (action.dataset.notificationAction === 'clear') this._clearNotifications();
    });
    panel.addEventListener('keydown', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleNotificationCenter(false);
        return;
      }
      if (target?.closest('.wm-notification-action, .wm-notification-filter, .wm-notification-clear')) return;
      if (event.key === 'ArrowDown' || event.key === 'ArrowRight') {
        event.preventDefault();
        this._moveNotificationCenterSelection(1);
      } else if (event.key === 'ArrowUp' || event.key === 'ArrowLeft') {
        event.preventDefault();
        this._moveNotificationCenterSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._setNotificationCenterSelection(0);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._setNotificationCenterSelection(this._filteredNotificationItems().length - 1);
      } else if (event.key === 'Enter') {
        event.preventDefault();
        this._activateNotificationCenterSelection('open');
      } else if (event.key === ' ') {
        event.preventDefault();
        this._activateNotificationCenterSelection('ack');
      }
    });
    document.body.appendChild(panel);
    this._notificationCenter = panel;
    return panel;
  }

  _toggleNotificationCenter(open = null) {
    const panel = this._ensureNotificationCenter();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderNotificationCenter();
    return shouldOpen;
  }

  _renderNotificationCenter() {
    const panel = this._ensureNotificationCenter();
    panel.dataset.focusMode = this._focusMode;
    const items = this._filteredNotificationItems();
    if (this._notificationCenterActiveIndex >= items.length) this._notificationCenterActiveIndex = Math.max(0, items.length - 1);
    panel.innerHTML = '';
    if (items.length) {
      panel.setAttribute('aria-activedescendant', `wm-notification-card-${this._notificationCenterActiveIndex}`);
      panel.dataset.notificationActiveIndex = String(this._notificationCenterActiveIndex);
    } else {
      panel.removeAttribute('aria-activedescendant');
      delete panel.dataset.notificationActiveIndex;
    }
    const header = document.createElement('div');
    header.className = 'wm-notification-header';
    const title = document.createElement('strong');
    title.className = 'wm-notification-title';
    title.textContent = 'Notifications';
    header.appendChild(title);
    const focus = document.createElement('span');
    focus.className = 'wm-notification-focus';
    focus.textContent = this._focusModeLabel();
    header.appendChild(focus);
    const clear = document.createElement('button');
    clear.type = 'button';
    clear.className = 'wm-notification-clear';
    clear.dataset.notificationAction = 'clear';
    clear.textContent = 'Clear';
    header.appendChild(clear);
    panel.appendChild(header);
    const filters = document.createElement('div');
    filters.className = 'wm-notification-filters';
    filters.setAttribute('aria-label', 'Notification filters');
    for (const filter of this._notificationFilters()) filters.appendChild(this._makeNotificationFilterButton(filter));
    panel.appendChild(filters);
    const list = document.createElement('div');
    list.className = 'wm-notification-list';
    list.dataset.notificationSource = 'history';
    list.setAttribute('role', 'listbox');
    list.setAttribute('aria-label', 'Notification history');
    if (items.length) list.setAttribute('aria-activedescendant', `wm-notification-card-${this._notificationCenterActiveIndex}`);
    for (let index = 0; index < items.length; index += 1) list.appendChild(this._makeNotificationCard(items[index], index));
    if (!items.length) {
      const empty = document.createElement('div');
      empty.className = 'wm-notification-empty';
      empty.textContent = 'No matching notifications';
      list.appendChild(empty);
    }
    panel.appendChild(list);
  }

  _notificationFilters() {
    return [
      { id: 'all', label: 'All' },
      { id: 'unread', label: 'Unread' },
      { id: 'quiet', label: 'Quiet' }
    ];
  }

  _makeNotificationFilterButton(filter) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-notification-filter' + (this._notificationFilter === filter.id ? ' active' : '');
    button.dataset.notificationFilter = filter.id;
    button.setAttribute('aria-pressed', this._notificationFilter === filter.id ? 'true' : 'false');
    button.textContent = filter.label;
    return button;
  }

  _setNotificationFilter(filterId) {
    const next = this._notificationFilters().some((filter) => filter.id === filterId) ? filterId : 'all';
    if (this._notificationFilter === next) return;
    this._notificationFilter = next;
    this._notificationCenterActiveIndex = 0;
    this._renderNotificationCenter();
  }

  _filteredNotificationItems() {
    const items = this._notificationItems();
    if (this._notificationFilter === 'unread') return items.filter((item) => item.unread);
    if (this._notificationFilter === 'quiet') return items.filter((item) => this._notificationItemQuiet(item));
    return items;
  }

  _notificationItems() {
    return [
      { id: 'build', kind: 'build', title: 'Build finished', meta: 'simple check passed', unread: true },
      { id: 'system', kind: 'system', title: 'System ready', meta: 'workspace services online', unread: false },
      { id: 'privacy', kind: 'privacy', title: 'Privacy status', meta: 'camera and microphone idle', unread: false }
    ];
  }

  _makeNotificationCard(item, index) {
    const card = document.createElement('article');
    const quiet = this._notificationItemQuiet(item);
    const selected = index === this._notificationCenterActiveIndex;
    card.id = `wm-notification-card-${index}`;
    card.className = 'wm-notification-card' + (item.unread ? ' unread' : '') + (quiet ? ' quiet' : '') + (selected ? ' selected' : '');
    card.dataset.notificationId = item.id;
    card.dataset.notificationKind = item.kind;
    card.dataset.notificationIndex = String(index);
    card.dataset.focusFiltered = quiet ? 'true' : 'false';
    card.tabIndex = selected ? 0 : -1;
    card.setAttribute('role', 'option');
    card.setAttribute('aria-selected', selected ? 'true' : 'false');
    card.setAttribute('aria-label', `${item.title}: ${item.meta}`);
    card.appendChild(this._makeRoundIcon('wm-notification-icon', item.title));
    const body = document.createElement('span');
    body.className = 'wm-notification-body';
    const title = document.createElement('strong');
    title.className = 'wm-notification-card-title';
    title.textContent = item.title;
    body.appendChild(title);
    const meta = document.createElement('span');
    meta.className = 'wm-notification-card-meta';
    meta.textContent = item.meta;
    body.appendChild(meta);
    card.appendChild(body);
    const actions = document.createElement('span');
    actions.className = 'wm-notification-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', `${item.title} actions`);
    actions.appendChild(this._makeNotificationAction('open', 'Open'));
    actions.appendChild(this._makeNotificationAction('snooze', 'Snooze'));
    actions.appendChild(this._makeNotificationAction('ack', 'Done'));
    card.appendChild(actions);
    return card;
  }

  _notificationItemQuiet(item) {
    return this._focusMode !== 'off' && item.kind !== 'privacy';
  }

  _makeNotificationAction(action, label) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-notification-action';
    button.dataset.notificationAction = action;
    button.textContent = label;
    return button;
  }

  _moveNotificationCenterSelection(delta) {
    if (!this._notificationCenter || this._notificationCenter.hidden) return;
    const max = this._filteredNotificationItems().length - 1;
    if (max < 0) return;
    this._notificationCenterActiveIndex = Math.max(0, Math.min(max, this._notificationCenterActiveIndex + delta));
    this._syncNotificationCenterSelection(true);
  }

  _setNotificationCenterSelection(index) {
    if (!this._notificationCenter || this._notificationCenter.hidden) return;
    const max = this._filteredNotificationItems().length - 1;
    if (max < 0) return;
    this._notificationCenterActiveIndex = Math.max(0, Math.min(max, index));
    this._syncNotificationCenterSelection(true);
  }

  _syncNotificationCenterSelection(shouldFocus = true) {
    if (!this._notificationCenter) return;
    const list = this._notificationCenter.querySelector('.wm-notification-list');
    const cards = list ? Array.from(list.querySelectorAll('.wm-notification-card')) : [];
    if (!list || !cards.length) return;
    const activeIndex = Math.max(0, Math.min(cards.length - 1, this._notificationCenterActiveIndex));
    this._notificationCenterActiveIndex = activeIndex;
    const activeId = `wm-notification-card-${activeIndex}`;
    this._notificationCenter.setAttribute('aria-activedescendant', activeId);
    this._notificationCenter.dataset.notificationActiveIndex = String(activeIndex);
    list.setAttribute('aria-activedescendant', activeId);
    cards.forEach((card, index) => {
      const selected = index === activeIndex;
      card.classList.toggle('selected', selected);
      card.tabIndex = selected ? 0 : -1;
      card.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && shouldFocus) card.focus();
    });
  }

  _activateNotificationCenterSelection(action = 'open') {
    if (!this._notificationCenter || this._notificationCenter.hidden) return;
    const card = this._notificationCenter.querySelector(`.wm-notification-card[data-notification-index="${this._notificationCenterActiveIndex}"]`);
    const notificationId = card?.dataset.notificationId || '';
    if (!notificationId) return;
    if (action === 'ack') this._ackNotification(notificationId);
    else this._openNotification(notificationId);
  }

  _openNotification(notificationId) {
    this._markNotificationActionFeedback(notificationId, 'open');
    this._sendWindowCmd('notification_open', { notification_id: String(notificationId || '') });
    setTimeout(() => this._toggleNotificationCenter(false), 180);
    this._showSystemHud('Notification', 'opened', 1400);
  }

  _snoozeNotification(notificationId) {
    this._markNotificationActionFeedback(notificationId, 'snooze');
    this._sendWindowCmd('notification_snooze', { notification_id: String(notificationId || ''), minutes: 60 });
    this._showSystemHud('Notification', 'snoozed 1h', 1400);
  }

  _ackNotification(notificationId) {
    this._markNotificationActionFeedback(notificationId, 'ack');
    this._sendWindowCmd('notification_ack', { notification_id: String(notificationId || '') });
    this._showSystemHud('Notification', 'done', 1400);
  }

  _clearNotifications() {
    this._markNotificationActionFeedback('', 'clear');
    this._sendWindowCmd('notification_clear', {});
    setTimeout(() => this._toggleNotificationCenter(false), 180);
    this._showSystemHud('Notifications', 'cleared', 1400);
  }

  _markNotificationActionFeedback(notificationId, action = '') {
    if (!this._notificationCenter || !this._notificationCenter.isConnected) return;
    const feedback = String(action || 'open');
    const id = String(notificationId || '');
    const safeId = typeof CSS !== 'undefined' && CSS.escape ? CSS.escape(id) : id.replace(/["\\]/g, '\\$&');
    const key = `${id}:${feedback}`;
    const existing = this._notificationActionFeedbackTimers.get(key);
    if (existing) clearTimeout(existing);
    const targets = [];
    if (feedback === 'clear') {
      targets.push(this._notificationCenter);
      const clear = this._notificationCenter.querySelector('.wm-notification-clear');
      if (clear) targets.push(clear);
    } else if (id) {
      const card = this._notificationCenter.querySelector(`.wm-notification-card[data-notification-id="${safeId}"]`);
      if (card) targets.push(card);
      const button = card?.querySelector(`.wm-notification-action[data-notification-action="${feedback}"]`);
      if (button) targets.push(button);
    }
    if (!targets.length) return;
    for (const target of targets) {
      target.classList.remove('action-feedback');
      void target.offsetWidth;
      target.classList.add('action-feedback');
      target.dataset.notificationFeedback = feedback;
    }
    const timer = setTimeout(() => {
      for (const target of targets) {
        target.classList.remove('action-feedback');
        delete target.dataset.notificationFeedback;
      }
      this._notificationActionFeedbackTimers.delete(key);
    }, 560);
    this._notificationActionFeedbackTimers.set(key, timer);
  }

  _ensureLiveActivity() {
    if (this._liveActivity && this._liveActivity.isConnected) return this._liveActivity;
    const panel = document.createElement('aside');
    panel.className = 'wm-live-activity';
    panel.hidden = true;
    panel.setAttribute('role', 'status');
    panel.setAttribute('aria-live', 'polite');
    panel.setAttribute('aria-label', 'Live activity');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const action = target?.closest('[data-live-action]');
      if (!action || !panel.contains(action)) return;
      this._activateLiveActivityAction(action.dataset.liveAction || '');
    });
    document.body.appendChild(panel);
    this._liveActivity = panel;
    return panel;
  }

  _toggleLiveActivity(open = null) {
    const panel = this._ensureLiveActivity();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderLiveActivity();
    return shouldOpen;
  }

  _renderLiveActivity() {
    const panel = this._ensureLiveActivity();
    panel.innerHTML = '';
    panel.dataset.liveActivityId = 'build';
    panel.dataset.liveState = this._liveActivityPaused ? 'paused' : 'running';
    panel.appendChild(this._makeRoundIcon('wm-live-activity-icon', 'Build'));
    const body = document.createElement('span');
    body.className = 'wm-live-activity-body';
    const title = document.createElement('strong');
    title.className = 'wm-live-activity-title';
    title.textContent = 'Build running';
    body.appendChild(title);
    const meta = document.createElement('span');
    meta.className = 'wm-live-activity-meta';
    meta.textContent = 'Type check and specs';
    body.appendChild(meta);
    const progress = document.createElement('span');
    progress.className = 'wm-live-activity-progress';
    progress.dataset.liveProgress = '64';
    progress.setAttribute('role', 'progressbar');
    progress.setAttribute('aria-label', 'Build progress');
    progress.setAttribute('aria-valuemin', '0');
    progress.setAttribute('aria-valuemax', '100');
    progress.setAttribute('aria-valuenow', '64');
    progress.setAttribute('aria-valuetext', '64%');
    const bar = document.createElement('span');
    bar.className = 'wm-live-activity-bar';
    progress.appendChild(bar);
    body.appendChild(progress);
    panel.appendChild(body);
    const actions = document.createElement('span');
    actions.className = 'wm-live-activity-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', 'Live activity controls');
    actions.appendChild(this._makeLiveActivityAction('open', 'Open', true));
    actions.appendChild(this._makeLiveActivityAction(this._liveActivityPaused ? 'resume' : 'pause', this._liveActivityPaused ? 'Resume' : 'Pause', false));
    actions.appendChild(this._makeLiveActivityAction('cancel', 'Cancel', false));
    actions.appendChild(this._makeLiveActivityAction('dismiss', 'Done', false));
    panel.appendChild(actions);
  }

  _makeLiveActivityAction(action, label, active = false) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-live-activity-action' + (active ? ' active' : '');
    button.dataset.liveAction = action;
    button.setAttribute('aria-label', `Live activity ${label.toLowerCase()}`);
    button.setAttribute('aria-pressed', active || action === 'pause' || action === 'resume' ? String(active || action === 'resume') : 'false');
    button.textContent = label;
    return button;
  }

  _activateLiveActivityAction(action) {
    if (action === 'open') {
      this._markLiveActivityActionFeedback('open');
      this._sendWindowCmd('live_activity_open', { activity_id: 'build' });
      return;
    }
    if (action === 'pause' || action === 'resume') {
      this._liveActivityPaused = action === 'pause';
      this._sendWindowCmd(action === 'pause' ? 'live_activity_pause' : 'live_activity_resume', { activity_id: 'build' });
      this._showSystemHud('Live activity', this._liveActivityPaused ? 'paused' : 'resumed', 1400);
      this._renderLiveActivity();
      this._markLiveActivityActionFeedback(action, this._liveActivityPaused ? 'resume' : 'pause');
      return;
    }
    if (action === 'cancel') {
      this._markLiveActivityActionFeedback('cancel');
      this._sendWindowCmd('live_activity_cancel', { activity_id: 'build' });
      setTimeout(() => this._toggleLiveActivity(false), 180);
      this._showSystemHud('Live activity', 'cancelled', 1400);
      return;
    }
    if (action === 'dismiss') {
      this._markLiveActivityActionFeedback('dismiss');
      this._sendWindowCmd('live_activity_dismiss', { activity_id: 'build' });
      setTimeout(() => this._toggleLiveActivity(false), 180);
    }
  }

  _markLiveActivityActionFeedback(action, targetAction = '') {
    if (!this._liveActivity || !this._liveActivity.isConnected) return;
    const feedback = String(action || 'open');
    const target = String(targetAction || feedback);
    if (this._liveActivityActionFeedbackTimer) clearTimeout(this._liveActivityActionFeedbackTimer);
    const panel = this._liveActivity;
    const targets = [panel];
    const button = panel.querySelector(`.wm-live-activity-action[data-live-action="${target}"]`);
    if (button) targets.push(button);
    const progress = panel.querySelector('.wm-live-activity-progress');
    if (progress) targets.push(progress);
    panel.dataset.liveFeedback = feedback;
    panel.dataset.liveFeedbackTarget = target;
    for (const item of targets) {
      item.classList.remove('action-feedback');
      void item.offsetWidth;
      item.classList.add('action-feedback');
      item.dataset.liveFeedback = feedback;
    }
    this._liveActivityActionFeedbackTimer = setTimeout(() => {
      delete panel.dataset.liveFeedback;
      delete panel.dataset.liveFeedbackTarget;
      for (const item of targets) {
        item.classList.remove('action-feedback');
        delete item.dataset.liveFeedback;
      }
      this._liveActivityActionFeedbackTimer = 0;
    }, 560);
  }

  _ensureHotCorners() {
    if (this._hotCorners && this._hotCorners.isConnected) return this._hotCorners;
    const layer = document.createElement('div');
    layer.className = 'wm-hot-corners';
    layer.setAttribute('aria-label', 'Hot corners');
    for (const item of this._hotCornerItems()) {
      const zone = document.createElement('button');
      zone.type = 'button';
      zone.className = 'wm-hot-corner-zone wm-hot-corner-' + item.id;
      zone.dataset.hotCornerAction = item.action;
      zone.setAttribute('aria-label', item.label);
      zone.addEventListener('pointerenter', () => this._showHotCornerHint(item));
      zone.addEventListener('pointerleave', () => this._hideHotCornerHint());
      zone.addEventListener('click', (event) => {
        event.preventDefault();
        this._activateHotCorner(item.action);
      });
      layer.appendChild(zone);
    }
    const hint = document.createElement('div');
    hint.className = 'wm-hot-corner-hint';
    hint.hidden = true;
    hint.setAttribute('role', 'status');
    hint.setAttribute('aria-live', 'polite');
    layer.appendChild(hint);
    document.body.appendChild(layer);
    this._hotCorners = layer;
    this._hotCornerHint = hint;
    return layer;
  }

  _hotCornerItems() {
    return [
      { id: 'overview', action: 'overview', label: 'Open window overview' },
      { id: 'launcher', action: 'launcher', label: 'Open app launcher' },
      { id: 'desktop', action: 'desktop_peek', label: 'Peek desktop' },
      { id: 'control-center', action: 'control_center', label: 'Open control center' }
    ];
  }

  _showHotCornerHint(item) {
    this._ensureHotCorners();
    this._activeHotCorner = item.action;
    const hint = this._hotCornerHint;
    if (!hint) return;
    hint.hidden = false;
    hint.dataset.hotCornerAction = item.action;
    hint.textContent = item.label;
  }

  _hideHotCornerHint() {
    this._activeHotCorner = '';
    if (this._hotCornerHint && !this._hotCornerHint.classList.contains('action-feedback')) this._hotCornerHint.hidden = true;
  }

  _updateHotCornerPreview(event) {
    if (!this._hotCorners) return;
    const margin = 28;
    const x = event.clientX;
    const y = event.clientY;
    const w = window.innerWidth || 0;
    const h = window.innerHeight || 0;
    let action = '';
    if (x <= margin && y <= margin) action = 'overview';
    if (x >= w - margin && y <= margin) action = 'launcher';
    if (x <= margin && y >= h - margin) action = 'desktop_peek';
    if (x >= w - margin && y >= h - margin) action = 'control_center';
    if (action === this._activeHotCorner) return;
    const item = this._hotCornerItems().find((candidate) => candidate.action === action);
    if (item) this._showHotCornerHint(item);
    if (!item) this._hideHotCornerHint();
  }

  _activateHotCorner(action) {
    const value = String(action || '');
    this._markHotCornerFeedback(value);
    this._sendWindowCmd('hot_corner', { corner_action: value });
    if (value === 'overview') this._toggleWindowOverview(true);
    if (value === 'launcher') this._toggleAppLauncher(true);
    if (value === 'desktop_peek') this._toggleDesktopPeek();
    if (value === 'control_center') this._toggleControlCenter(true);
    this._showSystemHud('Hot corner', value.replace('_', ' '), 1400);
  }

  _markHotCornerFeedback(action) {
    const layer = this._ensureHotCorners();
    const value = String(action || '');
    if (!value || !layer) return;
    if (this._hotCornerFeedbackTimer) clearTimeout(this._hotCornerFeedbackTimer);
    const previous = layer.querySelectorAll('[data-hot-corner-feedback]');
    previous.forEach((item) => {
      item.classList.remove('action-feedback');
      delete item.dataset.hotCornerFeedback;
    });
    delete layer.dataset.hotCornerFeedback;
    const item = this._hotCornerItems().find((candidate) => candidate.action === value);
    const zone = layer.querySelector(`.wm-hot-corner-zone[data-hot-corner-action="${value}"]`);
    const hint = this._hotCornerHint;
    const targets = [];
    layer.dataset.hotCornerFeedback = value;
    if (zone) targets.push(zone);
    if (hint) {
      hint.hidden = false;
      hint.dataset.hotCornerAction = value;
      hint.textContent = item ? item.label : value.replace('_', ' ');
      targets.push(hint);
    }
    for (const target of targets) {
      target.classList.remove('action-feedback');
      void target.offsetWidth;
      target.classList.add('action-feedback');
      target.dataset.hotCornerFeedback = value;
    }
    this._hotCornerFeedbackTimer = setTimeout(() => {
      delete layer.dataset.hotCornerFeedback;
      for (const target of targets) {
        target.classList.remove('action-feedback');
        delete target.dataset.hotCornerFeedback;
      }
      if (hint && this._activeHotCorner !== value) hint.hidden = true;
      this._hotCornerFeedbackTimer = 0;
    }, 560);
  }

  _toggleDesktopPeek(open = null) {
    const shouldPeek = open == null ? !this._desktopPeekActive : open;
    const windows = this._arrangeVisibleWindows();
    if (shouldPeek) {
      this._desktopPeekWindowIds = windows.map((win) => win.id);
      this._desktopPeekActive = true;
      if (this.desktop) this.desktop.dataset.desktopPeek = 'true';
      for (const win of windows) {
        const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(win.id);
        if (isElectronWindow) this._electronMinimizeWindow(win.id);
        this._sendWindowCmd('minimize', {
          window_id_hint: win.id,
          ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
          desktop_peek: true
        });
      }
      this._sendWindowCmd('desktop_peek', { active: true, window_count: windows.length });
      this._showSystemHud('Desktop peek', 'on', 1500);
      return true;
    }
    const ids = this._desktopPeekWindowIds.slice();
    this._desktopPeekActive = false;
    this._desktopPeekWindowIds = [];
    if (this.desktop) this.desktop.dataset.desktopPeek = 'false';
    for (const id of ids) {
      const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(id);
      if (isElectronWindow) this._electronFocusWindow(id);
      this._sendWindowCmd('restore', {
        window_id_hint: id,
        ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
        desktop_peek: false
      });
    }
    this._sendWindowCmd('desktop_peek', { active: false, window_count: ids.length });
    this._showSystemHud('Desktop peek', 'off', 1500);
    return false;
  }

  _ensureResizeHud() {
    if (this._resizeHud && this._resizeHud.isConnected) return this._resizeHud;
    const hud = document.createElement('aside');
    hud.className = 'wm-resize-hud';
    hud.hidden = true;
    hud.setAttribute('role', 'status');
    hud.setAttribute('aria-live', 'polite');
    hud.setAttribute('aria-label', 'Resize HUD');
    document.body.appendChild(hud);
    this._resizeHud = hud;
    return hud;
  }

  _showResizeHud(width, height, direction = '') {
    const hud = this._ensureResizeHud();
    hud.hidden = false;
    const resizeDirection = String(direction || '');
    hud.dataset.resizeDirection = resizeDirection;
    hud.dataset.resizeFeedback = resizeDirection ? 'directional' : 'size-only';
    hud.innerHTML = '';
    const label = document.createElement('span');
    label.className = 'wm-resize-hud-label';
    label.textContent = 'Resize';
    hud.appendChild(label);
    const value = document.createElement('strong');
    value.className = 'wm-resize-hud-value';
    value.textContent = `${Math.round(width)} x ${Math.round(height)}`;
    hud.appendChild(value);
    window.clearTimeout(this._resizeHudTimer);
    return hud;
  }

  _hideResizeHud(delayMs = 900) {
    if (!this._resizeHud) return;
    window.clearTimeout(this._resizeHudTimer);
    this._resizeHudTimer = window.setTimeout(() => {
      if (this._resizeHud) this._resizeHud.hidden = true;
    }, Math.max(0, delayMs || 0));
  }

  _ensureGestureHints() {
    if (this._gestureHints && this._gestureHints.isConnected) return this._gestureHints;
    const panel = document.createElement('aside');
    panel.className = 'wm-gesture-hints';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Trackpad gesture hints');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const action = event.target.closest('[data-gesture-action]');
      if (!action || !panel.contains(action)) return;
      if (action.dataset.gestureAction === 'close') this._toggleGestureHints(false);
    });
    document.body.appendChild(panel);
    this._gestureHints = panel;
    return panel;
  }

  _toggleGestureHints(open = null) {
    const panel = this._ensureGestureHints();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderGestureHints();
    return shouldOpen;
  }

  _renderGestureHints() {
    const panel = this._ensureGestureHints();
    panel.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-gesture-title';
    title.textContent = 'Trackpad gestures';
    panel.appendChild(title);
    const list = document.createElement('div');
    list.className = 'wm-gesture-list';
    for (const item of this._gestureHintItems()) list.appendChild(this._makeGestureHint(item));
    panel.appendChild(list);
    const close = document.createElement('button');
    close.type = 'button';
    close.className = 'wm-gesture-action active';
    close.dataset.gestureAction = 'close';
    close.textContent = 'Done';
    panel.appendChild(close);
  }

  _gestureHintItems() {
    return this._trackpadGestureItems().map((item) => ({ gesture: item.gesture, action: item.label }));
  }

  _trackpadGestureItems() {
    return [
      { gesture: 'Three-finger swipe up', action: 'overview', label: 'Window overview' },
      { gesture: 'Three-finger swipe left', action: 'workspace_previous', label: 'Previous workspace' },
      { gesture: 'Three-finger swipe right', action: 'workspace_next', label: 'Next workspace' },
      { gesture: 'Pinch open', action: 'launcher', label: 'App launcher' }
    ];
  }

  _makeGestureHint(item) {
    const row = document.createElement('span');
    row.className = 'wm-gesture-row';
    row.dataset.gestureHint = item.action.toLowerCase().replace(/\s+/g, '-');
    row.appendChild(this._makeRoundIcon('wm-gesture-icon', item.gesture));
    const body = document.createElement('span');
    body.className = 'wm-gesture-body';
    const gesture = document.createElement('strong');
    gesture.className = 'wm-gesture-name';
    gesture.textContent = item.gesture;
    body.appendChild(gesture);
    const action = document.createElement('span');
    action.className = 'wm-gesture-action-label';
    action.textContent = item.action;
    body.appendChild(action);
    row.appendChild(body);
    return row;
  }

  _shouldHandleShellTrackpadGesture(event) {
    const target = event.target instanceof Element ? event.target : event.target?.parentElement;
    if (!target) return false;
    if (target.closest('input, textarea, select, [contenteditable="true"]')) return false;
    if (target.closest('[data-canonical-id], .wm-window, .wm-command-palette, .wm-shortcut-overlay, .wm-clipboard-history, .wm-screen-capture-overlay')) return false;
    return !!target.closest('#wm-desktop, #wm-taskbar, .wm-top-menu-bar, .wm-hot-corner-zone');
  }

  _normalizedWheelDelta(value, deltaMode) {
    const unit = deltaMode === 1 ? 16 : deltaMode === 2 ? 120 : 1;
    return Number(value || 0) * unit;
  }

  _handleTrackpadGesture(event) {
    if (!this._shouldHandleShellTrackpadGesture(event)) return false;
    const now = window.performance && typeof window.performance.now === 'function' ? window.performance.now() : Date.now();
    if (now - this._trackpadGestureLastActionAt < 420) return false;
    const dx = this._normalizedWheelDelta(event.deltaX, event.deltaMode);
    const dy = this._normalizedWheelDelta(event.deltaY, event.deltaMode);
    if (Math.abs(dx) < 4 && Math.abs(dy) < 4) return false;
    if (now - this._trackpadGestureAccum.lastAt > 260) this._trackpadGestureAccum = { x: 0, y: 0, lastAt: now };
    this._trackpadGestureAccum.x += dx;
    this._trackpadGestureAccum.y += dy;
    this._trackpadGestureAccum.lastAt = now;
    const x = this._trackpadGestureAccum.x;
    const y = this._trackpadGestureAccum.y;
    let action = '';
    if ((event.ctrlKey || event.metaKey) && y < -42) action = 'launcher';
    else if (Math.abs(x) >= 110 && Math.abs(x) > Math.abs(y) * 1.18) action = x > 0 ? 'workspace_next' : 'workspace_previous';
    else if (Math.abs(y) >= 135 && Math.abs(y) > Math.abs(x) * 1.18) action = y < 0 ? 'overview' : 'desktop_peek';
    if (!action) return false;
    event.preventDefault();
    this._trackpadGestureAccum = { x: 0, y: 0, lastAt: now };
    this._trackpadGestureLastActionAt = now;
    this._activateTrackpadGesture(action);
    return true;
  }

  _activateTrackpadGesture(action) {
    const value = String(action || '');
    if (value === 'overview') this._toggleWindowOverview(true);
    if (value === 'workspace_previous') this._switchRelativeWorkspace(-1);
    if (value === 'workspace_next') this._switchRelativeWorkspace(1);
    if (value === 'launcher') this._toggleAppLauncher(true);
    if (value === 'desktop_peek') this._toggleDesktopPeek();
    this._sendWindowCmd('trackpad_gesture', { gesture_action: value });
    this._showSystemHud('Trackpad', value.replace('_', ' '), 1300);
  }

  _switchRelativeWorkspace(delta) {
    const items = this._workspaceItems();
    if (!items.length) return;
    const current = this._workspaceIndex(this._activeWorkspaceId);
    const next = (current + delta + items.length) % items.length;
    this._switchWorkspace(items[next].id);
  }

  _ensureSystemHud() {
    if (this._systemHud && this._systemHud.isConnected) return this._systemHud;
    const hud = document.createElement('aside');
    hud.className = 'wm-system-hud';
    hud.hidden = true;
    hud.setAttribute('role', 'status');
    hud.setAttribute('aria-live', 'polite');
    hud.setAttribute('aria-label', 'System status HUD');
    document.body.appendChild(hud);
    this._systemHud = hud;
    return hud;
  }

  _showSystemHud(label = 'System', value = 'ready', durationMs = 1800) {
    if (!this._feedbackAllows('standard')) return null;
    const hud = this._ensureSystemHud();
    hud.innerHTML = '';
    const icon = document.createElement('span');
    icon.className = 'wm-system-hud-icon wm-round-icon';
    const glyph = document.createElement('span');
    glyph.className = 'wm-icon-glyph';
    glyph.textContent = String(label || 'S').slice(0, 1).toUpperCase();
    icon.appendChild(glyph);
    hud.appendChild(icon);

    const body = document.createElement('div');
    body.className = 'wm-system-hud-body';
    const title = document.createElement('span');
    title.className = 'wm-system-hud-title';
    title.textContent = label || 'System';
    const status = document.createElement('strong');
    status.className = 'wm-system-hud-value';
    status.textContent = value || 'ready';
    body.appendChild(title);
    body.appendChild(status);
    hud.appendChild(body);

    const meter = document.createElement('span');
    meter.className = 'wm-system-hud-meter';
    hud.appendChild(meter);

    hud.hidden = false;
    window.clearTimeout(this._systemHudTimer);
    this._systemHudTimer = window.setTimeout(() => {
      if (this._systemHud) this._systemHud.hidden = true;
    }, Math.max(600, durationMs || 1800));
    return hud;
  }

  _ensurePrivacyIndicator() {
    if (this._privacyIndicator && this._privacyIndicator.isConnected) return this._privacyIndicator;
    const panel = document.createElement('aside');
    panel.className = 'wm-privacy-indicator';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Privacy status');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const action = event.target.closest('[data-privacy-action]');
      if (!action || !panel.contains(action)) return;
      if (action.dataset.privacyAction === 'close') this._togglePrivacyIndicator(false);
    });
    document.body.appendChild(panel);
    this._privacyIndicator = panel;
    return panel;
  }

  _togglePrivacyIndicator(open = null) {
    const panel = this._ensurePrivacyIndicator();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderPrivacyIndicator();
    return shouldOpen;
  }

  _renderPrivacyIndicator() {
    const panel = this._ensurePrivacyIndicator();
    panel.innerHTML = '';
    const header = document.createElement('div');
    header.className = 'wm-privacy-header';
    const dot = document.createElement('span');
    dot.className = 'wm-privacy-dot';
    header.appendChild(dot);
    const title = document.createElement('strong');
    title.textContent = 'Privacy';
    header.appendChild(title);
    panel.appendChild(header);

    const list = document.createElement('div');
    list.className = 'wm-privacy-list';
    list.appendChild(this._makePrivacyRow('Camera', this._browserPrivacyState('camera')));
    list.appendChild(this._makePrivacyRow('Microphone', this._browserPrivacyState('microphone')));
    list.appendChild(this._makePrivacyRow('Screen capture', 'off'));
    panel.appendChild(list);

    const actions = document.createElement('div');
    actions.className = 'wm-privacy-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', 'Privacy controls');
    const close = document.createElement('button');
    close.type = 'button';
    close.className = 'wm-privacy-action active';
    close.dataset.privacyAction = 'close';
    close.textContent = 'Done';
    actions.appendChild(close);
    panel.appendChild(actions);
  }

  _makePrivacyRow(label, value) {
    const row = document.createElement('span');
    row.className = 'wm-privacy-row';
    row.dataset.privacyService = label.toLowerCase().replace(/\s+/g, '-');
    row.appendChild(this._makeRoundIcon('wm-privacy-icon', label));
    const name = document.createElement('span');
    name.className = 'wm-privacy-name';
    name.textContent = label;
    row.appendChild(name);
    const state = document.createElement('strong');
    state.className = 'wm-privacy-state';
    state.textContent = value || 'off';
    row.appendChild(state);
    return row;
  }

  _browserPrivacyState(name) {
    const nav = window.navigator || {};
    if (!nav.permissions || typeof nav.permissions.query !== 'function') return 'unknown';
    return 'available';
  }

  _ensureControlCenter() {
    if (this._controlCenter && this._controlCenter.isConnected) return this._controlCenter;
    const panel = document.createElement('aside');
    panel.className = 'wm-control-center';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'WM control center');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    document.body.appendChild(panel);
    this._controlCenter = panel;
    return panel;
  }

  _toggleControlCenter(open = null) {
    const panel = this._ensureControlCenter();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderControlCenter();
    return shouldOpen;
  }

  _renderControlCenter() {
    const panel = this._ensureControlCenter();
    panel.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-control-title';
    title.textContent = 'Control center';
    panel.appendChild(title);
    const motion = document.createElement('div');
    motion.className = 'wm-control-group';
    motion.setAttribute('aria-label', 'Motion');
    motion.appendChild(this._makeControlCenterButton('Standard motion', this._normalizeMotionPreference(this._readMotionPreference()) === 'standard', () => this._setMotionFromControlCenter('standard')));
    motion.appendChild(this._makeControlCenterButton('Reduced motion', this._normalizeMotionPreference(this._readMotionPreference()) === 'reduced', () => this._setMotionFromControlCenter('reduced')));
    motion.appendChild(this._makeControlCenterButton('Motion off', this._normalizeMotionPreference(this._readMotionPreference()) === 'off', () => this._setMotionFromControlCenter('off')));
    panel.appendChild(motion);
    const quiet = document.createElement('div');
    quiet.className = 'wm-control-group';
    quiet.setAttribute('aria-label', 'Quiet mode');
    quiet.appendChild(this._makeControlCenterButton('Quiet mode off', this._quietMode === 'off', () => this.setQuietModePreference('off')));
    quiet.appendChild(this._makeControlCenterButton('Quiet mode on', this._quietMode === 'on', () => this.setQuietModePreference('on')));
    panel.appendChild(quiet);
    const animation = document.createElement('div');
    animation.className = 'wm-control-group';
    animation.setAttribute('aria-label', 'Animation style');
    animation.appendChild(this._makeControlCenterButton('Spring motion', this._animationStyle === 'spring', () => this.setAnimationStyle('spring')));
    animation.appendChild(this._makeControlCenterButton('Calm motion', this._animationStyle === 'calm', () => this.setAnimationStyle('calm')));
    animation.appendChild(this._makeControlCenterButton('Snappy motion', this._animationStyle === 'snappy', () => this.setAnimationStyle('snappy')));
    panel.appendChild(animation);
    const dockMagnification = document.createElement('div');
    dockMagnification.className = 'wm-control-group';
    dockMagnification.setAttribute('aria-label', 'Dock magnification');
    dockMagnification.appendChild(this._makeControlCenterButton('Standard dock', this._dockMagnificationMode === 'standard', () => this.setDockMagnificationPreference('standard')));
    dockMagnification.appendChild(this._makeControlCenterButton('Subtle dock', this._dockMagnificationMode === 'subtle', () => this.setDockMagnificationPreference('subtle')));
    dockMagnification.appendChild(this._makeControlCenterButton('Dock magnification off', this._dockMagnificationMode === 'off', () => this.setDockMagnificationPreference('off')));
    panel.appendChild(dockMagnification);
    const dockVisibility = document.createElement('div');
    dockVisibility.className = 'wm-control-group';
    dockVisibility.setAttribute('aria-label', 'Dock visibility');
    dockVisibility.appendChild(this._makeControlCenterButton('Dock shown', this._dockVisibilityMode === 'shown', () => this.setDockVisibilityPreference('shown')));
    dockVisibility.appendChild(this._makeControlCenterButton('Dock auto-hide', this._dockVisibilityMode === 'auto', () => this.setDockVisibilityPreference('auto')));
    dockVisibility.appendChild(this._makeControlCenterButton('Dock hidden', this._dockVisibilityMode === 'hidden', () => this.setDockVisibilityPreference('hidden')));
    panel.appendChild(dockVisibility);
    const surface = document.createElement('div');
    surface.className = 'wm-control-group';
    surface.setAttribute('aria-label', 'Surface depth');
    surface.appendChild(this._makeControlCenterButton('Layered depth', this._surfaceDepthMode === 'layered', () => this.setSurfaceDepthPreference('layered')));
    surface.appendChild(this._makeControlCenterButton('Subtle depth', this._surfaceDepthMode === 'subtle', () => this.setSurfaceDepthPreference('subtle')));
    surface.appendChild(this._makeControlCenterButton('Flat depth', this._surfaceDepthMode === 'flat', () => this.setSurfaceDepthPreference('flat')));
    panel.appendChild(surface);
    const traffic = document.createElement('div');
    traffic.className = 'wm-control-group';
    traffic.setAttribute('aria-label', 'Traffic controls');
    traffic.appendChild(this._makeControlCenterButton('Left traffic', this._trafficSideMode === 'left', () => this.setTrafficSidePreference('left')));
    traffic.appendChild(this._makeControlCenterButton('Right traffic', this._trafficSideMode === 'right', () => this.setTrafficSidePreference('right')));
    panel.appendChild(traffic);
    const chrome = document.createElement('div');
    chrome.className = 'wm-control-group';
    chrome.setAttribute('aria-label', 'Chrome verbosity');
    chrome.appendChild(this._makeControlCenterButton('Full chrome', this._chromeVerbosityMode === 'full', () => this.setChromeVerbosityPreference('full')));
    chrome.appendChild(this._makeControlCenterButton('Compact chrome', this._chromeVerbosityMode === 'compact', () => this.setChromeVerbosityPreference('compact')));
    chrome.appendChild(this._makeControlCenterButton('Minimal chrome', this._chromeVerbosityMode === 'minimal', () => this.setChromeVerbosityPreference('minimal')));
    panel.appendChild(chrome);
    const windowMotion = document.createElement('div');
    windowMotion.className = 'wm-control-group';
    windowMotion.setAttribute('aria-label', 'Window motion');
    windowMotion.appendChild(this._makeControlCenterButton('Mac motion', this._windowTransitionMode === 'mac', () => this.setWindowTransitionPreference('mac')));
    windowMotion.appendChild(this._makeControlCenterButton('Fade motion', this._windowTransitionMode === 'fade', () => this.setWindowTransitionPreference('fade')));
    windowMotion.appendChild(this._makeControlCenterButton('Motion none', this._windowTransitionMode === 'none', () => this.setWindowTransitionPreference('none')));
    panel.appendChild(windowMotion);
    const focus = document.createElement('div');
    focus.className = 'wm-control-group';
    focus.setAttribute('aria-label', 'Focus mode');
    focus.appendChild(this._makeControlCenterButton('Focus off', this._focusMode === 'off', () => this.setFocusMode('off')));
    focus.appendChild(this._makeControlCenterButton('Work focus', this._focusMode === 'work', () => this.setFocusMode('work')));
    focus.appendChild(this._makeControlCenterButton('Deep focus', this._focusMode === 'deep', () => this.setFocusMode('deep')));
    panel.appendChild(focus);
    const material = document.createElement('div');
    material.className = 'wm-control-group';
    material.setAttribute('aria-label', 'Material transparency');
    material.appendChild(this._makeControlCenterButton('Standard glass', this._normalizeTransparencyPreference(this._readTransparencyPreference()) === 'standard', () => this._setTransparencyFromControlCenter('standard')));
    material.appendChild(this._makeControlCenterButton('Reduced glass', this._normalizeTransparencyPreference(this._readTransparencyPreference()) === 'reduced', () => this._setTransparencyFromControlCenter('reduced')));
    material.appendChild(this._makeControlCenterButton('Solid surfaces', this._normalizeTransparencyPreference(this._readTransparencyPreference()) === 'off', () => this._setTransparencyFromControlCenter('off')));
    panel.appendChild(material);
    const accent = document.createElement('div');
    accent.className = 'wm-control-group';
    accent.setAttribute('aria-label', 'Accent color');
    const activeAccent = this._normalizeAccentPreference(this._readAccentPreference()).id;
    this._accentChoices().forEach((choice) => {
      accent.appendChild(this._makeControlCenterButton(choice.label + ' accent', activeAccent === choice.id, () => this._setAccentFromControlCenter(choice.id)));
    });
    panel.appendChild(accent);
    const contrast = document.createElement('div');
    contrast.className = 'wm-control-group';
    contrast.setAttribute('aria-label', 'Readability contrast');
    contrast.appendChild(this._makeControlCenterButton('Comfortable contrast', this._contrastMode === 'comfortable', () => this.setContrastPreference('comfortable')));
    contrast.appendChild(this._makeControlCenterButton('High contrast', this._contrastMode === 'high', () => this.setContrastPreference('high')));
    panel.appendChild(contrast);
    const feedback = document.createElement('div');
    feedback.className = 'wm-control-group';
    feedback.setAttribute('aria-label', 'Feedback policy');
    feedback.appendChild(this._makeControlCenterButton('Standard feedback', this._feedbackMode === 'standard', () => this.setFeedbackPreference('standard')));
    feedback.appendChild(this._makeControlCenterButton('Subtle feedback', this._feedbackMode === 'subtle', () => this.setFeedbackPreference('subtle')));
    feedback.appendChild(this._makeControlCenterButton('Feedback off', this._feedbackMode === 'off', () => this.setFeedbackPreference('off')));
    panel.appendChild(feedback);
    const energy = document.createElement('div');
    energy.className = 'wm-control-group';
    energy.setAttribute('aria-label', 'Energy policy');
    energy.appendChild(this._makeControlCenterButton('Standard energy', this._energyMode === 'standard', () => this.setEnergyPreference('standard')));
    energy.appendChild(this._makeControlCenterButton('Low power', this._energyMode === 'low', () => this.setEnergyPreference('low')));
    energy.appendChild(this._makeControlCenterButton('Critical saver', this._energyMode === 'critical', () => this.setEnergyPreference('critical')));
    panel.appendChild(energy);
    const wallpaper = document.createElement('div');
    wallpaper.className = 'wm-control-group';
    wallpaper.setAttribute('aria-label', 'Animated wallpaper');
    const activeWallpaper = this._normalizeWallpaperPreference(this._readWallpaperPreference());
    wallpaper.appendChild(this._makeControlCenterButton('Aurora', activeWallpaper === 'aurora', () => this._setWallpaperFromControlCenter('aurora')));
    wallpaper.appendChild(this._makeControlCenterButton('Mesh', activeWallpaper === 'mesh', () => this._setWallpaperFromControlCenter('mesh')));
    wallpaper.appendChild(this._makeControlCenterButton('Solid', activeWallpaper === 'solid', () => this._setWallpaperFromControlCenter('solid')));
    panel.appendChild(wallpaper);
    const backdrop = document.createElement('div');
    backdrop.className = 'wm-control-group';
    backdrop.setAttribute('aria-label', 'Backdrop motion');
    backdrop.appendChild(this._makeControlCenterButton('Ambient drift', this._backdropMotionMode === 'ambient', () => this.setBackdropMotionPreference('ambient')));
    backdrop.appendChild(this._makeControlCenterButton('Subtle drift', this._backdropMotionMode === 'subtle', () => this.setBackdropMotionPreference('subtle')));
    backdrop.appendChild(this._makeControlCenterButton('Static backdrop', this._backdropMotionMode === 'static', () => this.setBackdropMotionPreference('static')));
    panel.appendChild(backdrop);
    const backdropIntensity = document.createElement('div');
    backdropIntensity.className = 'wm-control-group';
    backdropIntensity.setAttribute('aria-label', 'Backdrop intensity');
    backdropIntensity.appendChild(this._makeControlCenterButton('Vivid backdrop', this._backdropIntensityMode === 'vivid', () => this.setBackdropIntensityPreference('vivid')));
    backdropIntensity.appendChild(this._makeControlCenterButton('Balanced backdrop', this._backdropIntensityMode === 'balanced', () => this.setBackdropIntensityPreference('balanced')));
    backdropIntensity.appendChild(this._makeControlCenterButton('Quiet backdrop', this._backdropIntensityMode === 'quiet', () => this.setBackdropIntensityPreference('quiet')));
    panel.appendChild(backdropIntensity);
    const density = document.createElement('div');
    density.className = 'wm-control-group';
    density.setAttribute('aria-label', 'Layout density');
    density.appendChild(this._makeControlCenterButton('Compact density', this._densityMode === 'compact', () => this.setDensityPreference('compact')));
    density.appendChild(this._makeControlCenterButton('Comfortable density', this._densityMode === 'comfortable', () => this.setDensityPreference('comfortable')));
    density.appendChild(this._makeControlCenterButton('Spacious density', this._densityMode === 'spacious', () => this.setDensityPreference('spacious')));
    panel.appendChild(density);
    const cornerRadius = document.createElement('div');
    cornerRadius.className = 'wm-control-group';
    cornerRadius.setAttribute('aria-label', 'Corner radius');
    cornerRadius.appendChild(this._makeControlCenterButton('Round corners', this._cornerRadiusMode === 'round', () => this._setCornerRadiusFromControlCenter('round')));
    cornerRadius.appendChild(this._makeControlCenterButton('Soft corners', this._cornerRadiusMode === 'soft', () => this._setCornerRadiusFromControlCenter('soft')));
    cornerRadius.appendChild(this._makeControlCenterButton('Square corners', this._cornerRadiusMode === 'square', () => this._setCornerRadiusFromControlCenter('square')));
    panel.appendChild(cornerRadius);
    const tools = document.createElement('div');
    tools.className = 'wm-control-group';
    tools.setAttribute('aria-label', 'Workspace tools');
    tools.appendChild(this._makeControlCenterButton('Desktop widgets', !!this._desktopWidgets && !this._desktopWidgets.classList.contains('collapsed'), () => this._toggleDesktopWidgets()));
    tools.appendChild(this._makeControlCenterButton('Window overview', !!this._windowOverview && !this._windowOverview.hidden, () => this._toggleWindowOverview(true)));
    tools.appendChild(this._makeControlCenterButton('Arrange windows', !!this._windowArrangePalette && !this._windowArrangePalette.hidden, () => this._toggleWindowArrangePalette(true)));
    tools.appendChild(this._makeControlCenterButton('Peek desktop', this._desktopPeekActive, () => this._toggleDesktopPeek()));
    tools.appendChild(this._makeControlCenterButton('Workspace switcher', !!this._workspaceSwitcher && !this._workspaceSwitcher.hidden, () => this._toggleWorkspaceSwitcher(true)));
    tools.appendChild(this._makeControlCenterButton('Clipboard history', !!this._clipboardHistory && !this._clipboardHistory.hidden, () => this._toggleClipboardHistory(true)));
    tools.appendChild(this._makeControlCenterButton('Screen capture', !!this._screenCaptureOverlay && !this._screenCaptureOverlay.hidden, () => this._toggleScreenCapture(true)));
    tools.appendChild(this._makeControlCenterButton('Quick settings', !!this._quickSettings && !this._quickSettings.hidden, () => this._toggleQuickSettings(true)));
    tools.appendChild(this._makeControlCenterButton('Wallpaper picker', !!this._wallpaperPicker && !this._wallpaperPicker.hidden, () => this._toggleWallpaperPicker(true)));
    tools.appendChild(this._makeControlCenterButton('Accent palette', !!this._accentPalette && !this._accentPalette.hidden, () => this._toggleAccentPalette(true)));
    tools.appendChild(this._makeControlCenterButton('Dock stack', !!this._dockStack && !this._dockStack.hidden, () => this._toggleDockStack(true)));
    tools.appendChild(this._makeControlCenterButton('Quality inspector', !!this._qualityInspector && !this._qualityInspector.hidden, () => this._toggleQualityInspector(true)));
    panel.appendChild(tools);
  }

  _makeControlCenterButton(label, active, action) {
    const button = document.createElement('button');
    const feedbackId = this._controlCenterActionId(label);
    button.type = 'button';
    button.className = 'wm-control-button' + (active ? ' active' : '');
    button.dataset.controlAction = feedbackId;
    button.setAttribute('aria-pressed', active ? 'true' : 'false');
    button.textContent = label;
    button.addEventListener('click', () => {
      action();
      this._renderControlCenter();
      this._markControlCenterFeedback(feedbackId);
    });
    return button;
  }

  _controlCenterActionId(label) {
    return String(label || 'control').toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '') || 'control';
  }

  _markControlCenterFeedback(actionId) {
    if (!this._controlCenter || !this._controlCenter.isConnected || !this._feedbackAllows('standard')) return;
    const id = this._controlCenterActionId(actionId);
    if (this._controlCenterFeedbackTimer) clearTimeout(this._controlCenterFeedbackTimer);
    this._clearControlCenterFeedback();
    const panel = this._controlCenter;
    const button = panel.querySelector(`.wm-control-button[data-control-action="${CSS.escape(id)}"]`);
    panel.dataset.controlFeedback = id;
    panel.classList.remove('action-feedback');
    void panel.offsetWidth;
    panel.classList.add('action-feedback');
    if (button) {
      button.dataset.controlFeedback = id;
      button.classList.remove('action-feedback');
      void button.offsetWidth;
      button.classList.add('action-feedback');
    }
    this._controlCenterFeedbackTimer = setTimeout(() => {
      this._clearControlCenterFeedback();
      this._controlCenterFeedbackTimer = 0;
    }, 560);
  }

  _clearControlCenterFeedback() {
    if (!this._controlCenter || !this._controlCenter.isConnected) return;
    const panel = this._controlCenter;
    delete panel.dataset.controlFeedback;
    panel.classList.remove('action-feedback');
    panel.querySelectorAll('.wm-control-button.action-feedback').forEach((button) => {
      button.classList.remove('action-feedback');
      delete button.dataset.controlFeedback;
    });
  }

  _setMotionFromControlCenter(preference) {
    this.setMotionPreference(preference);
    const shelf = this._ensureDesktopWidgets();
    const value = shelf ? shelf.querySelector('.wm-widget-system .wm-desktop-widget-value') : null;
    if (value) value.textContent = this._normalizeMotionPreference(preference);
  }

  _setTransparencyFromControlCenter(preference) {
    const transparency = this.setTransparencyPreference(preference);
    const shelf = this._ensureDesktopWidgets();
    const value = shelf ? shelf.querySelector('.wm-widget-system .wm-desktop-widget-meta') : null;
    if (value) value.textContent = 'material: ' + transparency;
    this._sendWindowCmd('transparency_pick', { transparency_id: transparency });
  }

  _setWallpaperFromControlCenter(preference) {
    const wallpaper = this.setWallpaperPreference(preference);
    const shelf = this._ensureDesktopWidgets();
    const value = shelf ? shelf.querySelector('.wm-widget-workspace .wm-desktop-widget-meta') : null;
    if (value) value.textContent = 'wallpaper: ' + wallpaper;
    this._sendWindowCmd('wallpaper_pick', { wallpaper_id: wallpaper });
  }

  _setAccentFromControlCenter(preference) {
    const accentId = this.setAccentPreference(preference);
    this._sendWindowCmd('accent_pick', { accent_id: accentId });
    if (this._controlCenter && !this._controlCenter.hidden) this._renderControlCenter();
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
    return accentId;
  }

  _setCornerRadiusFromControlCenter(preference) {
    const radius = this.setCornerRadiusPreference(preference);
    this._sendWindowCmd('corner_radius_pick', { corner_radius_id: radius });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
    return radius;
  }

  _ensureWallpaperPicker() {
    if (this._wallpaperPicker && this._wallpaperPicker.isConnected) return this._wallpaperPicker;
    const picker = document.createElement('aside');
    picker.className = 'wm-wallpaper-picker';
    picker.hidden = true;
    picker.setAttribute('role', 'dialog');
    picker.setAttribute('aria-label', 'Wallpaper picker');
    picker.dataset.wallpaperSource = 'desktop-background';
    picker.addEventListener('pointerdown', (event) => event.stopPropagation());
    picker.addEventListener('mousedown', (event) => event.stopPropagation());
    picker.addEventListener('click', (event) => {
      const close = event.target.closest('[data-wallpaper-action="close"]');
      if (close && picker.contains(close)) {
        this._toggleWallpaperPicker(false);
        return;
      }
      const choice = event.target.closest('.wm-wallpaper-choice');
      if (!choice || !picker.contains(choice)) return;
      this._wallpaperPickerActiveIndex = Number(choice.dataset.wallpaperIndex || '0') || 0;
      this._selectWallpaperChoice(choice.dataset.wallpaperChoice || '');
    });
    picker.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveWallpaperPickerSelection(1);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveWallpaperPickerSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._setWallpaperPickerSelection(0);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._setWallpaperPickerSelection(this._wallpaperChoices().length - 1);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateWallpaperPickerSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleWallpaperPicker(false);
      }
    });
    document.body.appendChild(picker);
    this._wallpaperPicker = picker;
    return picker;
  }

  _toggleWallpaperPicker(open = null) {
    const picker = this._ensureWallpaperPicker();
    const shouldOpen = open == null ? picker.hidden : open;
    picker.hidden = !shouldOpen;
    if (shouldOpen) this._renderWallpaperPicker();
    return shouldOpen;
  }

  _renderWallpaperPicker() {
    const picker = this._ensureWallpaperPicker();
    const active = this._normalizeWallpaperPreference(this._readWallpaperPreference());
    const choices = this._wallpaperChoices();
    const activeIndex = choices.findIndex((choice) => choice.id === active);
    if (activeIndex >= 0) this._wallpaperPickerActiveIndex = activeIndex;
    picker.innerHTML = '';
    picker.setAttribute('aria-activedescendant', `wm-wallpaper-choice-${this._wallpaperPickerActiveIndex}`);
    picker.dataset.wallpaperActiveIndex = String(this._wallpaperPickerActiveIndex);
    const header = document.createElement('div');
    header.className = 'wm-wallpaper-header';
    const title = document.createElement('div');
    title.className = 'wm-wallpaper-title';
    title.textContent = 'Wallpaper';
    const close = document.createElement('button');
    close.type = 'button';
    close.className = 'wm-wallpaper-action';
    close.dataset.wallpaperAction = 'close';
    close.setAttribute('aria-label', 'Close wallpaper picker');
    close.textContent = 'Close';
    header.appendChild(title);
    header.appendChild(close);
    picker.appendChild(header);
    const grid = document.createElement('div');
    grid.className = 'wm-wallpaper-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Available wallpapers');
    grid.setAttribute('aria-activedescendant', `wm-wallpaper-choice-${this._wallpaperPickerActiveIndex}`);
    choices.forEach((choice, index) => grid.appendChild(this._makeWallpaperChoice(choice, index)));
    picker.appendChild(grid);
  }

  _wallpaperChoices() {
    return [
      { id: 'aurora', label: 'Aurora', meta: 'animated glow' },
      { id: 'mesh', label: 'Mesh', meta: 'soft gradient mesh' },
      { id: 'solid', label: 'Solid', meta: 'quiet solid surface' }
    ];
  }

  _makeWallpaperChoice(choice, index) {
    const selected = choice.id === this._normalizeWallpaperPreference(this._readWallpaperPreference());
    const active = index === this._wallpaperPickerActiveIndex;
    const button = document.createElement('button');
    button.type = 'button';
    button.id = `wm-wallpaper-choice-${index}`;
    button.className = 'wm-wallpaper-choice' + (active ? ' active' : '');
    button.dataset.wallpaperChoice = choice.id;
    button.dataset.wallpaperIndex = String(index);
    button.tabIndex = active ? 0 : -1;
    button.setAttribute('role', 'option');
    button.setAttribute('aria-selected', selected ? 'true' : 'false');
    button.setAttribute('aria-pressed', selected ? 'true' : 'false');
    const swatch = document.createElement('span');
    swatch.className = 'wm-wallpaper-swatch wm-wallpaper-swatch-' + choice.id;
    const body = document.createElement('span');
    body.className = 'wm-wallpaper-body';
    const label = document.createElement('span');
    label.className = 'wm-wallpaper-label';
    label.textContent = choice.label;
    const meta = document.createElement('span');
    meta.className = 'wm-wallpaper-meta';
    meta.textContent = choice.meta;
    body.appendChild(label);
    body.appendChild(meta);
    button.appendChild(swatch);
    button.appendChild(body);
    return button;
  }

  _moveWallpaperPickerSelection(delta) {
    if (!this._wallpaperPicker || this._wallpaperPicker.hidden) return;
    const max = this._wallpaperChoices().length - 1;
    this._wallpaperPickerActiveIndex = Math.max(0, Math.min(max, this._wallpaperPickerActiveIndex + delta));
    this._syncWallpaperPickerSelection(true);
  }

  _setWallpaperPickerSelection(index) {
    if (!this._wallpaperPicker || this._wallpaperPicker.hidden) return;
    const max = this._wallpaperChoices().length - 1;
    this._wallpaperPickerActiveIndex = Math.max(0, Math.min(max, index));
    this._syncWallpaperPickerSelection(true);
  }

  _syncWallpaperPickerSelection(shouldFocus = true) {
    if (!this._wallpaperPicker) return;
    const grid = this._wallpaperPicker.querySelector('.wm-wallpaper-grid');
    const choices = grid ? Array.from(grid.querySelectorAll('.wm-wallpaper-choice')) : [];
    if (!grid || !choices.length) return;
    const activeIndex = Math.max(0, Math.min(choices.length - 1, this._wallpaperPickerActiveIndex));
    this._wallpaperPickerActiveIndex = activeIndex;
    const activeId = `wm-wallpaper-choice-${activeIndex}`;
    this._wallpaperPicker.setAttribute('aria-activedescendant', activeId);
    this._wallpaperPicker.dataset.wallpaperActiveIndex = String(activeIndex);
    grid.setAttribute('aria-activedescendant', activeId);
    choices.forEach((choice, index) => {
      const active = index === activeIndex;
      choice.classList.toggle('active', active);
      choice.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) choice.focus();
    });
  }

  _activateWallpaperPickerSelection() {
    if (!this._wallpaperPicker || this._wallpaperPicker.hidden) return;
    const choice = this._wallpaperPicker.querySelector(`.wm-wallpaper-choice[data-wallpaper-index="${this._wallpaperPickerActiveIndex}"]`);
    this._selectWallpaperChoice(choice?.dataset.wallpaperChoice || 'aurora');
  }

  _selectWallpaperChoice(preference) {
    const wallpaper = this._normalizeWallpaperPreference(preference);
    this.setWallpaperPreference(wallpaper);
    const shelf = this._ensureDesktopWidgets();
    const value = shelf ? shelf.querySelector('.wm-widget-workspace .wm-desktop-widget-meta') : null;
    if (value) value.textContent = 'wallpaper: ' + wallpaper;
    this._sendWindowCmd('wallpaper_pick', { wallpaper_id: wallpaper });
    this._renderWallpaperPicker();
  }

  _ensureAccentPalette() {
    if (this._accentPalette && this._accentPalette.isConnected) return this._accentPalette;
    const palette = document.createElement('aside');
    palette.className = 'wm-accent-palette';
    palette.hidden = true;
    palette.setAttribute('role', 'dialog');
    palette.setAttribute('aria-label', 'Accent palette');
    palette.dataset.accentSource = 'theme';
    palette.addEventListener('pointerdown', (event) => event.stopPropagation());
    palette.addEventListener('mousedown', (event) => event.stopPropagation());
    palette.addEventListener('click', (event) => {
      const choice = event.target.closest('.wm-accent-choice');
      if (!choice || !palette.contains(choice)) return;
      this._accentPaletteActiveIndex = Number(choice.dataset.accentIndex || '0') || 0;
      this._selectAccentChoice(choice.dataset.accentChoice || '');
    });
    palette.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveAccentPaletteSelection(1);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveAccentPaletteSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._setAccentPaletteSelection(0);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._setAccentPaletteSelection(this._accentChoices().length - 1);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateAccentPaletteSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleAccentPalette(false);
      }
    });
    document.body.appendChild(palette);
    this._accentPalette = palette;
    return palette;
  }

  _toggleAccentPalette(open = null) {
    const palette = this._ensureAccentPalette();
    const shouldOpen = open == null ? palette.hidden : open;
    palette.hidden = !shouldOpen;
    if (shouldOpen) this._renderAccentPalette();
    return shouldOpen;
  }

  _renderAccentPalette() {
    const palette = this._ensureAccentPalette();
    const active = this._normalizeAccentPreference(this._readAccentPreference()).id;
    const choices = this._accentChoices();
    const activeIndex = choices.findIndex((choice) => choice.id === active);
    if (activeIndex >= 0) this._accentPaletteActiveIndex = activeIndex;
    palette.innerHTML = '';
    palette.setAttribute('aria-activedescendant', `wm-accent-choice-${this._accentPaletteActiveIndex}`);
    palette.dataset.accentActiveIndex = String(this._accentPaletteActiveIndex);
    const title = document.createElement('div');
    title.className = 'wm-accent-title';
    title.textContent = 'Accent';
    palette.appendChild(title);
    const grid = document.createElement('div');
    grid.className = 'wm-accent-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Available accent colors');
    grid.setAttribute('aria-activedescendant', `wm-accent-choice-${this._accentPaletteActiveIndex}`);
    choices.forEach((choice, index) => grid.appendChild(this._makeAccentChoice(choice, index)));
    palette.appendChild(grid);
  }

  _accentChoices() {
    return [
      { id: 'blue', label: 'Blue', meta: 'clear focus', color: '#64d2ff', rgb: '100,210,255' },
      { id: 'green', label: 'Green', meta: 'steady status', color: '#30d158', rgb: '48,209,88' },
      { id: 'rose', label: 'Rose', meta: 'warm alerts', color: '#ff375f', rgb: '255,55,95' },
      { id: 'amber', label: 'Amber', meta: 'sunlit tools', color: '#ffd60a', rgb: '255,214,10' },
      { id: 'violet', label: 'Violet', meta: 'creative mode', color: '#bf5af2', rgb: '191,90,242' }
    ];
  }

  _makeAccentChoice(choice, index) {
    const selected = choice.id === this._normalizeAccentPreference(this._readAccentPreference()).id;
    const active = index === this._accentPaletteActiveIndex;
    const button = document.createElement('button');
    button.type = 'button';
    button.id = `wm-accent-choice-${index}`;
    button.className = 'wm-accent-choice' + (active ? ' active' : '');
    button.dataset.accentChoice = choice.id;
    button.dataset.accentIndex = String(index);
    button.tabIndex = active ? 0 : -1;
    button.setAttribute('role', 'option');
    button.setAttribute('aria-selected', selected ? 'true' : 'false');
    button.setAttribute('aria-pressed', selected ? 'true' : 'false');
    const swatch = document.createElement('span');
    swatch.className = 'wm-accent-swatch wm-accent-' + choice.id;
    const body = document.createElement('span');
    body.className = 'wm-accent-body';
    const label = document.createElement('span');
    label.className = 'wm-accent-label';
    label.textContent = choice.label;
    const meta = document.createElement('span');
    meta.className = 'wm-accent-meta';
    meta.textContent = choice.meta;
    body.appendChild(label);
    body.appendChild(meta);
    button.appendChild(swatch);
    button.appendChild(body);
    return button;
  }

  _moveAccentPaletteSelection(delta) {
    if (!this._accentPalette || this._accentPalette.hidden) return;
    const max = this._accentChoices().length - 1;
    this._accentPaletteActiveIndex = Math.max(0, Math.min(max, this._accentPaletteActiveIndex + delta));
    this._syncAccentPaletteSelection(true);
  }

  _setAccentPaletteSelection(index) {
    if (!this._accentPalette || this._accentPalette.hidden) return;
    const max = this._accentChoices().length - 1;
    this._accentPaletteActiveIndex = Math.max(0, Math.min(max, index));
    this._syncAccentPaletteSelection(true);
  }

  _syncAccentPaletteSelection(shouldFocus = true) {
    if (!this._accentPalette) return;
    const grid = this._accentPalette.querySelector('.wm-accent-grid');
    const choices = grid ? Array.from(grid.querySelectorAll('.wm-accent-choice')) : [];
    if (!grid || !choices.length) return;
    const activeIndex = Math.max(0, Math.min(choices.length - 1, this._accentPaletteActiveIndex));
    this._accentPaletteActiveIndex = activeIndex;
    const activeId = `wm-accent-choice-${activeIndex}`;
    this._accentPalette.setAttribute('aria-activedescendant', activeId);
    this._accentPalette.dataset.accentActiveIndex = String(activeIndex);
    grid.setAttribute('aria-activedescendant', activeId);
    choices.forEach((choice, index) => {
      const active = index === activeIndex;
      choice.classList.toggle('active', active);
      choice.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) choice.focus();
    });
  }

  _activateAccentPaletteSelection() {
    if (!this._accentPalette || this._accentPalette.hidden) return;
    const choice = this._accentPalette.querySelector(`.wm-accent-choice[data-accent-index="${this._accentPaletteActiveIndex}"]`);
    this._selectAccentChoice(choice?.dataset.accentChoice || 'blue');
  }

  _selectAccentChoice(preference) {
    const accent = this._normalizeAccentPreference(preference);
    this.setAccentPreference(accent.id);
    this._sendWindowCmd('accent_pick', { accent_id: accent.id });
    this._renderAccentPalette();
    this._markAccentPaletteFeedback(accent.id);
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _markAccentPaletteFeedback(accentId) {
    if (!this._accentPalette || !this._accentPalette.isConnected || !this._feedbackAllows('standard')) return;
    const id = this._normalizeAccentPreference(accentId).id;
    if (this._accentPaletteFeedbackTimer) clearTimeout(this._accentPaletteFeedbackTimer);
    this._clearAccentPaletteFeedback();
    const palette = this._accentPalette;
    const choice = palette.querySelector(`.wm-accent-choice[data-accent-choice="${CSS.escape(id)}"]`);
    palette.dataset.accentFeedback = 'pick';
    palette.dataset.accentFeedbackChoice = id;
    palette.classList.remove('action-feedback');
    void palette.offsetWidth;
    palette.classList.add('action-feedback');
    if (choice) {
      choice.dataset.accentFeedback = 'pick';
      choice.classList.remove('action-feedback');
      void choice.offsetWidth;
      choice.classList.add('action-feedback');
      const swatch = choice.querySelector('.wm-accent-swatch');
      if (swatch) swatch.classList.add('action-feedback');
    }
    this._accentPaletteFeedbackTimer = setTimeout(() => {
      this._clearAccentPaletteFeedback();
      this._accentPaletteFeedbackTimer = 0;
    }, 560);
  }

  _clearAccentPaletteFeedback() {
    if (!this._accentPalette || !this._accentPalette.isConnected) return;
    const palette = this._accentPalette;
    delete palette.dataset.accentFeedback;
    delete palette.dataset.accentFeedbackChoice;
    palette.classList.remove('action-feedback');
    palette.querySelectorAll('.wm-accent-choice.action-feedback').forEach((choice) => {
      choice.classList.remove('action-feedback');
      delete choice.dataset.accentFeedback;
    });
    palette.querySelectorAll('.wm-accent-swatch.action-feedback').forEach((swatch) => {
      swatch.classList.remove('action-feedback');
    });
  }

  _ensureDockStack() {
    if (this._dockStack && this._dockStack.isConnected) return this._dockStack;
    const stack = document.createElement('aside');
    stack.className = 'wm-dock-stack';
    stack.hidden = true;
    stack.setAttribute('role', 'dialog');
    stack.setAttribute('aria-label', 'Dock stack Downloads');
    stack.dataset.stackSource = 'dock';
    stack.addEventListener('pointerdown', (event) => event.stopPropagation());
    stack.addEventListener('mousedown', (event) => event.stopPropagation());
    stack.addEventListener('click', (event) => {
      const mode = event.target.closest('[data-stack-mode]');
      if (mode && stack.contains(mode)) {
        this._setDockStackMode(mode.dataset.stackMode || 'fan');
        return;
      }
      const item = event.target.closest('.wm-dock-stack-item');
      if (!item || !stack.contains(item)) return;
      this._dockStackActiveIndex = Number(item.dataset.stackIndex || '0') || 0;
      this._openDockStackItem(item.dataset.stackItem || '');
    });
    stack.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveDockStackSelection(1);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveDockStackSelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._moveDockStackSelection(-999);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._moveDockStackSelection(999);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateDockStackSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleDockStack(false);
      }
    });
    document.body.appendChild(stack);
    this._dockStack = stack;
    return stack;
  }

  _toggleDockStack(open = null) {
    const stack = this._ensureDockStack();
    const shouldOpen = open == null ? stack.hidden : open;
    stack.hidden = !shouldOpen;
    if (shouldOpen) this._renderDockStack();
    return shouldOpen;
  }

  _renderDockStack() {
    const stack = this._ensureDockStack();
    const mode = this._dockStackMode === 'grid' ? 'grid' : 'fan';
    stack.dataset.stackLayout = 'fan-grid';
    stack.dataset.stackModeActive = mode;
    stack.innerHTML = '';
    const header = document.createElement('div');
    header.className = 'wm-dock-stack-header';
    const title = document.createElement('div');
    title.className = 'wm-dock-stack-title';
    title.textContent = 'Downloads';
    const modes = document.createElement('div');
    modes.className = 'wm-dock-stack-modes';
    modes.appendChild(this._makeDockStackModeButton('fan', mode === 'fan'));
    modes.appendChild(this._makeDockStackModeButton('grid', mode === 'grid'));
    header.appendChild(title);
    header.appendChild(modes);
    stack.appendChild(header);
    const list = document.createElement('div');
    list.className = 'wm-dock-stack-list ' + mode;
    list.setAttribute('role', 'listbox');
    list.setAttribute('aria-label', 'Downloads stack items');
    list.setAttribute('aria-activedescendant', `wm-dock-stack-item-${this._dockStackActiveIndex}`);
    this._dockStackItems().forEach((item, index) => list.appendChild(this._makeDockStackItem(item, index)));
    stack.appendChild(list);
    this._syncDockStackSelection(false);
  }

  _dockStackItems() {
    return [
      { id: 'screenshot', icon: 'S', label: 'Screenshot', meta: 'PNG image' },
      { id: 'report', icon: 'R', label: 'Quality report', meta: 'Markdown' },
      { id: 'archive', icon: 'A', label: 'Build archive', meta: 'Zip file' }
    ];
  }

  _makeDockStackModeButton(mode, active) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-dock-stack-mode' + (active ? ' active' : '');
    button.dataset.stackMode = mode;
    button.setAttribute('aria-pressed', active ? 'true' : 'false');
    button.textContent = mode;
    return button;
  }

  _makeDockStackItem(item, index) {
    const button = document.createElement('button');
    const active = index === this._dockStackActiveIndex;
    button.type = 'button';
    button.id = `wm-dock-stack-item-${index}`;
    button.className = 'wm-dock-stack-item' + (active ? ' active' : '');
    button.dataset.stackItem = item.id;
    button.dataset.stackIndex = String(index);
    button.setAttribute('role', 'option');
    button.setAttribute('aria-selected', active ? 'true' : 'false');
    button.tabIndex = active ? 0 : -1;
    button.appendChild(this._makeRoundIcon('wm-dock-stack-icon', item.icon));
    const body = document.createElement('span');
    body.className = 'wm-dock-stack-body';
    const label = document.createElement('span');
    label.className = 'wm-dock-stack-label';
    label.textContent = item.label;
    const meta = document.createElement('span');
    meta.className = 'wm-dock-stack-meta';
    meta.textContent = item.meta;
    body.appendChild(label);
    body.appendChild(meta);
    button.appendChild(body);
    return button;
  }

  _setDockStackMode(mode) {
    this._dockStackMode = mode === 'grid' ? 'grid' : 'fan';
    this._sendWindowCmd('dock_stack_mode', { stack_mode: this._dockStackMode });
    this._renderDockStack();
  }

  _moveDockStackSelection(delta) {
    const stack = this._ensureDockStack();
    const items = Array.from(stack.querySelectorAll('.wm-dock-stack-item'));
    if (!items.length) return;
    const max = items.length - 1;
    this._dockStackActiveIndex = Math.max(0, Math.min(max, this._dockStackActiveIndex + delta));
    this._syncDockStackSelection(true);
  }

  _syncDockStackSelection(shouldFocus = true) {
    const stack = this._ensureDockStack();
    const list = stack.querySelector('.wm-dock-stack-list');
    const items = Array.from(stack.querySelectorAll('.wm-dock-stack-item'));
    if (!items.length) return;
    const activeIndex = Math.max(0, Math.min(items.length - 1, this._dockStackActiveIndex));
    this._dockStackActiveIndex = activeIndex;
    if (list) list.setAttribute('aria-activedescendant', `wm-dock-stack-item-${activeIndex}`);
    items.forEach((item, index) => {
      const active = index === activeIndex;
      item.classList.toggle('active', active);
      item.setAttribute('aria-selected', active ? 'true' : 'false');
      item.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) item.focus();
    });
  }

  _activateDockStackSelection() {
    const stack = this._ensureDockStack();
    const item = stack.querySelector(`.wm-dock-stack-item[data-stack-index="${this._dockStackActiveIndex}"]`);
    this._openDockStackItem(item?.dataset.stackItem || '');
  }

  _openDockStackItem(itemId) {
    const item = this._dockStackItems().find((candidate) => candidate.id === itemId) || this._dockStackItems()[0];
    this._sendWindowCmd('dock_stack_open', { stack_item: item.id });
    this._showSystemHud('Dock stack', item.label, 1600);
  }

  _ensureQualityInspector() {
    if (this._qualityInspector && this._qualityInspector.isConnected) return this._qualityInspector;
    const panel = document.createElement('aside');
    panel.className = 'wm-quality-inspector';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'GUI quality inspector');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const filter = event.target.closest('[data-quality-filter]');
      if (filter && panel.contains(filter)) {
        this._setQualityFilter(filter.dataset.qualityFilter || 'all');
        return;
      }
      const check = event.target.closest('[data-quality-check]');
      if (check && panel.contains(check)) {
        this._selectQualityCheck(check.dataset.qualityCheck || 'color');
        return;
      }
      const contrastPolicy = event.target.closest('.wm-quality-contrast-policy-item');
      if (contrastPolicy && panel.contains(contrastPolicy)) {
        this._qualityContrastPolicyActiveIndex = Number(contrastPolicy.dataset.contrastPolicyIndex || '0') || 0;
        this._syncQualityContrastPolicySelection(false);
        this._activateQualityContrastPolicySelection();
        return;
      }
      const accentPolicy = event.target.closest('.wm-quality-accent-policy-item');
      if (accentPolicy && panel.contains(accentPolicy)) {
        this._qualityAccentPolicyActiveIndex = Number(accentPolicy.dataset.accentPolicyIndex || '0') || 0;
        this._syncQualityAccentPolicySelection(false);
        this._activateQualityAccentPolicySelection();
        return;
      }
      const densityPolicy = event.target.closest('.wm-quality-density-policy-item');
      if (densityPolicy && panel.contains(densityPolicy)) {
        this._qualityDensityPolicyActiveIndex = Number(densityPolicy.dataset.densityPolicyIndex || '0') || 0;
        this._syncQualityDensityPolicySelection(false);
        this._activateQualityDensityPolicySelection();
        return;
      }
      const surfaceDepthPolicy = event.target.closest('.wm-quality-surface-depth-policy-item');
      if (surfaceDepthPolicy && panel.contains(surfaceDepthPolicy)) {
        this._qualitySurfaceDepthPolicyActiveIndex = Number(surfaceDepthPolicy.dataset.surfaceDepthPolicyIndex || '0') || 0;
        this._syncQualitySurfaceDepthPolicySelection(false);
        this._activateQualitySurfaceDepthPolicySelection();
        return;
      }
      const trafficSidePolicy = event.target.closest('.wm-quality-traffic-side-policy-item');
      if (trafficSidePolicy && panel.contains(trafficSidePolicy)) {
        this._qualityTrafficSidePolicyActiveIndex = Number(trafficSidePolicy.dataset.trafficSidePolicyIndex || '0') || 0;
        this._syncQualityTrafficSidePolicySelection(false);
        this._activateQualityTrafficSidePolicySelection();
        return;
      }
      const widgetStackPolicy = event.target.closest('.wm-quality-widget-stack-policy-item');
      if (widgetStackPolicy && panel.contains(widgetStackPolicy)) {
        this._qualityWidgetStackPolicyActiveIndex = Number(widgetStackPolicy.dataset.widgetStackPolicyIndex || '0') || 0;
        this._syncQualityWidgetStackPolicySelection(false);
        this._activateQualityWidgetStackPolicySelection();
        return;
      }
      const iconMaskPolicy = event.target.closest('.wm-quality-icon-mask-policy-item');
      if (iconMaskPolicy && panel.contains(iconMaskPolicy)) {
        this._qualityIconMaskPolicyActiveIndex = Number(iconMaskPolicy.dataset.iconMaskPolicyIndex || '0') || 0;
        this._syncQualityIconMaskPolicySelection(false);
        this._activateQualityIconMaskPolicySelection();
        return;
      }
      const cornerRadiusPolicy = event.target.closest('.wm-quality-corner-radius-policy-item');
      if (cornerRadiusPolicy && panel.contains(cornerRadiusPolicy)) {
        this._qualityCornerRadiusPolicyActiveIndex = Number(cornerRadiusPolicy.dataset.cornerRadiusPolicyIndex || '0') || 0;
        this._syncQualityCornerRadiusPolicySelection(false);
        this._activateQualityCornerRadiusPolicySelection();
        return;
      }
      const materialPolicy = event.target.closest('.wm-quality-material-policy-item');
      if (materialPolicy && panel.contains(materialPolicy)) {
        this._qualityMaterialPolicyActiveIndex = Number(materialPolicy.dataset.materialPolicyIndex || '0') || 0;
        this._syncQualityMaterialPolicySelection(false);
        this._activateQualityMaterialPolicySelection();
        return;
      }
      const dockMagnificationPolicy = event.target.closest('.wm-quality-dock-magnification-policy-item');
      if (dockMagnificationPolicy && panel.contains(dockMagnificationPolicy)) {
        this._qualityDockMagnificationPolicyActiveIndex = Number(dockMagnificationPolicy.dataset.dockMagnificationPolicyIndex || '0') || 0;
        this._syncQualityDockMagnificationPolicySelection(false);
        this._activateQualityDockMagnificationPolicySelection();
        return;
      }
      const dockVisibilityPolicy = event.target.closest('.wm-quality-dock-visibility-policy-item');
      if (dockVisibilityPolicy && panel.contains(dockVisibilityPolicy)) {
        this._qualityDockVisibilityPolicyActiveIndex = Number(dockVisibilityPolicy.dataset.dockVisibilityPolicyIndex || '0') || 0;
        this._syncQualityDockVisibilityPolicySelection(false);
        this._activateQualityDockVisibilityPolicySelection();
        return;
      }
      const backdropPolicy = event.target.closest('.wm-quality-backdrop-policy-item');
      if (backdropPolicy && panel.contains(backdropPolicy)) {
        this._qualityBackdropPolicyActiveIndex = Number(backdropPolicy.dataset.backdropPolicyIndex || '0') || 0;
        this._syncQualityBackdropPolicySelection(false);
        this._activateQualityBackdropPolicySelection();
        return;
      }
      const wallpaperPolicy = event.target.closest('.wm-quality-wallpaper-policy-item');
      if (wallpaperPolicy && panel.contains(wallpaperPolicy)) {
        this._qualityWallpaperPolicyActiveIndex = Number(wallpaperPolicy.dataset.wallpaperPolicyIndex || '0') || 0;
        this._syncQualityWallpaperPolicySelection(false);
        this._activateQualityWallpaperPolicySelection();
        return;
      }
      const titleCommandPolicy = event.target.closest('.wm-quality-title-command-policy-item');
      if (titleCommandPolicy && panel.contains(titleCommandPolicy)) {
        this._qualityTitleCommandPolicyActiveIndex = Number(titleCommandPolicy.dataset.titleCommandPolicyIndex || '0') || 0;
        this._syncQualityTitleCommandPolicySelection(false);
        this._activateQualityTitleCommandPolicySelection();
        return;
      }
      const windowTransitionPolicy = event.target.closest('.wm-quality-window-transition-policy-item');
      if (windowTransitionPolicy && panel.contains(windowTransitionPolicy)) {
        this._qualityWindowTransitionPolicyActiveIndex = Number(windowTransitionPolicy.dataset.windowTransitionPolicyIndex || '0') || 0;
        this._syncQualityWindowTransitionPolicySelection(false);
        this._activateQualityWindowTransitionPolicySelection();
        return;
      }
      const animationStylePolicy = event.target.closest('.wm-quality-animation-style-policy-item');
      if (animationStylePolicy && panel.contains(animationStylePolicy)) {
        this._qualityAnimationStylePolicyActiveIndex = Number(animationStylePolicy.dataset.animationStylePolicyIndex || '0') || 0;
        this._syncQualityAnimationStylePolicySelection(false);
        this._activateQualityAnimationStylePolicySelection();
        return;
      }
      const chromeVerbosityPolicy = event.target.closest('.wm-quality-chrome-verbosity-policy-item');
      if (chromeVerbosityPolicy && panel.contains(chromeVerbosityPolicy)) {
        this._qualityChromeVerbosityPolicyActiveIndex = Number(chromeVerbosityPolicy.dataset.chromeVerbosityPolicyIndex || '0') || 0;
        this._syncQualityChromeVerbosityPolicySelection(false);
        this._activateQualityChromeVerbosityPolicySelection();
        return;
      }
      const feedbackPolicy = event.target.closest('.wm-quality-feedback-policy-item');
      if (feedbackPolicy && panel.contains(feedbackPolicy)) {
        this._qualityFeedbackPolicyActiveIndex = Number(feedbackPolicy.dataset.feedbackPolicyIndex || '0') || 0;
        this._syncQualityFeedbackPolicySelection(false);
        this._activateQualityFeedbackPolicySelection();
        return;
      }
      const energyPolicy = event.target.closest('.wm-quality-energy-policy-item');
      if (energyPolicy && panel.contains(energyPolicy)) {
        this._qualityEnergyPolicyActiveIndex = Number(energyPolicy.dataset.energyPolicyIndex || '0') || 0;
        this._syncQualityEnergyPolicySelection(false);
        this._activateQualityEnergyPolicySelection();
        return;
      }
      const mode = event.target.closest('[data-quality-mode]');
      if (mode && panel.contains(mode)) {
        this._setQualityAuditMode(mode.dataset.qualityMode || 'full');
        return;
      }
      const fix = event.target.closest('[data-quality-fix]');
      if (fix && panel.contains(fix)) {
        this._applyQualityFix(fix.dataset.qualityFix || this._selectedQualityCheck);
        return;
      }
      const action = event.target.closest('[data-quality-action]');
      if (!action || !panel.contains(action)) return;
      this._activateQualityInspectorAction(action.dataset.qualityAction || '');
    });
    panel.addEventListener('keydown', (event) => {
      const target = event.target instanceof Element ? event.target : null;
      const contrastPolicy = target ? target.closest('.wm-quality-contrast-policy-item') : null;
      const accentPolicy = target ? target.closest('.wm-quality-accent-policy-item') : null;
      const densityPolicy = target ? target.closest('.wm-quality-density-policy-item') : null;
      const surfaceDepthPolicy = target ? target.closest('.wm-quality-surface-depth-policy-item') : null;
      const trafficSidePolicy = target ? target.closest('.wm-quality-traffic-side-policy-item') : null;
      const widgetStackPolicy = target ? target.closest('.wm-quality-widget-stack-policy-item') : null;
      const iconMaskPolicy = target ? target.closest('.wm-quality-icon-mask-policy-item') : null;
      const cornerRadiusPolicy = target ? target.closest('.wm-quality-corner-radius-policy-item') : null;
      const materialPolicy = target ? target.closest('.wm-quality-material-policy-item') : null;
      const dockMagnificationPolicy = target ? target.closest('.wm-quality-dock-magnification-policy-item') : null;
      const dockVisibilityPolicy = target ? target.closest('.wm-quality-dock-visibility-policy-item') : null;
      const backdropPolicy = target ? target.closest('.wm-quality-backdrop-policy-item') : null;
      const wallpaperPolicy = target ? target.closest('.wm-quality-wallpaper-policy-item') : null;
      const titleCommandPolicy = target ? target.closest('.wm-quality-title-command-policy-item') : null;
      const windowTransitionPolicy = target ? target.closest('.wm-quality-window-transition-policy-item') : null;
      const animationStylePolicy = target ? target.closest('.wm-quality-animation-style-policy-item') : null;
      const chromeVerbosityPolicy = target ? target.closest('.wm-quality-chrome-verbosity-policy-item') : null;
      const feedbackPolicy = target ? target.closest('.wm-quality-feedback-policy-item') : null;
      const energyPolicy = target ? target.closest('.wm-quality-energy-policy-item') : null;
      if ((!contrastPolicy || !panel.contains(contrastPolicy)) && (!accentPolicy || !panel.contains(accentPolicy)) && (!densityPolicy || !panel.contains(densityPolicy)) && (!surfaceDepthPolicy || !panel.contains(surfaceDepthPolicy)) && (!trafficSidePolicy || !panel.contains(trafficSidePolicy)) && (!widgetStackPolicy || !panel.contains(widgetStackPolicy)) && (!iconMaskPolicy || !panel.contains(iconMaskPolicy)) && (!cornerRadiusPolicy || !panel.contains(cornerRadiusPolicy)) && (!materialPolicy || !panel.contains(materialPolicy)) && (!dockMagnificationPolicy || !panel.contains(dockMagnificationPolicy)) && (!dockVisibilityPolicy || !panel.contains(dockVisibilityPolicy)) && (!backdropPolicy || !panel.contains(backdropPolicy)) && (!wallpaperPolicy || !panel.contains(wallpaperPolicy)) && (!titleCommandPolicy || !panel.contains(titleCommandPolicy)) && (!windowTransitionPolicy || !panel.contains(windowTransitionPolicy)) && (!animationStylePolicy || !panel.contains(animationStylePolicy)) && (!chromeVerbosityPolicy || !panel.contains(chromeVerbosityPolicy)) && (!feedbackPolicy || !panel.contains(feedbackPolicy)) && (!energyPolicy || !panel.contains(energyPolicy))) return;
      const moveSelection = (delta) => {
        if (contrastPolicy) this._moveQualityContrastPolicySelection(delta);
        if (accentPolicy) this._moveQualityAccentPolicySelection(delta);
        if (densityPolicy) this._moveQualityDensityPolicySelection(delta);
        if (surfaceDepthPolicy) this._moveQualitySurfaceDepthPolicySelection(delta);
        if (trafficSidePolicy) this._moveQualityTrafficSidePolicySelection(delta);
        if (widgetStackPolicy) this._moveQualityWidgetStackPolicySelection(delta);
        if (iconMaskPolicy) this._moveQualityIconMaskPolicySelection(delta);
        if (cornerRadiusPolicy) this._moveQualityCornerRadiusPolicySelection(delta);
        if (materialPolicy) this._moveQualityMaterialPolicySelection(delta);
        if (dockMagnificationPolicy) this._moveQualityDockMagnificationPolicySelection(delta);
        if (dockVisibilityPolicy) this._moveQualityDockVisibilityPolicySelection(delta);
        if (backdropPolicy) this._moveQualityBackdropPolicySelection(delta);
        if (wallpaperPolicy) this._moveQualityWallpaperPolicySelection(delta);
        if (titleCommandPolicy) this._moveQualityTitleCommandPolicySelection(delta);
        if (windowTransitionPolicy) this._moveQualityWindowTransitionPolicySelection(delta);
        if (animationStylePolicy) this._moveQualityAnimationStylePolicySelection(delta);
        if (chromeVerbosityPolicy) this._moveQualityChromeVerbosityPolicySelection(delta);
        if (feedbackPolicy) this._moveQualityFeedbackPolicySelection(delta);
        if (energyPolicy) this._moveQualityEnergyPolicySelection(delta);
      };
      const setSelection = (index) => {
        if (contrastPolicy) this._setQualityContrastPolicySelection(index);
        if (accentPolicy) this._setQualityAccentPolicySelection(index);
        if (densityPolicy) this._setQualityDensityPolicySelection(index);
        if (surfaceDepthPolicy) this._setQualitySurfaceDepthPolicySelection(index);
        if (trafficSidePolicy) this._setQualityTrafficSidePolicySelection(index);
        if (widgetStackPolicy) this._setQualityWidgetStackPolicySelection(index);
        if (iconMaskPolicy) this._setQualityIconMaskPolicySelection(index);
        if (cornerRadiusPolicy) this._setQualityCornerRadiusPolicySelection(index);
        if (materialPolicy) this._setQualityMaterialPolicySelection(index);
        if (dockMagnificationPolicy) this._setQualityDockMagnificationPolicySelection(index);
        if (dockVisibilityPolicy) this._setQualityDockVisibilityPolicySelection(index);
        if (backdropPolicy) this._setQualityBackdropPolicySelection(index);
        if (wallpaperPolicy) this._setQualityWallpaperPolicySelection(index);
        if (titleCommandPolicy) this._setQualityTitleCommandPolicySelection(index);
        if (windowTransitionPolicy) this._setQualityWindowTransitionPolicySelection(index);
        if (animationStylePolicy) this._setQualityAnimationStylePolicySelection(index);
        if (chromeVerbosityPolicy) this._setQualityChromeVerbosityPolicySelection(index);
        if (feedbackPolicy) this._setQualityFeedbackPolicySelection(index);
        if (energyPolicy) this._setQualityEnergyPolicySelection(index);
      };
      const itemCount = contrastPolicy ? this._qualityContrastPolicyItems().length : accentPolicy ? this._qualityAccentPolicyItems().length : densityPolicy ? this._qualityDensityPolicyItems().length : surfaceDepthPolicy ? this._qualitySurfaceDepthPolicyItems().length : trafficSidePolicy ? this._qualityTrafficSidePolicyItems().length : widgetStackPolicy ? this._qualityWidgetStackPolicyItems().length : iconMaskPolicy ? this._qualityIconMaskPolicyItems().length : cornerRadiusPolicy ? this._qualityCornerRadiusPolicyItems().length : materialPolicy ? this._qualityMaterialPolicyItems().length : dockMagnificationPolicy ? this._qualityDockMagnificationPolicyItems().length : dockVisibilityPolicy ? this._qualityDockVisibilityPolicyItems().length : backdropPolicy ? this._qualityBackdropPolicyItems().length : wallpaperPolicy ? this._qualityWallpaperPolicyItems().length : titleCommandPolicy ? this._qualityTitleCommandPolicyItems().length : windowTransitionPolicy ? this._qualityWindowTransitionPolicyItems().length : animationStylePolicy ? this._qualityAnimationStylePolicyItems().length : chromeVerbosityPolicy ? this._qualityChromeVerbosityPolicyItems().length : feedbackPolicy ? this._qualityFeedbackPolicyItems().length : this._qualityEnergyPolicyItems().length;
      const activateSelection = () => {
        if (contrastPolicy) this._activateQualityContrastPolicySelection();
        if (accentPolicy) this._activateQualityAccentPolicySelection();
        if (densityPolicy) this._activateQualityDensityPolicySelection();
        if (surfaceDepthPolicy) this._activateQualitySurfaceDepthPolicySelection();
        if (trafficSidePolicy) this._activateQualityTrafficSidePolicySelection();
        if (widgetStackPolicy) this._activateQualityWidgetStackPolicySelection();
        if (iconMaskPolicy) this._activateQualityIconMaskPolicySelection();
        if (cornerRadiusPolicy) this._activateQualityCornerRadiusPolicySelection();
        if (materialPolicy) this._activateQualityMaterialPolicySelection();
        if (dockMagnificationPolicy) this._activateQualityDockMagnificationPolicySelection();
        if (dockVisibilityPolicy) this._activateQualityDockVisibilityPolicySelection();
        if (backdropPolicy) this._activateQualityBackdropPolicySelection();
        if (wallpaperPolicy) this._activateQualityWallpaperPolicySelection();
        if (titleCommandPolicy) this._activateQualityTitleCommandPolicySelection();
        if (windowTransitionPolicy) this._activateQualityWindowTransitionPolicySelection();
        if (animationStylePolicy) this._activateQualityAnimationStylePolicySelection();
        if (chromeVerbosityPolicy) this._activateQualityChromeVerbosityPolicySelection();
        if (feedbackPolicy) this._activateQualityFeedbackPolicySelection();
        if (energyPolicy) this._activateQualityEnergyPolicySelection();
      };
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        moveSelection(1);
        return;
      }
      if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        moveSelection(-1);
        return;
      }
      if (event.key === 'Home') {
        event.preventDefault();
        setSelection(0);
        return;
      }
      if (event.key === 'End') {
        event.preventDefault();
        setSelection(itemCount - 1);
        return;
      }
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        activateSelection();
      }
    });
    document.body.appendChild(panel);
    this._qualityInspector = panel;
    return panel;
  }

  _toggleQualityInspector(open = null) {
    const panel = this._ensureQualityInspector();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderQualityInspector();
    return shouldOpen;
  }

  _renderQualityInspector() {
    const panel = this._ensureQualityInspector();
    panel.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-quality-title';
    title.textContent = 'Quality';
    panel.appendChild(title);
    const items = this._qualityInspectorItems();
    panel.appendChild(this._makeQualitySummary(items));
    panel.appendChild(this._makeQualityAuditModes());
    panel.appendChild(this._makeQualityFilters());
    const visibleItems = this._filteredQualityItems(items);
    if (visibleItems.length > 0 && !visibleItems.some((item) => item.key === this._selectedQualityCheck)) {
      this._selectedQualityCheck = visibleItems[0].key;
    }
    const grid = document.createElement('div');
    grid.className = 'wm-quality-grid';
    visibleItems.forEach((item) => grid.appendChild(this._makeQualityInspectorRow(item)));
    panel.appendChild(grid);
    panel.appendChild(this._makeQualityColorPreview());
    panel.appendChild(this._makeQualityComputedColorPreview());
    panel.appendChild(this._makeQualityLayoutPreview());
    panel.appendChild(this._makeQualityComputedLayoutPreview());
    panel.appendChild(this._makeQualityComputedDensityPreview());
    panel.appendChild(this._makeQualityComputedShapePreview());
    panel.appendChild(this._makeQualityTitlebarPreview());
    panel.appendChild(this._makeQualityComputedTitlebarPreview());
    panel.appendChild(this._makeQualityComputedTrafficPreview());
    panel.appendChild(this._makeQualityComputedCommandPreview());
    panel.appendChild(this._makeQualityIconPreview());
    panel.appendChild(this._makeQualityComputedIconPreview());
    panel.appendChild(this._makeQualityComputedIconKitPreview());
    panel.appendChild(this._makeQualityComputedScrollbarPreview());
    panel.appendChild(this._makeQualityTypographyPreview());
    panel.appendChild(this._makeQualityDepthPreview());
    panel.appendChild(this._makeQualityInteractionPreview());
    panel.appendChild(this._makeQualityComputedShortcutPreview());
    panel.appendChild(this._makeQualityComputedMultitaskingPreview());
    panel.appendChild(this._makeQualityComputedWorkspaceControlsPreview());
    panel.appendChild(this._makeQualityComputedWindowActionsPreview());
    panel.appendChild(this._makeQualityStatePreview());
    panel.appendChild(this._makeQualityComputedLifecyclePreview());
    panel.appendChild(this._makeQualityVerbosityPreview());
    panel.appendChild(this._makeQualityComputedPersonalizationPreview());
    panel.appendChild(this._makeQualityComputedControlCenterPreview());
    panel.appendChild(this._makeQualityComputedOsToolsPreview());
    panel.appendChild(this._makeQualityPerformancePreview());
    panel.appendChild(this._makeQualityComputedBackdropPreview());
    panel.appendChild(this._makeQualityComputedWallpaperPreview());
    panel.appendChild(this._makeQualityComputedMotionPreview());
    panel.appendChild(this._makeQualityComputedMotionBudgetPreview());
    panel.appendChild(this._makeQualitySpatialPreview());
    panel.appendChild(this._makeQualityComputedSpatialPreview());
    panel.appendChild(this._makeQualityDockPreview());
    panel.appendChild(this._makeQualityComputedDockPreview());
    panel.appendChild(this._makeQualityResponsivePreview());
    panel.appendChild(this._makeQualityViewportPreview());
    panel.appendChild(this._makeQualityAccessibilityPreview());
    panel.appendChild(this._makeQualityComputedAccessibilityPreview());
    panel.appendChild(this._makeQualityComputedStatusPreview());
    panel.appendChild(this._makeQualityComputedProductivityPreview());
    panel.appendChild(this._makeQualityMotionPreview());
    panel.appendChild(this._makeQualityAnimationPreview());
    panel.appendChild(this._makeQualityWidgetPreview());
    panel.appendChild(this._makeQualityComputedWidgetPreview());
    panel.appendChild(this._makeQualityMaterialPreview());
    panel.appendChild(this._makeQualityComputedMaterialPreview());
    panel.appendChild(this._makeQualitySurfacePreview());
    panel.appendChild(this._makeQualityComputedSurfacePreview());
    if (this._qualityAuditMode === 'full') {
      panel.appendChild(this._makeQualityCheckDetail(items));
      panel.appendChild(this._makeQualityDetailPanel());
    }
    panel.appendChild(this._makeQualityRecommendations(items));
    panel.appendChild(this._makeQualityReportPreview(items));
    panel.appendChild(this._makeQualityEvidencePreview());
    panel.appendChild(this._makeQualityActions());
  }

  _qualityInspectorItems() {
    const root = getComputedStyle(document.documentElement);
    const body = getComputedStyle(document.body);
    const titlebar = document.querySelector('.wm-titlebar');
    const command = document.querySelector('.wm-command-palette');
    const taskbarItem = document.querySelector('.wm-taskbar-item');
    const titleInput = document.querySelector('.wm-title-input, .wm-command-bar');
    const contrast = this._qualityContrastRatio(root.getPropertyValue('--ui-bg') || body.backgroundColor, root.getPropertyValue('--ui-text') || body.color);
    return [
      { key: 'color', category: 'visual', label: 'Color contrast', value: contrast + ':1', threshold: '>= 4.5:1', source: '--ui-bg / --ui-text', fix: 'Adjust theme contrast tokens', good: contrast >= 4.5 },
      { key: 'touch', category: 'layout', label: 'Touch target', value: this._qualityElementMinHeight(taskbarItem) + 'px', threshold: '>= 34px', source: '.wm-taskbar-item', fix: 'Raise taskbar hit area', good: this._qualityElementMinHeight(taskbarItem) >= 34 },
      { key: 'titlebar', category: 'layout', label: 'Titlebar height', value: this._qualityElementHeight(titlebar) + 'px', threshold: '>= 38px', source: '.wm-titlebar', fix: 'Increase titlebar height token', good: this._qualityElementHeight(titlebar) >= 38 },
      { key: 'input', category: 'layout', label: 'Title input', value: this._qualityElementWidth(titleInput) + 'px', threshold: '>= 140px', source: '.wm-title-input', fix: 'Widen command input track', good: this._qualityElementWidth(titleInput) >= 140 },
      { key: 'bounds', category: 'layout', label: 'Command bounds', value: this._qualityElementWidth(command) + 'px', threshold: '<= 680px', source: '.wm-command-palette', fix: 'Clamp command palette width', good: this._qualityElementWidth(command) <= 680 },
      { key: 'motion', category: 'motion', label: 'Motion mode', value: this._normalizeMotionPreference(this._readMotionPreference()), threshold: 'standard or reduced', source: 'simple.wm.motion', fix: 'Use motion preference toggle', good: true },
      { key: 'material', category: 'material', label: 'Material policy', value: this._normalizeTransparencyPreference(this._readTransparencyPreference()), threshold: 'standard or reduced', source: 'simple.wm.transparency', fix: 'Use transparency preference toggle', good: true }
    ];
  }

  _qualityFilterItems() {
    return [
      { id: 'all', label: 'All' },
      { id: 'layout', label: 'Layout' },
      { id: 'visual', label: 'Visual' },
      { id: 'motion', label: 'Motion' },
      { id: 'material', label: 'Material' }
    ];
  }

  _makeQualityFilters() {
    const filters = document.createElement('div');
    filters.className = 'wm-quality-filters';
    filters.setAttribute('role', 'group');
    filters.setAttribute('aria-label', 'Quality filters');
    this._qualityFilterItems().forEach((item) => {
      const button = document.createElement('button');
      const active = item.id === this._qualityFilter;
      button.type = 'button';
      button.className = 'wm-quality-filter' + (active ? ' active' : '');
      button.dataset.qualityFilter = item.id;
      button.setAttribute('aria-pressed', active ? 'true' : 'false');
      button.textContent = item.label;
      filters.appendChild(button);
    });
    return filters;
  }

  _setQualityFilter(filter) {
    const next = this._qualityFilterItems().some((item) => item.id === filter) ? filter : 'all';
    if (next === this._qualityFilter) return;
    this._qualityFilter = next;
    this._sendWindowCmd('quality_filter', { quality_filter: next });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _filteredQualityItems(items) {
    if (this._qualityFilter === 'all') return items;
    return items.filter((item) => item.category === this._qualityFilter);
  }

  _qualityAuditModeItems() {
    return [
      { id: 'full', label: 'Full' },
      { id: 'compact', label: 'Compact' }
    ];
  }

  _makeQualityAuditModes() {
    const modes = document.createElement('div');
    modes.className = 'wm-quality-modes';
    modes.setAttribute('role', 'group');
    modes.setAttribute('aria-label', 'Quality audit mode');
    this._qualityAuditModeItems().forEach((item) => {
      const button = document.createElement('button');
      const active = item.id === this._qualityAuditMode;
      button.type = 'button';
      button.className = 'wm-quality-mode' + (active ? ' active' : '');
      button.dataset.qualityMode = item.id;
      button.setAttribute('aria-pressed', active ? 'true' : 'false');
      button.textContent = item.label;
      modes.appendChild(button);
    });
    return modes;
  }

  _setQualityAuditMode(mode) {
    const next = this._qualityAuditModeItems().some((item) => item.id === mode) ? mode : 'full';
    if (next === this._qualityAuditMode) return;
    this._qualityAuditMode = next;
    this._sendWindowCmd('quality_audit_mode', { quality_audit_mode: next });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _selectQualityCheck(check) {
    this._selectedQualityCheck = check || 'color';
    this._sendWindowCmd('quality_check', { quality_check: this._selectedQualityCheck });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualitySummary(items) {
    const passed = items.filter((item) => item.good).length;
    const total = Math.max(1, items.length);
    const score = Math.round((passed / total) * 100);
    const color = items.find((item) => item.key === 'color');
    const summary = document.createElement('div');
    summary.className = 'wm-quality-summary';
    summary.dataset.qualityScore = String(score);
    summary.appendChild(this._makeQualitySummaryMetric('Score', score + '%'));
    summary.appendChild(this._makeQualitySummaryMetric('Checks', passed + '/' + total));
    summary.appendChild(this._makeQualitySummaryMetric('Contrast', color?.value || 'n/a'));
    return summary;
  }

  _makeQualitySummaryMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-summary-metric';
    const name = document.createElement('span');
    name.className = 'wm-quality-summary-label';
    name.textContent = label;
    const number = document.createElement('strong');
    number.className = 'wm-quality-summary-value';
    number.textContent = value;
    metric.appendChild(name);
    metric.appendChild(number);
    return metric;
  }

  _makeQualityDetailPanel() {
    const root = getComputedStyle(document.documentElement);
    const panel = document.createElement('div');
    panel.className = 'wm-quality-details';
    panel.appendChild(this._makeQualitySwatches(root));
    const metrics = document.createElement('div');
    metrics.className = 'wm-quality-metrics';
    metrics.appendChild(this._makeQualityMetric('Safe area', this._qualityCssPx(root, '--ui-layout-safe-area-px', 16) + 'px'));
    metrics.appendChild(this._makeQualityMetric('Panel gap', this._qualityCssPx(root, '--ui-layout-panel-gap-px', 12) + 'px'));
    metrics.appendChild(this._makeQualityMetric('Min touch', this._qualityCssPx(root, '--ui-layout-min-touch-target-px', 44) + 'px'));
    panel.appendChild(metrics);
    panel.appendChild(this._makeQualityAuditPolicy());
    return panel;
  }

  _makeQualityColorPreview() {
    const root = getComputedStyle(document.documentElement);
    const body = getComputedStyle(document.body);
    const bg = root.getPropertyValue('--ui-bg') || body.backgroundColor;
    const text = root.getPropertyValue('--ui-text') || body.color;
    const accent = root.getPropertyValue('--ui-accent') || '#7dd3fc';
    const contrast = this._qualityContrastRatio(bg, text);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-color-preview';
    preview.dataset.qualityContrast = String(contrast);
    preview.appendChild(this._makeQualityColorMetric('Background', bg, bg));
    preview.appendChild(this._makeQualityColorMetric('Text', text, text));
    preview.appendChild(this._makeQualityColorMetric('Accent', accent, accent));
    preview.appendChild(this._makeQualityColorMetric('Contrast', contrast + ':1', accent));
    preview.appendChild(this._makeQualityContrastPolicy());
    preview.appendChild(this._makeQualityAccentPolicy());
    return preview;
  }

  _makeQualityColorMetric(label, value, swatch) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-color-metric';
    metric.dataset.colorMetric = label.toLowerCase();
    const chip = document.createElement('span');
    chip.className = 'wm-quality-color-chip';
    chip.style.background = (swatch || '').trim();
    const name = document.createElement('span');
    name.className = 'wm-quality-color-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-color-value';
    result.textContent = (value || '').trim();
    metric.appendChild(chip);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityContrastPolicy() {
    const entries = [
      ['comfortable', 'Comfortable', '4.5:1 target'],
      ['high', 'High', 'Stronger text']
    ];
    const current = this._normalizeContrastPreference(this._readContrastPreference());
    const currentIndex = entries.findIndex(([mode]) => mode === current);
    if (currentIndex >= 0) this._qualityContrastPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-contrast-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Contrast policy');
    policy.dataset.contrastPolicyActiveIndex = String(this._qualityContrastPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-contrast-policy-${this._qualityContrastPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityContrastPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-contrast-policy-${index}`;
      item.className = 'wm-quality-contrast-policy-item' + (selected ? ' selected' : '');
      item.dataset.contrastPolicy = mode;
      item.dataset.contrastPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-contrast-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-contrast-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityContrastPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-contrast-policy-item'));
  }

  _moveQualityContrastPolicySelection(delta) {
    const items = this._qualityContrastPolicyItems();
    if (!items.length) return;
    const next = (this._qualityContrastPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityContrastPolicySelection(next);
  }

  _setQualityContrastPolicySelection(index) {
    const items = this._qualityContrastPolicyItems();
    if (!items.length) return;
    this._qualityContrastPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityContrastPolicySelection();
  }

  _syncQualityContrastPolicySelection(shouldFocus = true) {
    const items = this._qualityContrastPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-contrast-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityContrastPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.contrastPolicyActiveIndex = String(this._qualityContrastPolicyActiveIndex);
  }

  _activateQualityContrastPolicySelection() {
    const item = this._qualityContrastPolicyItems()[this._qualityContrastPolicyActiveIndex];
    if (!item) return;
    const contrast = item.dataset.contrastPolicy || 'comfortable';
    this.setContrastPreference(contrast);
    this._sendWindowCmd('quality_contrast_policy', { contrast_policy: contrast });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityAccentPolicy() {
    const entries = this._accentChoices();
    const current = this._normalizeAccentPreference(this._readAccentPreference()).id;
    const currentIndex = entries.findIndex((choice) => choice.id === current);
    if (currentIndex >= 0) this._qualityAccentPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-accent-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Accent color policy');
    policy.dataset.accentPolicyActiveIndex = String(this._qualityAccentPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-accent-policy-${this._qualityAccentPolicyActiveIndex}`);
    entries.forEach((choice, index) => {
      const selected = index === this._qualityAccentPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-accent-policy-${index}`;
      item.className = 'wm-quality-accent-policy-item' + (selected ? ' selected' : '');
      item.dataset.accentPolicy = choice.id;
      item.dataset.accentPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const swatch = document.createElement('span');
      swatch.className = 'wm-quality-accent-policy-swatch';
      swatch.style.background = choice.color;
      const name = document.createElement('span');
      name.className = 'wm-quality-accent-policy-label';
      name.textContent = choice.label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-accent-policy-value';
      result.textContent = choice.meta;
      item.appendChild(swatch);
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityAccentPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-accent-policy-item'));
  }

  _moveQualityAccentPolicySelection(delta) {
    const items = this._qualityAccentPolicyItems();
    if (!items.length) return;
    const next = (this._qualityAccentPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityAccentPolicySelection(next);
  }

  _setQualityAccentPolicySelection(index) {
    const items = this._qualityAccentPolicyItems();
    if (!items.length) return;
    this._qualityAccentPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityAccentPolicySelection();
  }

  _syncQualityAccentPolicySelection(shouldFocus = true) {
    const items = this._qualityAccentPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-accent-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityAccentPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.accentPolicyActiveIndex = String(this._qualityAccentPolicyActiveIndex);
  }

  _activateQualityAccentPolicySelection() {
    const item = this._qualityAccentPolicyItems()[this._qualityAccentPolicyActiveIndex];
    if (!item) return;
    const accent = item.dataset.accentPolicy || 'blue';
    this.setAccentPreference(accent);
    this._sendWindowCmd('quality_accent_policy', { accent_policy: accent });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedColorPreview() {
    const root = getComputedStyle(document.documentElement);
    const fallbackBg = root.getPropertyValue('--ui-bg') || getComputedStyle(document.body).backgroundColor;
    const fallbackText = root.getPropertyValue('--ui-text') || getComputedStyle(document.body).color;
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-color-preview';
    preview.dataset.qualityComputedColor = 'live';
    const rows = [
      ['Window', '.wm-window.focused, .wm-window', 'window'],
      ['Command', '.wm-command-palette, .wm-title-input, .wm-command-bar', 'command'],
      ['Taskbar', '#wm-taskbar, .wm-taskbar-item', 'taskbar'],
      ['Widget', '.wm-desktop-widget, .widget-panel', 'widget']
    ].map(([label, selector, kind]) => {
      const colors = this._qualityComputedSurfaceColors(selector, fallbackBg, fallbackText);
      const ratio = this._qualityContrastRatio(colors.bg, colors.fg);
      preview.appendChild(this._makeQualityComputedColorMetric(label, ratio + ':1', kind, ratio >= 4.5));
      return { label, kind, ratio, grade: this._qualityContrastGrade(ratio) };
    });
    preview.appendChild(this._makeQualityContrastMatrix(rows));
    return preview;
  }

  _qualityContrastGrade(ratio) {
    if (ratio >= 7) return 'AAA pass';
    if (ratio >= 4.5) return 'AA pass';
    return 'Fail';
  }

  _makeQualityContrastMatrix(rows) {
    const matrix = document.createElement('div');
    matrix.className = 'wm-quality-contrast-matrix';
    matrix.dataset.qualityContrastMatrix = 'surface';
    rows.forEach((row) => {
      const item = document.createElement('span');
      item.className = 'wm-quality-contrast-matrix-item' + (row.ratio >= 4.5 ? ' good' : ' warn');
      item.dataset.contrastSurface = row.kind;
      item.dataset.contrastGrade = row.grade;
      const label = document.createElement('span');
      label.className = 'wm-quality-contrast-matrix-label';
      label.textContent = row.label;
      const value = document.createElement('strong');
      value.className = 'wm-quality-contrast-matrix-value';
      value.textContent = row.ratio + ':1 ' + row.grade;
      item.appendChild(label);
      item.appendChild(value);
      matrix.appendChild(item);
    });
    return matrix;
  }

  _makeQualityComputedColorMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-color-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedColorMetric = kind;
    const chip = document.createElement('span');
    chip.className = 'wm-quality-computed-color-chip';
    chip.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-color-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-color-value';
    result.textContent = value;
    metric.appendChild(chip);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityComputedSurfaceColors(selector, fallbackBg, fallbackText) {
    const el = document.querySelector(selector);
    if (!el) return { bg: fallbackBg, fg: fallbackText };
    const style = getComputedStyle(el);
    const bg = this._qualityVisibleColor(style.backgroundColor, fallbackBg);
    const fg = this._qualityVisibleColor(style.color, fallbackText);
    return { bg, fg };
  }

  _qualityVisibleColor(value, fallback) {
    const text = String(value || '').trim();
    if (!text || text === 'transparent' || text === 'rgba(0, 0, 0, 0)') return fallback;
    return text;
  }

  _makeQualityLayoutPreview() {
    const root = getComputedStyle(document.documentElement);
    const titlebar = document.querySelector('.wm-titlebar');
    const titleInput = document.querySelector('.wm-title-input, .wm-command-bar');
    const taskbarItem = document.querySelector('.wm-taskbar-item');
    const preview = document.createElement('div');
    preview.className = 'wm-quality-layout-preview';
    preview.dataset.qualityLayout = 'tokens';
    preview.appendChild(this._makeQualityLayoutMetric('Titlebar', this._qualityElementHeight(titlebar) + 'px'));
    preview.appendChild(this._makeQualityLayoutMetric('Title input', this._qualityElementWidth(titleInput) + 'px'));
    preview.appendChild(this._makeQualityLayoutMetric('Safe area', this._qualityCssPx(root, '--ui-layout-safe-area-px', 16) + 'px'));
    preview.appendChild(this._makeQualityLayoutMetric('Min touch', this._qualityElementMinHeight(taskbarItem) + 'px'));
    return preview;
  }

  _makeQualityLayoutMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-layout-metric';
    metric.dataset.layoutMetric = label.toLowerCase().replace(/\s+/g, '_');
    const name = document.createElement('span');
    name.className = 'wm-quality-layout-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-layout-value';
    result.textContent = value;
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedLayoutPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-layout-preview';
    preview.dataset.qualityComputedLayout = 'live';
    [
      ['Window', '.wm-window.focused, .wm-window', 'window', 200, 120],
      ['Titlebar', '.wm-titlebar', 'titlebar', 0, 38],
      ['Taskbar', '#wm-taskbar', 'taskbar', 180, 34],
      ['Widget', '.wm-desktop-widget, .widget-panel', 'widget', 160, 44]
    ].forEach(([label, selector, kind, minWidth, minHeight]) => {
      const geometry = this._qualityComputedGeometry(selector, minWidth, minHeight);
      preview.appendChild(this._makeQualityComputedLayoutMetric(label, geometry.label, kind, geometry.good));
    });
    return preview;
  }

  _makeQualityComputedLayoutMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-layout-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedLayoutMetric = kind;
    const frame = document.createElement('span');
    frame.className = 'wm-quality-computed-layout-frame';
    frame.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-layout-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-layout-value';
    result.textContent = value;
    metric.appendChild(frame);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedDensityPreview() {
    const root = getComputedStyle(document.documentElement);
    const mode = document.documentElement.dataset.wmDensity || this._densityMode || 'comfortable';
    const safe = this._qualityCssPx(root, '--ui-layout-safe-area-px', 16);
    const gap = this._qualityCssPx(root, '--ui-layout-panel-gap-px', 12);
    const touch = this._qualityCssPx(root, '--ui-layout-min-touch-target-px', 44);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-density-preview';
    preview.dataset.qualityComputedDensity = mode;
    preview.appendChild(this._makeQualityComputedDensityMetric('Mode', mode, 'mode', ['compact', 'comfortable', 'spacious'].includes(mode)));
    preview.appendChild(this._makeQualityComputedDensityMetric('Safe', safe + 'px', 'safe', safe >= 12 && safe <= 24));
    preview.appendChild(this._makeQualityComputedDensityMetric('Gap', gap + 'px', 'gap', gap >= 8 && gap <= 18));
    preview.appendChild(this._makeQualityComputedDensityMetric('Touch', touch + 'px', 'touch', touch >= 44));
    preview.appendChild(this._makeQualityDensityPolicy());
    return preview;
  }

  _makeQualityComputedDensityMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-density-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedDensityMetric = kind;
    const frame = document.createElement('span');
    frame.className = 'wm-quality-computed-density-frame';
    frame.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-density-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-density-value';
    result.textContent = value;
    metric.appendChild(frame);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityDensityPolicy() {
    const entries = [
      ['compact', 'Compact', '12 / 8 / 44'],
      ['comfortable', 'Comfortable', '16 / 12 / 44'],
      ['spacious', 'Spacious', '20 / 16 / 48']
    ];
    const mode = this._normalizeThreeMode(this._readDensityPreference() || this._densityMode, 'comfortable', 'compact', 'spacious');
    const currentIndex = entries.findIndex(([density]) => density === mode);
    if (currentIndex >= 0) this._qualityDensityPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-density-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Layout density policy');
    policy.dataset.densityPolicyActiveIndex = String(this._qualityDensityPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-density-policy-${this._qualityDensityPolicyActiveIndex}`);
    entries.forEach(([density, label, value], index) => {
      const selected = index === this._qualityDensityPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-density-policy-${index}`;
      item.className = 'wm-quality-density-policy-item' + (selected ? ' selected' : '');
      item.dataset.densityPolicy = density;
      item.dataset.densityPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-density-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-density-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityDensityPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-density-policy-item'));
  }

  _moveQualityDensityPolicySelection(delta) {
    const items = this._qualityDensityPolicyItems();
    if (!items.length) return;
    const next = (this._qualityDensityPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityDensityPolicySelection(next);
  }

  _setQualityDensityPolicySelection(index) {
    const items = this._qualityDensityPolicyItems();
    if (!items.length) return;
    this._qualityDensityPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityDensityPolicySelection();
  }

  _syncQualityDensityPolicySelection(shouldFocus = true) {
    const items = this._qualityDensityPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-density-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityDensityPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.densityPolicyActiveIndex = String(this._qualityDensityPolicyActiveIndex);
  }

  _activateQualityDensityPolicySelection() {
    const item = this._qualityDensityPolicyItems()[this._qualityDensityPolicyActiveIndex];
    if (!item) return;
    const density = item.dataset.densityPolicy || 'comfortable';
    this.setDensityPreference(density);
    this._sendWindowCmd('quality_density_policy', { density_policy: density });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _qualityComputedGeometry(selector, minWidth, minHeight) {
    const el = document.querySelector(selector);
    if (!el) return { label: 'missing', good: false };
    const rect = el.getBoundingClientRect();
    const width = Math.round(rect.width || 0);
    const height = Math.round(rect.height || 0);
    return {
      label: width + 'x' + height,
      good: width >= minWidth && height >= minHeight
    };
  }

  _makeQualityComputedShapePreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-shape-preview';
    preview.dataset.qualityComputedShape = 'round';
    [
      ['Window', this._qualityRadiusEvidence('.wm-window.focused, .wm-window', 18, false), 'window'],
      ['Taskbar', this._qualityRadiusEvidence('#wm-taskbar', 28, true), 'taskbar'],
      ['Widget', this._qualityRadiusEvidence('.wm-desktop-widget, .widget-panel', 16, false), 'widget'],
      ['Scrollbar', this._qualityComputedScrollbarEvidence('.wm-command-palette-list'), 'scrollbar']
    ].forEach(([label, evidence, kind]) => {
      const value = kind === 'scrollbar' && evidence.good ? 'thin round' : evidence.label;
      preview.appendChild(this._makeQualityComputedShapeMetric(label, value, kind, evidence.good));
    });
    preview.appendChild(this._makeQualityCornerRadiusPolicy());
    return preview;
  }

  _makeQualityComputedShapeMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-shape-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedShapeMetric = kind;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-computed-shape-sample';
    sample.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-shape-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-shape-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityRadiusEvidence(selector, minPx, pillOk) {
    const el = document.querySelector(selector);
    if (!el) return { label: 'missing', good: false };
    const style = getComputedStyle(el);
    const radius = String(style.borderRadius || '').trim();
    const first = parseFloat(radius);
    return {
      label: radius || '0px',
      good: (pillOk && radius.includes('999')) || (!Number.isNaN(first) && first >= minPx)
    };
  }

  _makeQualityCornerRadiusPolicy() {
    const entries = [
      ['round', 'Round', '24 / 20 / pill'],
      ['soft', 'Soft', '16 / 14 / 18'],
      ['square', 'Square', '8 / 8 / 10']
    ];
    const mode = this._normalizeThreeMode(this._readCornerRadiusPreference() || this._cornerRadiusMode, 'round', 'soft', 'square');
    const currentIndex = entries.findIndex(([radius]) => radius === mode);
    if (currentIndex >= 0) this._qualityCornerRadiusPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-corner-radius-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Corner radius policy');
    policy.dataset.cornerRadiusPolicyActiveIndex = String(this._qualityCornerRadiusPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-corner-radius-policy-${this._qualityCornerRadiusPolicyActiveIndex}`);
    entries.forEach(([radius, label, value], index) => {
      const selected = index === this._qualityCornerRadiusPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-corner-radius-policy-${index}`;
      item.className = 'wm-quality-corner-radius-policy-item' + (selected ? ' selected' : '');
      item.dataset.cornerRadiusPolicy = radius;
      item.dataset.cornerRadiusPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-corner-radius-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-corner-radius-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityCornerRadiusPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-corner-radius-policy-item'));
  }

  _moveQualityCornerRadiusPolicySelection(delta) {
    const items = this._qualityCornerRadiusPolicyItems();
    if (!items.length) return;
    const next = (this._qualityCornerRadiusPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityCornerRadiusPolicySelection(next);
  }

  _setQualityCornerRadiusPolicySelection(index) {
    const items = this._qualityCornerRadiusPolicyItems();
    if (!items.length) return;
    this._qualityCornerRadiusPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityCornerRadiusPolicySelection();
  }

  _syncQualityCornerRadiusPolicySelection(shouldFocus = true) {
    const items = this._qualityCornerRadiusPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-corner-radius-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityCornerRadiusPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.cornerRadiusPolicyActiveIndex = String(this._qualityCornerRadiusPolicyActiveIndex);
  }

  _activateQualityCornerRadiusPolicySelection() {
    const item = this._qualityCornerRadiusPolicyItems()[this._qualityCornerRadiusPolicyActiveIndex];
    if (!item) return;
    const radius = item.dataset.cornerRadiusPolicy || 'round';
    this.setCornerRadiusPreference(radius);
    this._sendWindowCmd('quality_corner_radius_policy', { corner_radius_policy: radius });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityTitlebarPreview() {
    const titlebar = document.querySelector('.wm-titlebar');
    const titleInput = document.querySelector('.wm-title-input, .wm-command-bar');
    const controls = titlebar ? titlebar.querySelectorAll('.wm-traffic-lights button').length : 3;
    const preview = document.createElement('div');
    preview.className = 'wm-quality-titlebar-preview';
    preview.dataset.qualityTitlebar = 'command';
    preview.appendChild(this._makeQualityTitlebarMetric('Traffic', controls + ' buttons', 'traffic'));
    preview.appendChild(this._makeQualityTitlebarMetric('Icon', 'round', 'icon'));
    preview.appendChild(this._makeQualityTitlebarMetric('Command', this._qualityElementWidth(titleInput) + 'px', 'command'));
    preview.appendChild(this._makeQualityTitlebarMetric('Context', 'visible', 'context'));
    return preview;
  }

  _makeQualityTitlebarMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-titlebar-metric';
    metric.dataset.titlebarMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-titlebar-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-titlebar-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-titlebar-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedTitlebarPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-titlebar-preview';
    preview.dataset.qualityComputedTitlebar = 'live';
    const titlebar = document.querySelector('.wm-titlebar');
    const controls = titlebar ? titlebar.querySelectorAll('.wm-traffic-lights button') : [];
    const icon = titlebar?.querySelector('.wm-titlebar-icon');
    const input = titlebar?.querySelector('.wm-title-input, .wm-command-bar');
    const context = titlebar?.querySelector('.wm-title-context');
    preview.appendChild(this._makeQualityComputedTitlebarMetric('Traffic', controls.length + ' left', 'traffic', controls.length === 3 && this._trafficSideMode === 'left'));
    preview.appendChild(this._makeQualityComputedTitlebarMetric('Icon', icon ? this._qualityElementWidth(icon) + 'px' : 'missing', 'icon', !!icon));
    preview.appendChild(this._makeQualityComputedTitlebarMetric('Input', input ? this._qualityElementWidth(input) + 'px' : 'missing', 'input', this._qualityElementWidth(input) >= 140));
    preview.appendChild(this._makeQualityComputedTitlebarMetric('Context', context ? this._qualityVisibleText(context, 'visible') : 'missing', 'context', !!context));
    return preview;
  }

  _makeQualityComputedTitlebarMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-titlebar-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedTitlebarMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-titlebar-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-titlebar-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-titlebar-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityVisibleText(el, fallback = '') {
    const text = String(el?.textContent || '').trim();
    return text || fallback;
  }

  _makeQualityComputedTrafficPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-traffic-preview';
    preview.dataset.qualityComputedTraffic = 'mac';
    const controls = Array.from(document.querySelectorAll('.wm-titlebar .wm-traffic-lights button'));
    const order = controls.map((button) => button.dataset.action || '').filter(Boolean).join('-');
    const classOrder = controls.map((button) => button.className || '').join(' ');
    const hit = this._qualityTrafficHitEvidence(controls[0]);
    const motion = this._qualityTrafficMotionEvidence(controls[0]);
    preview.appendChild(this._makeQualityComputedTrafficMetric('Side', controls.length + ' left', 'side', controls.length === 3 && this._trafficSideMode === 'left'));
    preview.appendChild(this._makeQualityComputedTrafficMetric('Order', order || 'missing', 'order', order === 'close-minimize-maximize'));
    preview.appendChild(this._makeQualityComputedTrafficMetric('Color', 'red yellow green', 'color', classOrder.includes('wm-btn-close') && classOrder.includes('wm-btn-minimize') && classOrder.includes('wm-btn-maximize')));
    preview.appendChild(this._makeQualityComputedTrafficMetric('Hit', hit.label, 'hit', hit.good));
    preview.appendChild(this._makeQualityComputedTrafficMetric('Hover', motion.label, 'motion', motion.good));
    preview.appendChild(this._makeQualityTrafficSidePolicy(this._trafficSideMode));
    return preview;
  }

  _makeQualityComputedTrafficMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-traffic-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedTrafficMetric = kind;
    const dots = document.createElement('span');
    dots.className = 'wm-quality-computed-traffic-dots';
    dots.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-traffic-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-traffic-value';
    result.textContent = value;
    metric.appendChild(dots);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityTrafficHitEvidence(button) {
    if (!button) return { label: 'missing', good: false };
    const rect = button.getBoundingClientRect();
    const style = getComputedStyle(button);
    const before = getComputedStyle(button, '::before');
    const size = Math.max(rect.width || parseFloat(style.width) || 0, rect.height || parseFloat(style.height) || 0);
    const inset = parseFloat(before.inset || before.top || '0');
    const target = Math.round(size + Math.abs(Number.isNaN(inset) ? 0 : inset) * 2);
    return { label: target + 'px', good: target >= 28 };
  }

  _qualityTrafficMotionEvidence(button) {
    if (!button) return { label: 'missing', good: false };
    const motionMode = this._normalizeMotionPreference(this._readMotionPreference());
    const style = getComputedStyle(button);
    const duration = this._qualityCssDurationListMs(style.transitionDuration || '');
    return {
      label: duration + 'ms',
      good: motionMode === 'off' ? duration === 0 : duration >= 80 && duration <= 180
    };
  }

  _makeQualityTrafficSidePolicy(activeSide) {
    const side = this._normalizeThreeMode(activeSide || this._trafficSideMode, 'left', 'right', 'left');
    const entries = [
      ['left', 'Left', 'Mac top-left'],
      ['right', 'Right', 'right title controls']
    ];
    this._qualityTrafficSidePolicyActiveIndex = Math.max(0, entries.findIndex(([mode]) => mode === side));
    const policy = document.createElement('div');
    policy.className = 'wm-quality-traffic-side-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Traffic side policy');
    policy.dataset.trafficSidePolicyActiveIndex = String(this._qualityTrafficSidePolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-traffic-side-policy-${this._qualityTrafficSidePolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityTrafficSidePolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-traffic-side-policy-${index}`;
      item.className = 'wm-quality-traffic-side-policy-item' + (selected ? ' selected' : '');
      item.dataset.trafficSidePolicy = mode;
      item.dataset.trafficSidePolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-traffic-side-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-traffic-side-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityTrafficSidePolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-traffic-side-policy-item'));
  }

  _moveQualityTrafficSidePolicySelection(delta) {
    const items = this._qualityTrafficSidePolicyItems();
    if (!items.length) return;
    this._qualityTrafficSidePolicyActiveIndex = (this._qualityTrafficSidePolicyActiveIndex + delta + items.length) % items.length;
    this._syncQualityTrafficSidePolicySelection(true);
  }

  _setQualityTrafficSidePolicySelection(index) {
    const items = this._qualityTrafficSidePolicyItems();
    if (!items.length) return;
    this._qualityTrafficSidePolicyActiveIndex = Math.max(0, Math.min(items.length - 1, index));
    this._syncQualityTrafficSidePolicySelection(true);
  }

  _syncQualityTrafficSidePolicySelection(shouldFocus = false) {
    const items = this._qualityTrafficSidePolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-traffic-side-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityTrafficSidePolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.trafficSidePolicyActiveIndex = String(this._qualityTrafficSidePolicyActiveIndex);
  }

  _activateQualityTrafficSidePolicySelection() {
    const item = this._qualityTrafficSidePolicyItems()[this._qualityTrafficSidePolicyActiveIndex];
    if (!item) return;
    const side = item.dataset.trafficSidePolicy || 'left';
    this.setTrafficSidePreference(side);
    this._sendWindowCmd('quality_traffic_side_policy', { traffic_side_policy: side });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedCommandPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-command-preview';
    preview.dataset.qualityComputedCommand = 'titlebar';
    const input = document.querySelector('.wm-window.focused .wm-title-input, .wm-title-input, .wm-command-bar');
    const value = String(input?.value || input?.placeholder || '').trim();
    const kind = this._titleCommandKind(value);
    const suggestions = this._titleCommandSuggestions(value, kind);
    const modes = this._titleCommandModes();
    const context = input?.closest('.wm-titlebar')?.querySelector('.wm-title-context');
    const contextText = this._qualityVisibleText(context, input?.placeholder || 'context');
    preview.appendChild(this._makeQualityComputedCommandMetric('Input', input ? this._qualityElementWidth(input) + 'px' : 'missing', 'input', this._qualityElementWidth(input) >= 140));
    preview.appendChild(this._makeQualityComputedCommandMetric('Kind', kind, 'kind', ['path', 'url', 'search', 'command'].includes(kind)));
    preview.appendChild(this._makeQualityComputedCommandMetric('Modes', modes.length + ' modes', 'modes', modes.length >= 4));
    preview.appendChild(this._makeQualityComputedCommandMetric('Suggest', suggestions.length + ' options', 'suggestions', suggestions.length >= 4));
    preview.appendChild(this._makeQualityComputedCommandMetric('Payload', contextText, 'payload', !!input && !!contextText));
    preview.appendChild(this._makeQualityTitleCommandPolicy(kind));
    return preview;
  }

  _makeQualityComputedCommandMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-command-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedCommandMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-command-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-command-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-command-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityTitleCommandPolicy(activeKind) {
    const modes = this._titleCommandModes();
    const currentIndex = modes.findIndex((mode) => mode.id === activeKind);
    if (currentIndex >= 0) this._qualityTitleCommandPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-title-command-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Title command mode policy');
    policy.dataset.titleCommandPolicyActiveIndex = String(this._qualityTitleCommandPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-title-command-policy-${this._qualityTitleCommandPolicyActiveIndex}`);
    modes.forEach((mode, index) => {
      const selected = index === this._qualityTitleCommandPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-title-command-policy-${index}`;
      item.className = 'wm-quality-title-command-policy-item' + (selected ? ' selected' : '');
      item.dataset.titleCommandPolicy = mode.id;
      item.dataset.titleCommandPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-title-command-policy-label';
      name.textContent = mode.label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-title-command-policy-value';
      result.textContent = mode.id === 'path' ? 'IDE path input' : mode.id === 'url' ? 'browser URL input' : mode.id === 'search' ? 'workspace search input' : 'command runner input';
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityTitleCommandPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-title-command-policy-item'));
  }

  _moveQualityTitleCommandPolicySelection(delta) {
    const items = this._qualityTitleCommandPolicyItems();
    if (!items.length) return;
    const next = (this._qualityTitleCommandPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityTitleCommandPolicySelection(next);
  }

  _setQualityTitleCommandPolicySelection(index) {
    const items = this._qualityTitleCommandPolicyItems();
    if (!items.length) return;
    this._qualityTitleCommandPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityTitleCommandPolicySelection();
  }

  _syncQualityTitleCommandPolicySelection(shouldFocus = true) {
    const items = this._qualityTitleCommandPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-title-command-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityTitleCommandPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.titleCommandPolicyActiveIndex = String(this._qualityTitleCommandPolicyActiveIndex);
  }

  _activateQualityTitleCommandPolicySelection() {
    const item = this._qualityTitleCommandPolicyItems()[this._qualityTitleCommandPolicyActiveIndex];
    if (!item) return;
    const modeId = item.dataset.titleCommandPolicy || 'path';
    const mode = this._titleCommandModes().find((entry) => entry.id === modeId);
    this._focusActiveTitleInput();
    const applied = this._applyTitleCommandMode(mode);
    this._sendWindowCmd('quality_title_command_policy', { title_command_mode: modeId, applied });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityIconPreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-icon-preview';
    preview.dataset.qualityIcon = 'round';
    preview.appendChild(this._makeQualityIconMetric('Mask', root.getPropertyValue('--ui-icon-mask-shape') || 'circle'));
    preview.appendChild(this._makeQualityIconMetric('Padding', this._qualityCssPx(root, '--ui-icon-inner-padding-px', 3) + 'px'));
    preview.appendChild(this._makeQualityIconMetric('Fit', root.getPropertyValue('--ui-icon-image-fit') || 'cover'));
    preview.appendChild(this._makeQualityIconMetric('Square', 'normalized'));
    preview.appendChild(this._makeQualityIconMaskPolicy());
    return preview;
  }

  _makeQualityIconMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-icon-metric';
    metric.dataset.iconMetric = label.toLowerCase();
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-icon-glyph wm-round-icon';
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-icon-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-icon-value';
    result.textContent = (value || '').trim();
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityIconMaskPolicy() {
    const mode = this._normalizeIconMaskPreference(document.documentElement.dataset.wmIconMask || this._iconMaskMode);
    const entries = [
      ['circle', 'Circle', 'strict round'],
      ['rounded', 'Rounded', 'soft square'],
      ['square', 'Square', 'preserve source']
    ];
    const currentIndex = entries.findIndex(([mask]) => mask === mode);
    if (currentIndex >= 0) this._qualityIconMaskPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-icon-mask-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Icon mask policy');
    policy.dataset.iconMaskPolicyActiveIndex = String(this._qualityIconMaskPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-icon-mask-policy-${this._qualityIconMaskPolicyActiveIndex}`);
    entries.forEach(([mask, label, value], index) => {
      const selected = index === this._qualityIconMaskPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-icon-mask-policy-${index}`;
      item.className = 'wm-quality-icon-mask-policy-item' + (selected ? ' selected' : '');
      item.dataset.iconMaskPolicy = mask;
      item.dataset.iconMaskPolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-icon-mask-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-icon-mask-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityIconMaskPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-icon-mask-policy-item'));
  }

  _moveQualityIconMaskPolicySelection(delta) {
    const items = this._qualityIconMaskPolicyItems();
    if (!items.length) return;
    const next = (this._qualityIconMaskPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityIconMaskPolicySelection(next);
  }

  _setQualityIconMaskPolicySelection(index) {
    const items = this._qualityIconMaskPolicyItems();
    if (!items.length) return;
    this._qualityIconMaskPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityIconMaskPolicySelection();
  }

  _syncQualityIconMaskPolicySelection(shouldFocus = true) {
    const items = this._qualityIconMaskPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-icon-mask-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityIconMaskPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.iconMaskPolicyActiveIndex = String(this._qualityIconMaskPolicyActiveIndex);
  }

  _activateQualityIconMaskPolicySelection() {
    const item = this._qualityIconMaskPolicyItems()[this._qualityIconMaskPolicyActiveIndex];
    if (!item) return;
    const mask = item.dataset.iconMaskPolicy || 'circle';
    this.setIconMaskPreference(mask);
    this._sendWindowCmd('quality_icon_mask_policy', { icon_mask_policy: mask });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedIconPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-icon-preview';
    preview.dataset.qualityComputedIcon = 'live';
    [
      ['Round', '.wm-round-icon', 'round'],
      ['Image', '.wm-icon-image', 'image'],
      ['Square', '.wm-icon-normalized-square', 'square'],
      ['Glyph', '.wm-icon-glyph', 'glyph']
    ].forEach(([label, selector, kind]) => {
      const evidence = this._qualityComputedIconEvidence(selector, kind);
      preview.appendChild(this._makeQualityComputedIconMetric(label, evidence.label, kind, evidence.good));
    });
    return preview;
  }

  _makeQualityComputedIconMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-icon-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedIconMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-icon-glyph wm-round-icon';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-icon-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-icon-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _simpleOsIconSeeds() {
    return [
      { id: 'simple.os', label: 'Simple OS', icon: 'S', brand: 'os', shape: 'round', conversion: 'brand-to-round' },
      { id: 'simple.wm', label: 'Simple WM', icon: 'W', brand: 'wm', shape: 'round', conversion: 'brand-to-round' },
      { id: 'simple.ide', label: 'Simple IDE', icon: 'I' },
      { id: 'simple.browser', label: 'Browser', icon: 'B' },
      { id: 'simple.square', label: 'Square app', icon: 'data:image/svg+xml,%3Csvg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 64 64%22%3E%3Crect width=%2264%22 height=%2264%22 fill=%22%237dd3fc%22/%3E%3Ctext x=%2232%22 y=%2239%22 text-anchor=%22middle%22 font-size=%2226%22 font-family=%22Arial%22 font-weight=%22700%22 fill=%22%230a0a0f%22%3ES%3C/text%3E%3C/svg%3E', shape: 'square-source', conversion: 'square-to-round' }
    ];
  }

  _makeSimpleBrandIcon(baseClass, item) {
    const icon = this._makeRoundIcon(baseClass, item.icon);
    icon.classList.add('wm-simple-brand-mark');
    icon.dataset.iconBrand = item.brand || 'simple';
    icon.dataset.iconShape = item.shape || 'round';
    icon.dataset.iconConversion = item.conversion || 'brand-to-round';
    const core = document.createElement('span');
    core.className = 'wm-simple-brand-mark-core';
    core.setAttribute('aria-hidden', 'true');
    const node = document.createElement('span');
    node.className = 'wm-simple-brand-mark-node';
    node.setAttribute('aria-hidden', 'true');
    icon.appendChild(core);
    icon.appendChild(node);
    return icon;
  }

  _makeQualityComputedIconKitPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-icon-kit-preview';
    preview.dataset.qualityComputedIconKit = 'simple-os';
    this._simpleOsIconSeeds().forEach((item) => {
      const tile = document.createElement('span');
      tile.className = 'wm-quality-computed-icon-kit-item';
      tile.dataset.iconKitId = item.id;
      if (item.shape) tile.dataset.iconShape = item.shape;
      if (item.conversion) tile.dataset.iconConversion = item.conversion;
      tile.appendChild(item.brand ? this._makeSimpleBrandIcon('wm-quality-computed-icon-kit-icon', item) : this._makeRoundIcon('wm-quality-computed-icon-kit-icon', item.icon));
      const label = document.createElement('span');
      label.className = 'wm-quality-computed-icon-kit-label';
      label.textContent = item.label;
      tile.appendChild(label);
      if (item.conversion) {
        const badge = document.createElement('span');
        badge.className = 'wm-quality-computed-icon-kit-badge';
        badge.textContent = item.conversion;
        tile.appendChild(badge);
      }
      preview.appendChild(tile);
    });
    return preview;
  }

  _qualityComputedIconEvidence(selector, kind) {
    const el = document.querySelector(selector);
    if (!el) return { label: 'missing', good: false };
    const style = getComputedStyle(el);
    if (kind === 'round') {
      const radius = style.borderRadius || '';
      return { label: radius || 'round', good: radius.includes('999') || radius.includes('50%') };
    }
    if (kind === 'image') {
      const fit = style.objectFit || '';
      return { label: fit || 'image', good: fit === 'cover' || fit === 'contain' };
    }
    if (kind === 'square') {
      const clip = style.clipPath || '';
      return { label: clip && clip !== 'none' ? 'clipped' : 'circle', good: clip.includes('circle') || el.classList.contains('wm-icon-normalized-square') };
    }
    const text = String(el.textContent || '').trim();
    return { label: text ? 'glyph ' + text.charAt(0).toUpperCase() : 'glyph', good: text.length > 0 };
  }

  _makeQualityComputedScrollbarPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-scrollbar-preview';
    preview.dataset.qualityComputedScrollbar = 'live';
    [
      ['App', '.wm-app-content, .wm-body, .wm-content', 'app'],
      ['Command', '.wm-command-palette-list', 'command'],
      ['Clipboard', '.wm-clipboard-list', 'clipboard'],
      ['Notify', '.wm-notification-list', 'notification']
    ].forEach(([label, selector, kind]) => {
      const evidence = this._qualityComputedScrollbarEvidence(selector);
      preview.appendChild(this._makeQualityComputedScrollbarMetric(label, evidence.label, kind, evidence.good));
    });
    return preview;
  }

  _makeQualityComputedScrollbarMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-scrollbar-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedScrollbarMetric = kind;
    const rail = document.createElement('span');
    rail.className = 'wm-quality-computed-scrollbar-rail';
    rail.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-scrollbar-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-scrollbar-value';
    result.textContent = value;
    metric.appendChild(rail);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityComputedScrollbarEvidence(selector) {
    const el = document.querySelector(selector);
    if (!el) return { label: 'missing', good: false };
    const style = getComputedStyle(el);
    const overflowY = String(style.overflowY || style.overflow || '').trim();
    const overflowX = String(style.overflowX || style.overflow || '').trim();
    const hasScrollablePolicy = ['auto', 'scroll', 'overlay'].includes(overflowY) || ['auto', 'scroll', 'overlay'].includes(overflowX);
    const firefoxWidth = String(style.scrollbarWidth || '').trim();
    const policy = firefoxWidth || overflowY || 'auto';
    return {
      label: policy,
      good: hasScrollablePolicy || firefoxWidth === 'thin'
    };
  }

  _makeQualityTypographyPreview() {
    const title = document.querySelector('.wm-title');
    const titleInput = document.querySelector('.wm-title-input, .wm-command-bar');
    const label = document.querySelector('.wm-quality-label, .wm-taskbar-label');
    const preview = document.createElement('div');
    preview.className = 'wm-quality-typography-preview';
    preview.dataset.qualityTypography = 'tokens';
    preview.appendChild(this._makeQualityTypographyMetric('Title', this._qualityElementFontSize(title, 12) + 'px'));
    preview.appendChild(this._makeQualityTypographyMetric('Input', this._qualityElementFontSize(titleInput, 11) + 'px'));
    preview.appendChild(this._makeQualityTypographyMetric('Label', this._qualityElementFontSize(label, 12) + 'px'));
    preview.appendChild(this._makeQualityTypographyMetric('Overflow', 'ellipsis'));
    return preview;
  }

  _makeQualityTypographyMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-typography-metric';
    metric.dataset.typographyMetric = label.toLowerCase();
    const sample = document.createElement('span');
    sample.className = 'wm-quality-typography-sample';
    sample.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-typography-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-typography-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityDepthPreview() {
    const windowEl = document.querySelector('.wm-window.focused, .wm-window');
    const taskbar = document.querySelector('#wm-taskbar');
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-depth-preview';
    preview.dataset.qualityDepth = 'elevation';
    preview.appendChild(this._makeQualityDepthMetric('Window', this._qualityElementZIndex(windowEl, 20)));
    preview.appendChild(this._makeQualityDepthMetric('Taskbar', this._qualityElementZIndex(taskbar, 10000)));
    preview.appendChild(this._makeQualityDepthMetric('Blur', this._qualityCssPx(root, '--ui-glass-blur-px', 24) + 'px'));
    preview.appendChild(this._makeQualityDepthMetric('Shadow', 'layered'));
    preview.appendChild(this._makeQualitySurfaceDepthPolicy(this._surfaceDepthMode));
    return preview;
  }

  _makeQualityDepthMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-depth-metric';
    metric.dataset.depthMetric = label.toLowerCase();
    const plane = document.createElement('span');
    plane.className = 'wm-quality-depth-plane';
    plane.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-depth-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-depth-value';
    result.textContent = value;
    metric.appendChild(plane);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualitySurfaceDepthPolicy(activeMode) {
    const mode = this._normalizeThreeMode(activeMode || this._surfaceDepthMode, 'layered', 'subtle', 'flat');
    const entries = [
      ['layered', 'Layered', 'deep elevation'],
      ['subtle', 'Subtle', 'lighter shadows'],
      ['flat', 'Flat', 'minimal depth']
    ];
    this._qualitySurfaceDepthPolicyActiveIndex = Math.max(0, entries.findIndex(([depth]) => depth === mode));
    const policy = document.createElement('div');
    policy.className = 'wm-quality-surface-depth-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Surface depth policy');
    policy.dataset.surfaceDepthPolicyActiveIndex = String(this._qualitySurfaceDepthPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-surface-depth-policy-${this._qualitySurfaceDepthPolicyActiveIndex}`);
    entries.forEach(([depth, label, value], index) => {
      const selected = index === this._qualitySurfaceDepthPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-surface-depth-policy-${index}`;
      item.className = 'wm-quality-surface-depth-policy-item' + (selected ? ' selected' : '');
      item.dataset.surfaceDepthPolicy = depth;
      item.dataset.surfaceDepthPolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-surface-depth-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-surface-depth-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualitySurfaceDepthPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-surface-depth-policy-item'));
  }

  _moveQualitySurfaceDepthPolicySelection(delta) {
    const items = this._qualitySurfaceDepthPolicyItems();
    if (!items.length) return;
    this._qualitySurfaceDepthPolicyActiveIndex = (this._qualitySurfaceDepthPolicyActiveIndex + delta + items.length) % items.length;
    this._syncQualitySurfaceDepthPolicySelection(true);
  }

  _setQualitySurfaceDepthPolicySelection(index) {
    const items = this._qualitySurfaceDepthPolicyItems();
    if (!items.length) return;
    this._qualitySurfaceDepthPolicyActiveIndex = Math.max(0, Math.min(items.length - 1, index));
    this._syncQualitySurfaceDepthPolicySelection(true);
  }

  _syncQualitySurfaceDepthPolicySelection(shouldFocus = false) {
    const items = this._qualitySurfaceDepthPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-surface-depth-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualitySurfaceDepthPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.surfaceDepthPolicyActiveIndex = String(this._qualitySurfaceDepthPolicyActiveIndex);
  }

  _activateQualitySurfaceDepthPolicySelection() {
    const item = this._qualitySurfaceDepthPolicyItems()[this._qualitySurfaceDepthPolicyActiveIndex];
    if (!item) return;
    const depth = item.dataset.surfaceDepthPolicy || 'layered';
    this.setSurfaceDepthPreference(depth);
    this._sendWindowCmd('quality_surface_depth_policy', { surface_depth_policy: depth });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityInteractionPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-interaction-preview';
    preview.dataset.qualityInteraction = 'affordance';
    preview.appendChild(this._makeQualityInteractionMetric('Focus', '2px ring'));
    preview.appendChild(this._makeQualityInteractionMetric('Hover', 'lift'));
    preview.appendChild(this._makeQualityInteractionMetric('Pointer', 'cursor'));
    preview.appendChild(this._makeQualityInteractionMetric('Keys', 'arrows'));
    return preview;
  }

  _makeQualityInteractionMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-interaction-metric';
    metric.dataset.interactionMetric = label.toLowerCase();
    const affordance = document.createElement('span');
    affordance.className = 'wm-quality-interaction-affordance';
    affordance.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-interaction-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-interaction-value';
    result.textContent = value;
    metric.appendChild(affordance);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedShortcutPreview() {
    const snapshot = this._qualityShortcutSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-shortcut-preview';
    preview.dataset.qualityComputedShortcut = 'live';
    preview.appendChild(this._makeQualityComputedShortcutMetric('Commands', snapshot.commands, 'commands', snapshot.commandsOk));
    preview.appendChild(this._makeQualityComputedShortcutMetric('Search', snapshot.search, 'search', snapshot.searchOk));
    preview.appendChild(this._makeQualityComputedShortcutMetric('Modes', snapshot.modes, 'modes', snapshot.modesOk));
    preview.appendChild(this._makeQualityComputedShortcutMetric('Context', snapshot.context, 'context', snapshot.contextOk));
    return preview;
  }

  _makeQualityComputedShortcutMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-shortcut-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedShortcutMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-shortcut-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.slice(0, 1);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-shortcut-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-shortcut-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityShortcutSnapshot() {
    const commands = this._commandPaletteCommands().length;
    const shortcuts = this._shortcutOverlayItems().length;
    const overlay = this._ensureShortcutOverlay();
    const search = overlay ? overlay.querySelector('.wm-shortcut-search') : null;
    const modes = this._titleCommandModes().length;
    const contextGroups = this._windowContextMenuGroups().length;
    return {
      commands: String(commands) + ' commands',
      commandsOk: commands >= 12 && shortcuts >= 8,
      search: search ? 'search ready' : 'missing',
      searchOk: !!search,
      modes: String(modes) + ' modes',
      modesOk: modes >= 4,
      context: String(contextGroups) + ' groups',
      contextOk: contextGroups >= 4
    };
  }

  _makeQualityComputedMultitaskingPreview() {
    const snapshot = this._qualityMultitaskingSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-multitasking-preview';
    preview.dataset.qualityComputedMultitasking = 'live';
    preview.appendChild(this._makeQualityComputedMultitaskingMetric('Overview', snapshot.overview, 'overview', snapshot.overviewOk));
    preview.appendChild(this._makeQualityComputedMultitaskingMetric('Switcher', snapshot.switcher, 'switcher', snapshot.switcherOk));
    preview.appendChild(this._makeQualityComputedMultitaskingMetric('Stage', snapshot.stage, 'stage', snapshot.stageOk));
    preview.appendChild(this._makeQualityComputedMultitaskingMetric('Peek', snapshot.peek, 'peek', snapshot.peekOk));
    return preview;
  }

  _makeQualityComputedMultitaskingMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-multitasking-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedMultitaskingMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-multitasking-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.slice(0, 1);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-multitasking-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-multitasking-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityMultitaskingSnapshot() {
    const windows = this._windowSwitcherWindows();
    const overview = this._ensureWindowOverview();
    this._renderWindowOverview();
    const overviewCards = overview.querySelectorAll('.wm-overview-card').length;
    const overviewSearch = !!overview.querySelector('.wm-overview-search');
    const switcher = this._ensureWindowSwitcher();
    this._renderWindowSwitcher();
    const switcherCards = switcher.querySelectorAll('.wm-window-switcher-card').length;
    const stage = this._ensureStageRail();
    this._renderStageRail();
    const stageItems = stage.querySelectorAll('.wm-stage-rail-item').length;
    const stageActions = stage.querySelectorAll('[data-stage-action]').length;
    const peekState = this.desktop ? String(this.desktop.dataset.desktopPeek || 'false') : 'missing';
    return {
      overview: String(overviewCards) + ' cards',
      overviewOk: overviewCards >= Math.min(windows.length, 1) && overviewSearch,
      switcher: String(switcherCards) + ' cards',
      switcherOk: switcherCards >= Math.min(windows.length, 1) && switcher.dataset.switcherShortcut === 'Meta Tab',
      stage: String(stageItems) + ' items',
      stageOk: stageItems >= Math.min(windows.length, 1) && stageActions >= Math.min(windows.length, 1) * 2,
      peek: peekState === 'true' ? 'peek on' : 'peek ready',
      peekOk: !!this.desktop && (peekState === 'true' || peekState === 'false')
    };
  }

  _makeQualityComputedWorkspaceControlsPreview() {
    const snapshot = this._qualityWorkspaceControlsSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-workspace-controls-preview';
    preview.dataset.qualityComputedWorkspaceControls = 'live';
    preview.appendChild(this._makeQualityComputedWorkspaceControlsMetric('Workspace', snapshot.workspace, 'workspace', snapshot.workspaceOk));
    preview.appendChild(this._makeQualityComputedWorkspaceControlsMetric('Corners', snapshot.corners, 'corners', snapshot.cornersOk));
    preview.appendChild(this._makeQualityComputedWorkspaceControlsMetric('Gestures', snapshot.gestures, 'gestures', snapshot.gesturesOk));
    preview.appendChild(this._makeQualityComputedWorkspaceControlsMetric('Focus', snapshot.focus, 'focus', snapshot.focusOk));
    return preview;
  }

  _makeQualityComputedWorkspaceControlsMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-workspace-controls-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedWorkspaceControlsMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-workspace-controls-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.slice(0, 1);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-workspace-controls-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-workspace-controls-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityWorkspaceControlsSnapshot() {
    const workspace = this._ensureWorkspaceSwitcher();
    this._renderWorkspaceSwitcher();
    const workspaceCards = workspace.querySelectorAll('.wm-workspace-card').length;
    const workspaceActions = workspace.querySelectorAll('[data-workspace-action]').length;
    const corners = this._ensureHotCorners();
    const cornerZones = corners.querySelectorAll('[data-hot-corner-action]').length;
    const gestures = this._ensureGestureHints();
    this._renderGestureHints();
    const gestureRows = gestures.querySelectorAll('[data-gesture-hint]').length;
    const gestureRuntime = this._trackpadGestureItems().length;
    const resize = this._ensureResizeHud();
    const resizeLive = resize.getAttribute('role') === 'status' && resize.getAttribute('aria-live') === 'polite';
    const focus = this._normalizeFocusMode(document.documentElement.dataset.wmFocusMode || this._focusMode);
    return {
      workspace: String(workspaceCards) + ' spaces',
      workspaceOk: workspaceCards >= 3 && workspaceActions >= 9,
      corners: String(cornerZones) + ' zones',
      cornersOk: cornerZones >= 4,
      gestures: String(gestureRuntime) + ' runtime',
      gesturesOk: gestureRows >= 4 && gestureRuntime >= 4 && resizeLive,
      focus: this._focusModeLabel(focus),
      focusOk: ['off', 'work', 'deep'].includes(focus)
    };
  }

  _makeQualityComputedWindowActionsPreview() {
    const snapshot = this._qualityWindowActionsSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-window-actions-preview';
    preview.dataset.qualityComputedWindowActions = 'live';
    preview.appendChild(this._makeQualityComputedWindowActionsMetric('Snap', snapshot.snap, 'snap', snapshot.snapOk));
    preview.appendChild(this._makeQualityComputedWindowActionsMetric('Arrange', snapshot.arrange, 'arrange', snapshot.arrangeOk));
    preview.appendChild(this._makeQualityComputedWindowActionsMetric('Taskbar', snapshot.taskbar, 'taskbar', snapshot.taskbarOk));
    preview.appendChild(this._makeQualityComputedWindowActionsMetric('Chrome', snapshot.chrome, 'chrome', snapshot.chromeOk));
    return preview;
  }

  _makeQualityComputedWindowActionsMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-window-actions-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedWindowActionsMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-window-actions-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.slice(0, 1);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-window-actions-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-window-actions-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityWindowActionsSnapshot() {
    const active = this._arrangeVisibleWindows()[0];
    const snap = this._ensureSnapLayoutPalette();
    if (active?.el) this._renderSnapLayoutPalette(active.el, active.el.querySelector('.wm-btn-maximize') || active.el);
    const snapChoices = snap.querySelectorAll('[data-snap-layout]').length;
    const snapPreviews = snap.querySelectorAll('[data-snap-preview]').length;
    const arrange = this._ensureWindowArrangePalette();
    this._renderWindowArrangePalette();
    const arrangeModes = arrange.querySelectorAll('[data-arrange-mode]').length;
    const arrangePreviews = arrange.querySelectorAll('[data-arrange-preview]').length;
    const taskbarEntry = this.windows.find((entry) => entry && (entry.window_id || entry.title));
    const taskbarPreview = this._ensureTaskbarPreview();
    if (taskbarEntry) {
      const anchor = this.taskbar?.querySelector('.wm-taskbar-item') || this.taskbar || document.body;
      this._showTaskbarPreview(taskbarEntry, anchor);
    }
    const previewActions = taskbarPreview.querySelectorAll('[data-preview-action]').length;
    const previewTitle = taskbarPreview.dataset.previewTitle || '';
    const trafficButtons = active?.el ? active.el.querySelectorAll('.wm-traffic-lights button').length : 0;
    const titleInput = active?.el ? active.el.querySelectorAll('.wm-title-input').length : 0;
    return {
      snap: String(snapChoices) + ' layouts',
      snapOk: snapChoices >= 3 && snapPreviews >= 3,
      arrange: String(arrangeModes) + ' modes',
      arrangeOk: arrangeModes >= 4 && arrangePreviews >= 4,
      taskbar: String(previewActions) + ' actions',
      taskbarOk: previewActions >= 3 && previewTitle.length > 0,
      chrome: String(trafficButtons) + ' traffic',
      chromeOk: trafficButtons >= 3 && titleInput >= 1
    };
  }

  _makeQualityStatePreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-state-preview';
    preview.dataset.qualityState = 'transitions';
    preview.appendChild(this._makeQualityStateMetric('Hover', 'lift', 'hover'));
    preview.appendChild(this._makeQualityStateMetric('Focus', 'ring', 'focus'));
    preview.appendChild(this._makeQualityStateMetric('Active', 'accent', 'active'));
    preview.appendChild(this._makeQualityStateMetric('Window', 'restore', 'window'));
    return preview;
  }

  _makeQualityStateMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-state-metric';
    metric.dataset.stateMetric = kind;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-state-sample';
    sample.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-state-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-state-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedLifecyclePreview() {
    const root = getComputedStyle(document.documentElement);
    const mode = document.documentElement.dataset.wmWindowTransition || this._windowTransitionMode || 'mac';
    const openMs = this._qualityCssPx(root, '--ui-motion-open-ms', 260);
    const closeMs = this._qualityCssPx(root, '--ui-motion-close-ms', 180);
    const minimizeMs = this._qualityCssPx(root, '--ui-motion-minimize-ms', 210);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-lifecycle-preview';
    preview.dataset.qualityComputedLifecycle = mode;
    preview.appendChild(this._makeQualityComputedLifecycleMetric('Open', openMs + 'ms', 'open', mode === 'none' ? openMs === 0 : openMs >= 90));
    preview.appendChild(this._makeQualityComputedLifecycleMetric('Close', closeMs + 'ms', 'close', mode === 'none' ? closeMs === 0 : closeMs >= 70));
    preview.appendChild(this._makeQualityComputedLifecycleMetric('Minimize', minimizeMs + 'ms', 'minimize', mode === 'none' ? minimizeMs === 0 : minimizeMs >= 80));
    preview.appendChild(this._makeQualityComputedLifecycleMetric('Mode', mode, 'mode', ['mac', 'fade', 'none'].includes(mode)));
    preview.appendChild(this._makeQualityLifecycleTimeline(openMs, closeMs, minimizeMs, mode));
    preview.appendChild(this._makeQualityWindowTransitionPolicy(mode));
    return preview;
  }

  _makeQualityComputedLifecycleMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-lifecycle-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedLifecycleMetric = kind;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-computed-lifecycle-sample';
    sample.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-lifecycle-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-lifecycle-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityLifecycleTimeline(openMs, closeMs, minimizeMs, mode) {
    const timeline = document.createElement('div');
    timeline.className = 'wm-quality-lifecycle-timeline';
    timeline.dataset.lifecycleTimeline = mode;
    [
      ['open', 'Open', openMs + 'ms', 'scale from titlebar'],
      ['minimize', 'Minimize', minimizeMs + 'ms', 'dock return'],
      ['restore', 'Restore', openMs + 'ms', 'spring back'],
      ['close', 'Close', closeMs + 'ms', 'fade shrink']
    ].forEach(([kind, label, value, detail]) => {
      timeline.appendChild(this._makeQualityLifecycleTimelineStep(kind, label, value, detail, mode));
    });
    return timeline;
  }

  _makeQualityLifecycleTimelineStep(kind, label, value, detail, mode) {
    const step = document.createElement('span');
    step.className = 'wm-quality-lifecycle-step' + (mode === 'none' ? ' disabled' : '');
    step.dataset.lifecycleStep = kind;
    const rail = document.createElement('span');
    rail.className = 'wm-quality-lifecycle-rail';
    rail.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-lifecycle-label';
    name.textContent = label;
    const timing = document.createElement('strong');
    timing.className = 'wm-quality-lifecycle-value';
    timing.textContent = mode === 'none' ? 'off' : value;
    const hint = document.createElement('span');
    hint.className = 'wm-quality-lifecycle-detail';
    hint.textContent = mode === 'none' ? 'motion disabled' : detail;
    step.appendChild(rail);
    step.appendChild(name);
    step.appendChild(timing);
    step.appendChild(hint);
    return step;
  }

  _makeQualityWindowTransitionPolicy(activeMode) {
    const entries = [
      ['mac', 'Mac', 'scale + dock return'],
      ['fade', 'Fade', 'opacity only'],
      ['none', 'None', 'no window motion']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === activeMode);
    if (currentIndex >= 0) this._qualityWindowTransitionPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-window-transition-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Window transition policy');
    policy.dataset.windowTransitionPolicyActiveIndex = String(this._qualityWindowTransitionPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-window-transition-policy-${this._qualityWindowTransitionPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityWindowTransitionPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-window-transition-policy-${index}`;
      item.className = 'wm-quality-window-transition-policy-item' + (selected ? ' selected' : '');
      item.dataset.windowTransitionPolicy = mode;
      item.dataset.windowTransitionPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-window-transition-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-window-transition-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityWindowTransitionPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-window-transition-policy-item'));
  }

  _moveQualityWindowTransitionPolicySelection(delta) {
    const items = this._qualityWindowTransitionPolicyItems();
    if (!items.length) return;
    const next = (this._qualityWindowTransitionPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityWindowTransitionPolicySelection(next);
  }

  _setQualityWindowTransitionPolicySelection(index) {
    const items = this._qualityWindowTransitionPolicyItems();
    if (!items.length) return;
    this._qualityWindowTransitionPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityWindowTransitionPolicySelection();
  }

  _syncQualityWindowTransitionPolicySelection(shouldFocus = true) {
    const items = this._qualityWindowTransitionPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-window-transition-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityWindowTransitionPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.windowTransitionPolicyActiveIndex = String(this._qualityWindowTransitionPolicyActiveIndex);
  }

  _activateQualityWindowTransitionPolicySelection() {
    const item = this._qualityWindowTransitionPolicyItems()[this._qualityWindowTransitionPolicyActiveIndex];
    if (!item) return;
    const transition = item.dataset.windowTransitionPolicy || 'mac';
    this.setWindowTransitionPreference(transition);
    this._sendWindowCmd('quality_window_transition_policy', { window_transition_policy: transition });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityVerbosityPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-verbosity-preview';
    preview.dataset.qualityVerbosity = 'calm';
    preview.appendChild(this._makeQualityVerbosityMetric('Audit', this._qualityAuditMode === 'compact' ? 'compact' : 'full', 'audit'));
    preview.appendChild(this._makeQualityVerbosityMetric('Motion', this._normalizeMotionPreference(this._readMotionPreference()), 'motion'));
    preview.appendChild(this._makeQualityVerbosityMetric('Glass', this._normalizeTransparencyPreference(this._readTransparencyPreference()), 'material'));
    preview.appendChild(this._makeQualityVerbosityMetric('Focus', this._focusModeLabel(), 'focus'));
    const mode = this._normalizeThreeMode(document.documentElement.dataset.wmChromeVerbosity || this._readChromeVerbosityPreference(), 'full', 'compact', 'minimal');
    preview.appendChild(this._makeQualityChromeVerbosityPolicy(mode));
    return preview;
  }

  _makeQualityVerbosityMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-verbosity-metric';
    metric.dataset.verbosityMetric = kind;
    const indicator = document.createElement('span');
    indicator.className = 'wm-quality-verbosity-indicator';
    indicator.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-verbosity-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-verbosity-value';
    result.textContent = String(value || '').trim();
    metric.appendChild(indicator);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityChromeVerbosityPolicy(activeMode) {
    const entries = [
      ['full', 'Full', 'all chrome visible'],
      ['compact', 'Compact', 'less visual chrome'],
      ['minimal', 'Minimal', 'quiet title chrome']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === activeMode);
    if (currentIndex >= 0) this._qualityChromeVerbosityPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-chrome-verbosity-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Chrome verbosity policy');
    policy.dataset.chromeVerbosityPolicyActiveIndex = String(this._qualityChromeVerbosityPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-chrome-verbosity-policy-${this._qualityChromeVerbosityPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityChromeVerbosityPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-chrome-verbosity-policy-${index}`;
      item.className = 'wm-quality-chrome-verbosity-policy-item' + (selected ? ' selected' : '');
      item.dataset.chromeVerbosityPolicy = mode;
      item.dataset.chromeVerbosityPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-chrome-verbosity-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-chrome-verbosity-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityChromeVerbosityPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-chrome-verbosity-policy-item'));
  }

  _moveQualityChromeVerbosityPolicySelection(delta) {
    const items = this._qualityChromeVerbosityPolicyItems();
    if (!items.length) return;
    const next = (this._qualityChromeVerbosityPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityChromeVerbosityPolicySelection(next);
  }

  _setQualityChromeVerbosityPolicySelection(index) {
    const items = this._qualityChromeVerbosityPolicyItems();
    if (!items.length) return;
    this._qualityChromeVerbosityPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityChromeVerbosityPolicySelection();
  }

  _syncQualityChromeVerbosityPolicySelection(shouldFocus = true) {
    const items = this._qualityChromeVerbosityPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-chrome-verbosity-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityChromeVerbosityPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.chromeVerbosityPolicyActiveIndex = String(this._qualityChromeVerbosityPolicyActiveIndex);
  }

  _activateQualityChromeVerbosityPolicySelection() {
    const item = this._qualityChromeVerbosityPolicyItems()[this._qualityChromeVerbosityPolicyActiveIndex];
    if (!item) return;
    const chrome = item.dataset.chromeVerbosityPolicy || 'full';
    this.setChromeVerbosityPreference(chrome);
    this._sendWindowCmd('quality_chrome_verbosity_policy', { chrome_verbosity_policy: chrome });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedPersonalizationPreview() {
    const snapshot = this._qualityPersonalizationSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-personalization-preview';
    preview.dataset.qualityComputedPersonalization = 'live';
    preview.appendChild(this._makeQualityComputedPersonalizationMetric('Motion', snapshot.motion, 'motion', snapshot.motionOk));
    preview.appendChild(this._makeQualityComputedPersonalizationMetric('Glass', snapshot.transparency, 'transparency', snapshot.transparencyOk));
    preview.appendChild(this._makeQualityComputedPersonalizationMetric('Wallpaper', snapshot.wallpaper, 'wallpaper', snapshot.wallpaperOk));
    preview.appendChild(this._makeQualityComputedPersonalizationMetric('Accent', snapshot.accent, 'accent', snapshot.accentOk));
    return preview;
  }

  _makeQualityComputedPersonalizationMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-personalization-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedPersonalizationMetric = kind;
    const indicator = document.createElement('span');
    indicator.className = 'wm-quality-computed-personalization-indicator';
    indicator.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-personalization-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-personalization-value';
    result.textContent = value;
    metric.appendChild(indicator);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityPersonalizationSnapshot() {
    const root = document.documentElement;
    const motion = this._normalizeMotionPreference(root.dataset.wmMotion || this._readMotionPreference());
    const transparency = this._normalizeTransparencyPreference(root.dataset.wmTransparency || this._readTransparencyPreference());
    const wallpaper = this._normalizeWallpaperPreference(root.dataset.wmWallpaper || this._readWallpaperPreference());
    const accent = this._normalizeAccentPreference(root.dataset.wmAccent || this._readAccentPreference()).id;
    return {
      motion: motion,
      transparency: transparency,
      wallpaper: wallpaper,
      accent: accent,
      motionOk: ['standard', 'reduced', 'off'].includes(motion),
      transparencyOk: ['standard', 'reduced', 'off'].includes(transparency),
      wallpaperOk: ['aurora', 'mesh', 'solid'].includes(wallpaper),
      accentOk: this._accentChoices().some((option) => option.id === accent)
    };
  }

  _makeQualityComputedControlCenterPreview() {
    const snapshot = this._qualityControlCenterSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-control-center-preview';
    preview.dataset.qualityComputedControlCenter = 'live';
    preview.appendChild(this._makeQualityComputedControlCenterMetric('Groups', snapshot.groups, 'groups', snapshot.groupsOk));
    preview.appendChild(this._makeQualityComputedControlCenterMetric('Policy', snapshot.policy, 'policy', snapshot.policyOk));
    preview.appendChild(this._makeQualityComputedControlCenterMetric('Active', snapshot.active, 'active', snapshot.activeOk));
    preview.appendChild(this._makeQualityComputedControlCenterMetric('Tools', snapshot.tools, 'tools', snapshot.toolsOk));
    return preview;
  }

  _makeQualityComputedControlCenterMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-control-center-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedControlCenterMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-control-center-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.slice(0, 1);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-control-center-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-control-center-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityControlCenterSnapshot() {
    const panel = this._ensureControlCenter();
    this._renderControlCenter();
    const groups = Array.from(panel.querySelectorAll('.wm-control-group'));
    const policyNames = [
      'Material transparency',
      'Motion preference',
      'Animation style',
      'Dock visibility',
      'Traffic controls',
      'Chrome verbosity',
      'Window motion',
      'Readability contrast',
      'Energy policy',
      'Animated wallpaper',
      'Backdrop motion',
      'Layout density'
    ];
    const policyGroups = policyNames.filter((label) => !!panel.querySelector('.wm-control-group[aria-label="' + label + '"]')).length;
    const buttons = panel.querySelectorAll('.wm-control-button').length;
    const activeButtons = panel.querySelectorAll('.wm-control-button.active[aria-pressed="true"]').length;
    const tools = panel.querySelector('.wm-control-group[aria-label="Workspace tools"]');
    const toolButtons = tools ? tools.querySelectorAll('.wm-control-button').length : 0;
    return {
      groups: String(groups.length) + ' groups',
      groupsOk: groups.length >= 18,
      policy: String(policyGroups) + '/' + String(policyNames.length) + ' policy',
      policyOk: policyGroups === policyNames.length && buttons >= 48,
      active: String(activeButtons) + ' active',
      activeOk: activeButtons >= 12,
      tools: String(toolButtons) + ' tools',
      toolsOk: toolButtons >= 10
    };
  }

  _makeQualityComputedOsToolsPreview() {
    const snapshot = this._qualityOsToolsSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-os-tools-preview';
    preview.dataset.qualityComputedOsTools = 'live';
    preview.appendChild(this._makeQualityComputedOsToolsMetric('Launcher', snapshot.launcher, 'launcher', snapshot.launcherOk));
    preview.appendChild(this._makeQualityComputedOsToolsMetric('Widgets', snapshot.widgets, 'widgets', snapshot.widgetsOk));
    preview.appendChild(this._makeQualityComputedOsToolsMetric('Style', snapshot.style, 'style', snapshot.styleOk));
    preview.appendChild(this._makeQualityComputedOsToolsMetric('Dock', snapshot.dock, 'dock', snapshot.dockOk));
    return preview;
  }

  _makeQualityComputedOsToolsMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-os-tools-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedOsToolsMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-os-tools-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.slice(0, 1);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-os-tools-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-os-tools-value';
    result.textContent = value;
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityOsToolsSnapshot() {
    this._ensureAppLauncher();
    this._renderAppLauncher();
    const apps = this._appLauncherGrid ? this._appLauncherGrid.querySelectorAll('.wm-app-launcher-tile').length : 0;
    const categories = this._appLauncherFilters ? this._appLauncherFilters.querySelectorAll('[data-app-category]').length : 0;
    const gallery = this._ensureWidgetGallery();
    this._renderWidgetGallery();
    const widgetCards = gallery.querySelectorAll('.wm-widget-gallery-card').length;
    const wallpaper = this._ensureWallpaperPicker();
    this._renderWallpaperPicker();
    const wallpaperChoices = wallpaper.querySelectorAll('[data-wallpaper-choice]').length;
    const accent = this._ensureAccentPalette();
    this._renderAccentPalette();
    const accentChoices = accent.querySelectorAll('[data-accent-choice]').length;
    const dock = this._ensureDockStack();
    this._renderDockStack();
    const dockItems = dock.querySelectorAll('[data-stack-item]').length;
    const dockModes = dock.querySelectorAll('[data-stack-mode]').length;
    return {
      launcher: String(apps) + ' apps',
      launcherOk: apps >= 4 && categories >= 4,
      widgets: String(widgetCards) + ' cards',
      widgetsOk: widgetCards >= 3,
      style: String(wallpaperChoices) + '/' + String(accentChoices) + ' choices',
      styleOk: wallpaperChoices >= 3 && accentChoices >= 5,
      dock: String(dockItems) + ' items',
      dockOk: dockItems >= 3 && dockModes >= 2
    };
  }

  _makeQualityPerformancePreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-performance-preview';
    preview.dataset.qualityPerformance = this._energyMode || 'standard';
    preview.appendChild(this._makeQualityPerformanceMetric('Frame', '16ms', 'frame'));
    preview.appendChild(this._makeQualityPerformanceMetric('Motion', 'transform', 'motion'));
    preview.appendChild(this._makeQualityPerformanceMetric('Opacity', 'fade', 'opacity'));
    preview.appendChild(this._makeQualityPerformanceMetric('Energy', this._energyLabel(), 'energy'));
    preview.appendChild(this._makeQualityPerformanceMetric('Backdrop', this._qualityCssPx(root, '--ui-backdrop-opacity-x100', 90) + '%', 'backdrop'));
    preview.appendChild(this._makeQualityPerformanceMetric('Fallback', this._energyMode === 'critical' ? 'off' : 'reduce', 'fallback'));
    preview.appendChild(this._makeQualityEnergyPolicy(this._energyMode));
    return preview;
  }

  _makeQualityPerformanceMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-performance-metric';
    metric.dataset.performanceMetric = kind;
    const meter = document.createElement('span');
    meter.className = 'wm-quality-performance-meter';
    meter.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-performance-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-performance-value';
    result.textContent = value;
    metric.appendChild(meter);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityEnergyPolicy(activeMode) {
    const entries = [
      ['standard', 'Standard', 'full motion budget'],
      ['low', 'Low', 'slower background'],
      ['critical', 'Critical', 'static saver']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === activeMode);
    if (currentIndex >= 0) this._qualityEnergyPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-energy-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Quality energy policy');
    policy.dataset.energyPolicyActiveIndex = String(this._qualityEnergyPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-energy-policy-${this._qualityEnergyPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityEnergyPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-energy-policy-${index}`;
      item.className = 'wm-quality-energy-policy-item' + (selected ? ' selected' : '');
      item.dataset.energyPolicy = mode;
      item.dataset.energyPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-energy-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-energy-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityEnergyPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-energy-policy-item'));
  }

  _moveQualityEnergyPolicySelection(delta) {
    const items = this._qualityEnergyPolicyItems();
    if (!items.length) return;
    const next = (this._qualityEnergyPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityEnergyPolicySelection(next);
  }

  _setQualityEnergyPolicySelection(index) {
    const items = this._qualityEnergyPolicyItems();
    if (!items.length) return;
    this._qualityEnergyPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityEnergyPolicySelection();
  }

  _syncQualityEnergyPolicySelection(shouldFocus = true) {
    const items = this._qualityEnergyPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-energy-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityEnergyPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.energyPolicyActiveIndex = String(this._qualityEnergyPolicyActiveIndex);
  }

  _activateQualityEnergyPolicySelection() {
    const item = this._qualityEnergyPolicyItems()[this._qualityEnergyPolicyActiveIndex];
    if (!item) return;
    const energy = item.dataset.energyPolicy || 'standard';
    this.setEnergyPreference(energy);
    this._sendWindowCmd('quality_energy_policy', { energy_policy: energy });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedBackdropPreview() {
    const root = getComputedStyle(document.documentElement);
    const desktop = document.querySelector('#wm-desktop');
    const pseudo = desktop ? getComputedStyle(desktop, '::before') : null;
    const motionMode = this._normalizeMotionPreference(this._readMotionPreference());
    const duration = pseudo ? this._qualityCssDurationListMs(pseudo.animationDuration) : this._qualityCssPx(root, '--ui-backdrop-duration-ms', 0);
    const animationName = pseudo ? String(pseudo.animationName || 'none').split(',')[0].trim() : 'none';
    const opacity = this._qualityCssPx(root, '--ui-backdrop-opacity-x100', 90);
    const driftScale = this._qualityCssPx(root, '--ui-backdrop-drift-scale-x100', 103);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-backdrop-preview';
    preview.dataset.qualityComputedBackdrop = motionMode;
    preview.appendChild(this._makeQualityComputedBackdropMetric('Motion', duration + 'ms ' + animationName, 'motion', motionMode === 'off' ? duration === 0 : duration >= 0));
    preview.appendChild(this._makeQualityComputedBackdropMetric('Opacity', opacity + '%', 'opacity', opacity >= 18 && opacity <= 100));
    preview.appendChild(this._makeQualityComputedBackdropMetric('Drift', (driftScale / 100).toFixed(2) + 'x', 'drift', motionMode === 'off' || driftScale >= 100));
    preview.appendChild(this._makeQualityComputedBackdropMetric('Energy', this._energyLabel(), 'energy', this._energyMode !== 'critical' || duration === 0));
    preview.appendChild(this._makeQualityBackdropPolicy());
    return preview;
  }

  _makeQualityComputedBackdropMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-backdrop-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedBackdropMetric = kind;
    const orb = document.createElement('span');
    orb.className = 'wm-quality-computed-backdrop-orb';
    orb.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-backdrop-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-backdrop-value';
    result.textContent = value;
    metric.appendChild(orb);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityBackdropPolicy() {
    const entries = [
      ['ambient', 'Ambient', '24s drift'],
      ['subtle', 'Subtle', '42s drift'],
      ['static', 'Static', 'No drift']
    ];
    const mode = this._normalizeThreeMode(this._readBackdropMotionPreference() || this._backdropMotionMode, 'ambient', 'subtle', 'static');
    const currentIndex = entries.findIndex(([motion]) => motion === mode);
    if (currentIndex >= 0) this._qualityBackdropPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-backdrop-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Backdrop motion policy');
    policy.dataset.backdropPolicyActiveIndex = String(this._qualityBackdropPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-backdrop-policy-${this._qualityBackdropPolicyActiveIndex}`);
    entries.forEach(([motion, label, value], index) => {
      const selected = index === this._qualityBackdropPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-backdrop-policy-${index}`;
      item.className = 'wm-quality-backdrop-policy-item' + (selected ? ' selected' : '');
      item.dataset.backdropPolicy = motion;
      item.dataset.backdropPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-backdrop-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-backdrop-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityBackdropPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-backdrop-policy-item'));
  }

  _moveQualityBackdropPolicySelection(delta) {
    const items = this._qualityBackdropPolicyItems();
    if (!items.length) return;
    const next = (this._qualityBackdropPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityBackdropPolicySelection(next);
  }

  _setQualityBackdropPolicySelection(index) {
    const items = this._qualityBackdropPolicyItems();
    if (!items.length) return;
    this._qualityBackdropPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityBackdropPolicySelection();
  }

  _syncQualityBackdropPolicySelection(shouldFocus = true) {
    const items = this._qualityBackdropPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-backdrop-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityBackdropPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.backdropPolicyActiveIndex = String(this._qualityBackdropPolicyActiveIndex);
  }

  _activateQualityBackdropPolicySelection() {
    const item = this._qualityBackdropPolicyItems()[this._qualityBackdropPolicyActiveIndex];
    if (!item) return;
    const motion = item.dataset.backdropPolicy || 'ambient';
    this.setBackdropMotionPreference(motion);
    this._sendWindowCmd('quality_backdrop_policy', { backdrop_policy: motion });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedWallpaperPreview() {
    const root = document.documentElement;
    const wallpaper = this._normalizeWallpaperPreference(root.dataset.wmWallpaper || this._readWallpaperPreference());
    const rawMotion = String(this._readBackdropMotionPreference() || '').trim();
    const motion = ['ambient', 'subtle', 'static'].includes(rawMotion) ? rawMotion : 'ambient';
    const choices = this._wallpaperChoices();
    const swatches = document.querySelectorAll('.wm-wallpaper-swatch');
    const duration = this._qualityCssPx(getComputedStyle(root), '--ui-backdrop-duration-ms', 24000);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-wallpaper-preview';
    preview.dataset.qualityComputedWallpaper = wallpaper;
    preview.appendChild(this._makeQualityComputedWallpaperMetric('Mode', wallpaper, 'mode', ['aurora', 'mesh', 'solid'].includes(wallpaper)));
    preview.appendChild(this._makeQualityComputedWallpaperMetric('Choices', choices.length + ' choices', 'choices', choices.length >= 3));
    preview.appendChild(this._makeQualityComputedWallpaperMetric('Swatches', swatches.length + ' live', 'swatches', swatches.length >= 3 || !this._wallpaperPicker?.hidden));
    preview.appendChild(this._makeQualityComputedWallpaperMetric('Motion', motion, 'motion', motion === 'static' || duration >= 0));
    preview.appendChild(this._makeQualityComputedWallpaperMetric('Duration', duration + 'ms', 'duration', motion === 'static' ? duration === 0 : duration >= 12000));
    preview.appendChild(this._makeQualityWallpaperPolicy());
    return preview;
  }

  _makeQualityComputedWallpaperMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-wallpaper-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedWallpaperMetric = kind;
    const orb = document.createElement('span');
    orb.className = 'wm-quality-computed-wallpaper-orb';
    orb.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-wallpaper-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-wallpaper-value';
    result.textContent = value;
    metric.appendChild(orb);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityWallpaperPolicy() {
    const entries = [
      ['aurora', 'Aurora', 'animated aurora wallpaper'],
      ['mesh', 'Mesh', 'soft gradient mesh'],
      ['solid', 'Solid', 'quiet static background']
    ];
    const wallpaper = this._normalizeWallpaperPreference(document.documentElement.dataset.wmWallpaper || this._readWallpaperPreference());
    const currentIndex = entries.findIndex(([mode]) => mode === wallpaper);
    if (currentIndex >= 0) this._qualityWallpaperPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-wallpaper-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Animated wallpaper policy');
    policy.dataset.wallpaperPolicyActiveIndex = String(this._qualityWallpaperPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-wallpaper-policy-${this._qualityWallpaperPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityWallpaperPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-wallpaper-policy-${index}`;
      item.className = 'wm-quality-wallpaper-policy-item' + (selected ? ' selected' : '');
      item.dataset.wallpaperPolicy = mode;
      item.dataset.wallpaperPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-wallpaper-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-wallpaper-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityWallpaperPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-wallpaper-policy-item'));
  }

  _moveQualityWallpaperPolicySelection(delta) {
    const items = this._qualityWallpaperPolicyItems();
    if (!items.length) return;
    const next = (this._qualityWallpaperPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityWallpaperPolicySelection(next);
  }

  _setQualityWallpaperPolicySelection(index) {
    const items = this._qualityWallpaperPolicyItems();
    if (!items.length) return;
    this._qualityWallpaperPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityWallpaperPolicySelection();
  }

  _syncQualityWallpaperPolicySelection(shouldFocus = true) {
    const items = this._qualityWallpaperPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-wallpaper-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityWallpaperPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.wallpaperPolicyActiveIndex = String(this._qualityWallpaperPolicyActiveIndex);
  }

  _activateQualityWallpaperPolicySelection() {
    const item = this._qualityWallpaperPolicyItems()[this._qualityWallpaperPolicyActiveIndex];
    if (!item) return;
    const wallpaper = item.dataset.wallpaperPolicy || 'aurora';
    this.setWallpaperPreference(wallpaper);
    this._sendWindowCmd('quality_wallpaper_policy', { wallpaper_policy: wallpaper });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedMotionPreview() {
    const motionMode = this._normalizeMotionPreference(this._readMotionPreference());
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-motion-preview';
    preview.dataset.qualityComputedMotion = motionMode;
    [
      ['Window', '.wm-window.focused, .wm-window', '', 'window'],
      ['Dock', '#wm-taskbar, .wm-taskbar-item', '', 'dock'],
      ['Command', '.wm-command-palette, .wm-title-input, .wm-command-bar', '', 'command'],
      ['Backdrop', '#wm-desktop', '::before', 'backdrop']
    ].forEach(([label, selector, pseudo, kind]) => {
      const timing = this._qualityComputedMotionTiming(selector, pseudo);
      const disabledOk = motionMode !== 'off' || timing.durationMs === 0;
      preview.appendChild(this._makeQualityComputedMotionMetric(label, timing.label, kind, disabledOk));
    });
    return preview;
  }

  _makeQualityComputedMotionMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-motion-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedMotionMetric = kind;
    const rail = document.createElement('span');
    rail.className = 'wm-quality-computed-motion-rail';
    rail.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-motion-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-motion-value';
    result.textContent = value;
    metric.appendChild(rail);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedMotionBudgetPreview() {
    const budget = this._qualityMotionBudgetSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-motion-budget-preview';
    preview.dataset.qualityComputedMotionBudget = budget.mode;
    preview.appendChild(this._makeQualityComputedMotionBudgetMetric('Active', budget.active, 'active', budget.activeOk));
    preview.appendChild(this._makeQualityComputedMotionBudgetMetric('Longest', budget.longest, 'longest', budget.longestOk));
    preview.appendChild(this._makeQualityComputedMotionBudgetMetric('Policy', budget.policy, 'policy', budget.policyOk));
    preview.appendChild(this._makeQualityComputedMotionBudgetMetric('Fallback', budget.fallback, 'fallback', budget.fallbackOk));
    return preview;
  }

  _makeQualityComputedMotionBudgetMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-motion-budget-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedMotionBudgetMetric = kind;
    const rail = document.createElement('span');
    rail.className = 'wm-quality-computed-motion-budget-rail';
    rail.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-motion-budget-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-motion-budget-value';
    result.textContent = value;
    metric.appendChild(rail);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityMotionBudgetSnapshot() {
    const mode = this._normalizeMotionPreference(this._readMotionPreference());
    const animations = typeof document.getAnimations === 'function' ? document.getAnimations({ subtree: true }) : [];
    const running = animations.filter((animation) => animation.playState !== 'idle' && animation.playState !== 'finished');
    const durations = running.map((animation) => {
      const timing = typeof animation.effect?.getTiming === 'function' ? animation.effect.getTiming() : {};
      const duration = Number(timing.duration || 0);
      return Number.isFinite(duration) ? duration : 0;
    });
    const root = getComputedStyle(document.documentElement);
    const fallbackLongest = Math.max(
      this._qualityCssPx(root, '--ui-motion-open-ms', 260),
      this._qualityCssPx(root, '--ui-motion-minimize-ms', 210),
      this._qualityCssPx(root, '--ui-motion-close-ms', 180),
      this._qualityCssPx(root, '--ui-backdrop-duration-ms', 24000)
    );
    const longest = durations.length ? Math.max(...durations) : fallbackLongest;
    const activeCount = running.length;
    const budgetLimit = mode === 'standard' ? 16 : mode === 'reduced' ? 8 : 0;
    const longestLimit = mode === 'standard' ? 30000 : mode === 'reduced' ? 1200 : 0;
    return {
      mode,
      active: activeCount + '/' + budgetLimit,
      longest: Math.round(longest) + 'ms',
      policy: mode === 'off' ? 'no motion' : mode === 'reduced' ? 'short motion' : 'standard motion',
      fallback: typeof document.getAnimations === 'function' ? 'web animations' : 'css tokens',
      activeOk: activeCount <= budgetLimit,
      longestOk: longest <= longestLimit,
      policyOk: ['standard', 'reduced', 'off'].includes(mode),
      fallbackOk: true
    };
  }

  _qualityComputedMotionTiming(selector, pseudo = '') {
    const el = document.querySelector(selector);
    if (!el) return { label: '0ms none', durationMs: 0 };
    const style = getComputedStyle(el, pseudo || null);
    const animationName = String(style.animationName || 'none').split(',')[0].trim();
    const animationMs = this._qualityCssDurationListMs(style.animationDuration);
    const transitionMs = this._qualityCssDurationListMs(style.transitionDuration);
    const durationMs = Math.max(animationMs, transitionMs);
    const name = animationName && animationName !== 'none' ? animationName : 'transition';
    return { label: durationMs + 'ms ' + name, durationMs };
  }

  _qualityCssDurationListMs(value) {
    const parts = String(value || '').split(',');
    let maxMs = 0;
    parts.forEach((part) => {
      const text = part.trim();
      if (!text) return;
      const raw = parseFloat(text);
      if (!Number.isFinite(raw)) return;
      const ms = text.endsWith('ms') ? raw : raw * 1000;
      maxMs = Math.max(maxMs, Math.round(ms));
    });
    return maxMs;
  }

  _makeQualitySpatialPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-spatial-preview';
    preview.dataset.qualitySpatial = 'origin';
    preview.appendChild(this._makeQualitySpatialMetric('Open', 'center', 'open'));
    preview.appendChild(this._makeQualitySpatialMetric('Close', 'return', 'close'));
    preview.appendChild(this._makeQualitySpatialMetric('Minimize', 'dock', 'minimize'));
    preview.appendChild(this._makeQualitySpatialMetric('Restore', 'dock', 'restore'));
    return preview;
  }

  _makeQualitySpatialMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-spatial-metric';
    metric.dataset.spatialMetric = kind;
    const path = document.createElement('span');
    path.className = 'wm-quality-spatial-path';
    path.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-spatial-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-spatial-value';
    result.textContent = value;
    metric.appendChild(path);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedSpatialPreview() {
    const snapshot = this._qualitySpatialSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-spatial-preview';
    preview.dataset.qualityComputedSpatial = snapshot.mode;
    preview.appendChild(this._makeQualityComputedSpatialMetric('Origin', snapshot.origin, 'origin', snapshot.originOk));
    preview.appendChild(this._makeQualityComputedSpatialMetric('Target', snapshot.target, 'target', snapshot.targetOk));
    preview.appendChild(this._makeQualityComputedSpatialMetric('Bounds', snapshot.bounds, 'bounds', snapshot.boundsOk));
    preview.appendChild(this._makeQualityComputedSpatialMetric('Mode', snapshot.mode, 'mode', snapshot.modeOk));
    return preview;
  }

  _makeQualityComputedSpatialMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-spatial-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedSpatialMetric = kind;
    const path = document.createElement('span');
    path.className = 'wm-quality-computed-spatial-path';
    path.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-spatial-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-spatial-value';
    result.textContent = value;
    metric.appendChild(path);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualitySpatialSnapshot() {
    const root = document.documentElement;
    const mode = this._normalizeThreeMode(this._readWindowTransitionPreference(), 'mac', 'fade', 'none');
    const active = document.querySelector('.wm-window.focused, .wm-window');
    const taskbar = this.taskbar || document.getElementById('wm-taskbar');
    const viewportWidth = Math.max(1, window.innerWidth || root.clientWidth || 1);
    const viewportHeight = Math.max(1, window.innerHeight || root.clientHeight || 1);
    const winRect = active ? active.getBoundingClientRect() : { left: viewportWidth * 0.25, top: viewportHeight * 0.18, right: viewportWidth * 0.75, bottom: viewportHeight * 0.72, width: viewportWidth * 0.5, height: viewportHeight * 0.54 };
    const dockRect = taskbar ? taskbar.getBoundingClientRect() : { top: viewportHeight - 64, left: viewportWidth * 0.25, right: viewportWidth * 0.75, width: viewportWidth * 0.5, height: 56 };
    const centerX = winRect.left + (winRect.width / 2);
    const centerY = winRect.top + (winRect.height / 2);
    const viewportCenterX = viewportWidth / 2;
    const viewportCenterY = viewportHeight / 2;
    const centerDistance = Math.hypot(centerX - viewportCenterX, centerY - viewportCenterY);
    const centerBudget = Math.max(96, Math.min(viewportWidth, viewportHeight) * 0.22);
    const dockDistance = Math.max(0, dockRect.top - winRect.bottom);
    const boundsOk = winRect.left >= -8 && winRect.top >= -8 && winRect.right <= viewportWidth + 8 && winRect.bottom <= viewportHeight + 8;
    const targetOk = dockRect.width >= 120 && dockRect.top >= viewportHeight * 0.68 && dockDistance <= viewportHeight;
    return {
      origin: centerDistance <= centerBudget ? 'centered' : 'offset',
      target: targetOk ? 'dock return' : 'missing dock',
      bounds: boundsOk ? 'in viewport' : 'overflow',
      mode,
      originOk: centerDistance <= centerBudget,
      targetOk,
      boundsOk,
      modeOk: mode === 'mac' || mode === 'fade' || mode === 'none'
    };
  }

  _makeQualityDockPreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-dock-preview';
    preview.dataset.qualityDock = 'magnification';
    preview.dataset.wmDockVisibility = this._dockVisibilityMode;
    const magnification = document.documentElement.dataset.wmDockMagnification || this._dockMagnificationMode;
    const scale = magnification === 'subtle' ? '1.08x' : magnification === 'off' ? '1.00x' : '1.18x';
    const neighbor = magnification === 'subtle' ? '1.03x' : magnification === 'off' ? '1.00x' : '1.07x';
    preview.dataset.wmDockMagnification = magnification;
    preview.appendChild(this._makeQualityDockMetric('Magnify', scale, 'magnify'));
    preview.appendChild(this._makeQualityDockMetric('Neighbor', neighbor, 'neighbor'));
    preview.appendChild(this._makeQualityDockMetric('Visibility', this._dockVisibilityLabel(this._dockVisibilityMode).toLowerCase(), 'visibility'));
    preview.appendChild(this._makeQualityDockMetric('Stack', this._dockStackMode === 'grid' ? 'grid' : 'fan', 'stack'));
    preview.appendChild(this._makeQualityDockMagnificationPolicy());
    preview.appendChild(this._makeQualityDockVisibilityPolicy());
    return preview;
  }

  _makeQualityDockMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-dock-metric';
    metric.dataset.dockMetric = kind;
    const icon = document.createElement('span');
    icon.className = 'wm-quality-dock-icon';
    icon.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-dock-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-dock-value';
    result.textContent = value;
    metric.appendChild(icon);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityDockMagnificationPolicy() {
    const current = document.documentElement.dataset.wmDockMagnification || this._readDockMagnificationPreference() || this._dockMagnificationMode;
    const entries = [
      ['standard', 'Standard', '1.18 / 1.07'],
      ['subtle', 'Subtle', '1.08 / 1.03'],
      ['off', 'Off', 'no magnify']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === current);
    if (currentIndex >= 0) this._qualityDockMagnificationPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-dock-magnification-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Dock magnification policy');
    policy.dataset.dockMagnificationPolicyActiveIndex = String(this._qualityDockMagnificationPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-dock-magnification-policy-${this._qualityDockMagnificationPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityDockMagnificationPolicyActiveIndex;
      const item = document.createElement('button');
      item.type = 'button';
      item.id = `wm-quality-dock-magnification-policy-${index}`;
      item.className = 'wm-quality-dock-magnification-policy-item' + (selected ? ' selected' : '');
      item.dataset.dockMagnificationPolicy = mode;
      item.dataset.dockMagnificationPolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-dock-magnification-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-dock-magnification-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityDockMagnificationPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-dock-magnification-policy-item'));
  }

  _moveQualityDockMagnificationPolicySelection(delta) {
    const items = this._qualityDockMagnificationPolicyItems();
    if (!items.length) return;
    const next = (this._qualityDockMagnificationPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityDockMagnificationPolicySelection(next);
  }

  _setQualityDockMagnificationPolicySelection(index) {
    const items = this._qualityDockMagnificationPolicyItems();
    if (!items.length) return;
    this._qualityDockMagnificationPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityDockMagnificationPolicySelection();
  }

  _syncQualityDockMagnificationPolicySelection(shouldFocus = true) {
    const items = this._qualityDockMagnificationPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-dock-magnification-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityDockMagnificationPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.dockMagnificationPolicyActiveIndex = String(this._qualityDockMagnificationPolicyActiveIndex);
  }

  _activateQualityDockMagnificationPolicySelection() {
    const item = this._qualityDockMagnificationPolicyItems()[this._qualityDockMagnificationPolicyActiveIndex];
    if (!item) return;
    const magnification = item.dataset.dockMagnificationPolicy || 'standard';
    this.setDockMagnificationPreference(magnification);
    this._sendWindowCmd('quality_dock_magnification_policy', { dock_magnification_policy: magnification });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityDockVisibilityPolicy() {
    const current = document.documentElement.dataset.wmDockVisibility || this._readDockVisibilityPreference() || this._dockVisibilityMode;
    const entries = [
      ['shown', 'Shown', 'always visible'],
      ['auto', 'Auto', 'hide until hover'],
      ['hidden', 'Hidden', 'quiet dock']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === current);
    if (currentIndex >= 0) this._qualityDockVisibilityPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-dock-visibility-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Dock visibility policy');
    policy.dataset.dockVisibilityPolicyActiveIndex = String(this._qualityDockVisibilityPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-dock-visibility-policy-${this._qualityDockVisibilityPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityDockVisibilityPolicyActiveIndex;
      const item = document.createElement('button');
      item.type = 'button';
      item.id = `wm-quality-dock-visibility-policy-${index}`;
      item.className = 'wm-quality-dock-visibility-policy-item' + (selected ? ' selected' : '');
      item.dataset.dockVisibilityPolicy = mode;
      item.dataset.dockVisibilityPolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-dock-visibility-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-dock-visibility-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityDockVisibilityPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-dock-visibility-policy-item'));
  }

  _moveQualityDockVisibilityPolicySelection(delta) {
    const items = this._qualityDockVisibilityPolicyItems();
    if (!items.length) return;
    const next = (this._qualityDockVisibilityPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityDockVisibilityPolicySelection(next);
  }

  _setQualityDockVisibilityPolicySelection(index) {
    const items = this._qualityDockVisibilityPolicyItems();
    if (!items.length) return;
    this._qualityDockVisibilityPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityDockVisibilityPolicySelection();
  }

  _syncQualityDockVisibilityPolicySelection(shouldFocus = true) {
    const items = this._qualityDockVisibilityPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-dock-visibility-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityDockVisibilityPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.dockVisibilityPolicyActiveIndex = String(this._qualityDockVisibilityPolicyActiveIndex);
  }

  _activateQualityDockVisibilityPolicySelection() {
    const item = this._qualityDockVisibilityPolicyItems()[this._qualityDockVisibilityPolicyActiveIndex];
    if (!item) return;
    const visibility = item.dataset.dockVisibilityPolicy || 'shown';
    this.setDockVisibilityPreference(visibility);
    this._sendWindowCmd('quality_dock_visibility_policy', { dock_visibility_policy: visibility });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedDockPreview() {
    const root = getComputedStyle(document.documentElement);
    const item = document.querySelector('.wm-taskbar-item');
    const stack = this._dockStack;
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-dock-preview';
    preview.dataset.qualityComputedDock = 'live';
    const scale = this._qualityCssPx(root, '--ui-dock-target-scale-x100', 118);
    const itemHeight = this._qualityElementMinHeight(item);
    const visibility = document.documentElement.dataset.wmDockVisibility || this._dockVisibilityMode;
    const stackLabel = (stack && !stack.hidden ? 'open ' : '') + (this._dockStackMode === 'grid' ? 'grid' : 'fan');
    preview.appendChild(this._makeQualityComputedDockMetric('Scale', (scale / 100).toFixed(2) + 'x', 'scale', scale >= 108));
    preview.appendChild(this._makeQualityComputedDockMetric('Hit', itemHeight + 'px', 'hit', itemHeight >= 34));
    preview.appendChild(this._makeQualityComputedDockMetric('Visibility', visibility, 'visibility', ['shown', 'auto', 'hidden'].includes(visibility)));
    preview.appendChild(this._makeQualityComputedDockMetric('Stack', stackLabel, 'stack', this._dockStackItems().length >= 3));
    return preview;
  }

  _makeQualityComputedDockMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-dock-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedDockMetric = kind;
    const icon = document.createElement('span');
    icon.className = 'wm-quality-computed-dock-icon';
    icon.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-dock-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-dock-value';
    result.textContent = value;
    metric.appendChild(icon);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityResponsivePreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-responsive-preview';
    preview.dataset.qualityResponsive = 'adaptive';
    preview.appendChild(this._makeQualityResponsiveMetric('Desktop', '680px'));
    preview.appendChild(this._makeQualityResponsiveMetric('Tablet', '420px'));
    preview.appendChild(this._makeQualityResponsiveMetric('Mobile', 'calc'));
    preview.appendChild(this._makeQualityResponsiveMetric('Safe', this._qualityCssPx(root, '--ui-layout-safe-area-px', 16) + 'px'));
    return preview;
  }

  _makeQualityResponsiveMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-responsive-metric';
    metric.dataset.responsiveMetric = label.toLowerCase();
    const frame = document.createElement('span');
    frame.className = 'wm-quality-responsive-frame';
    frame.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-responsive-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-responsive-value';
    result.textContent = value;
    metric.appendChild(frame);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityViewportPreview() {
    const snapshot = this._qualityViewportSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-viewport-preview';
    preview.dataset.qualityViewport = 'live';
    preview.appendChild(this._makeQualityViewportMetric('Viewport', snapshot.viewport, 'viewport', snapshot.viewportOk));
    preview.appendChild(this._makeQualityViewportMetric('Desktop', snapshot.desktop, 'desktop', snapshot.desktopOk));
    preview.appendChild(this._makeQualityViewportMetric('Window', snapshot.window, 'window', snapshot.windowOk));
    preview.appendChild(this._makeQualityViewportMetric('Overflow', snapshot.overflow, 'overflow', snapshot.overflowOk));
    return preview;
  }

  _makeQualityViewportMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-viewport-metric' + (good ? ' good' : ' warn');
    metric.dataset.viewportMetric = kind;
    const frame = document.createElement('span');
    frame.className = 'wm-quality-viewport-frame';
    frame.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-viewport-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-viewport-value';
    result.textContent = value;
    metric.appendChild(frame);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityViewportSnapshot() {
    const root = document.documentElement;
    const viewportWidth = Math.max(0, window.innerWidth || root.clientWidth || 0);
    const viewportHeight = Math.max(0, window.innerHeight || root.clientHeight || 0);
    const desktopRect = this.desktop ? this.desktop.getBoundingClientRect() : { width: viewportWidth, height: viewportHeight };
    const activeWindow = document.querySelector('.wm-window.focused, .wm-window');
    const windowRect = activeWindow ? activeWindow.getBoundingClientRect() : { width: 0, height: 0, left: 0, top: 0, right: 0, bottom: 0 };
    const overflowX = Math.max(root.scrollWidth || 0, document.body?.scrollWidth || 0) > viewportWidth + 1;
    const overflowY = Math.max(root.scrollHeight || 0, document.body?.scrollHeight || 0) > viewportHeight + 1;
    const windowOk = !activeWindow || (windowRect.left >= -8 && windowRect.top >= -8 && windowRect.right <= viewportWidth + 8 && windowRect.bottom <= viewportHeight + 8);
    return {
      viewport: Math.round(viewportWidth) + 'x' + Math.round(viewportHeight),
      desktop: Math.round(desktopRect.width || 0) + 'x' + Math.round(desktopRect.height || 0),
      window: activeWindow ? Math.round(windowRect.width || 0) + 'x' + Math.round(windowRect.height || 0) : 'none',
      overflow: overflowX || overflowY ? (overflowX ? 'x' : '') + (overflowY ? 'y' : '') : 'none',
      viewportOk: viewportWidth >= 320 && viewportHeight >= 240,
      desktopOk: Math.round(desktopRect.width || 0) <= viewportWidth + 1 && Math.round(desktopRect.height || 0) <= viewportHeight + 1,
      windowOk: windowOk,
      overflowOk: !overflowX && !overflowY
    };
  }

  _makeQualityAccessibilityPreview() {
    const taskbarItem = document.querySelector('.wm-taskbar-item');
    const preview = document.createElement('div');
    preview.className = 'wm-quality-accessibility-preview';
    preview.dataset.qualityAccessibility = 'operable';
    preview.appendChild(this._makeQualityAccessibilityMetric('Focus', 'visible'));
    preview.appendChild(this._makeQualityAccessibilityMetric('Labels', 'aria'));
    preview.appendChild(this._makeQualityAccessibilityMetric('Touch', this._qualityElementMinHeight(taskbarItem) + 'px'));
    preview.appendChild(this._makeQualityAccessibilityMetric('Reduce', 'motion'));
    return preview;
  }

  _makeQualityAccessibilityMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-accessibility-metric';
    metric.dataset.accessibilityMetric = label.toLowerCase();
    const indicator = document.createElement('span');
    indicator.className = 'wm-quality-accessibility-indicator';
    indicator.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-accessibility-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-accessibility-value';
    result.textContent = value;
    metric.appendChild(indicator);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedAccessibilityPreview() {
    const snapshot = this._qualityAccessibilitySnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-accessibility-preview';
    preview.dataset.qualityComputedAccessibility = 'live';
    preview.appendChild(this._makeQualityComputedAccessibilityMetric('Focus', snapshot.focus, 'focus', snapshot.focusOk));
    preview.appendChild(this._makeQualityComputedAccessibilityMetric('Labels', snapshot.labels, 'labels', snapshot.labelsOk));
    preview.appendChild(this._makeQualityComputedAccessibilityMetric('Touch', snapshot.touch, 'touch', snapshot.touchOk));
    preview.appendChild(this._makeQualityComputedAccessibilityMetric('Reduce', snapshot.reduce, 'reduce', snapshot.reduceOk));
    return preview;
  }

  _makeQualityComputedAccessibilityMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-accessibility-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedAccessibilityMetric = kind;
    const indicator = document.createElement('span');
    indicator.className = 'wm-quality-computed-accessibility-indicator';
    indicator.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-accessibility-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-accessibility-value';
    result.textContent = value;
    metric.appendChild(indicator);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityAccessibilitySnapshot() {
    const focusRule = Array.from(document.styleSheets || []).some((sheet) => {
      try {
        return Array.from(sheet.cssRules || []).some((rule) => String(rule.selectorText || rule.cssText || '').includes(':focus-visible'));
      } catch (_err) {
        return false;
      }
    });
    const controls = Array.from(document.querySelectorAll('button, input, [role="button"], [role="menuitem"], [role="option"]'));
    const labeled = controls.filter((el) => {
      const label = String(el.getAttribute('aria-label') || el.getAttribute('title') || el.textContent || '').trim();
      return label.length > 0 || el.getAttribute('aria-labelledby');
    }).length;
    const taskbarItem = document.querySelector('.wm-taskbar-item, .wm-control-button, button');
    const touchHeight = this._qualityElementMinHeight(taskbarItem);
    const reduceCapable = window.matchMedia ? window.matchMedia('(prefers-reduced-motion: reduce)').media.includes('prefers-reduced-motion') : true;
    return {
      focus: focusRule ? 'focus rule' : 'missing',
      labels: labeled + '/' + controls.length,
      touch: touchHeight + 'px',
      reduce: reduceCapable ? 'media' : 'missing',
      focusOk: focusRule,
      labelsOk: controls.length === 0 || labeled >= Math.max(1, Math.floor(controls.length * 0.9)),
      touchOk: touchHeight >= 44,
      reduceOk: reduceCapable
    };
  }

  _makeQualityComputedStatusPreview() {
    const snapshot = this._qualityStatusSnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-status-preview';
    preview.dataset.qualityComputedStatus = 'live';
    preview.appendChild(this._makeQualityComputedStatusMetric('HUD', snapshot.hud, 'hud', snapshot.hudOk));
    preview.appendChild(this._makeQualityComputedStatusMetric('Privacy', snapshot.privacy, 'privacy', snapshot.privacyOk));
    preview.appendChild(this._makeQualityComputedStatusMetric('Notify', snapshot.notify, 'notify', snapshot.notifyOk));
    preview.appendChild(this._makeQualityComputedStatusMetric('Activity', snapshot.activity, 'activity', snapshot.activityOk));
    preview.appendChild(this._makeQualityFeedbackPolicy(this._feedbackMode));
    return preview;
  }

  _makeQualityComputedStatusMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-status-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedStatusMetric = kind;
    const indicator = document.createElement('span');
    indicator.className = 'wm-quality-computed-status-indicator';
    indicator.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-status-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-status-value';
    result.textContent = value;
    metric.appendChild(indicator);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityFeedbackPolicy(activeMode) {
    const entries = [
      ['standard', 'Standard', 'all confirmations'],
      ['subtle', 'Subtle', 'quiet routine feedback'],
      ['off', 'Off', 'critical only']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === activeMode);
    if (currentIndex >= 0) this._qualityFeedbackPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-feedback-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Quality feedback policy');
    policy.dataset.feedbackPolicyActiveIndex = String(this._qualityFeedbackPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-feedback-policy-${this._qualityFeedbackPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityFeedbackPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-feedback-policy-${index}`;
      item.className = 'wm-quality-feedback-policy-item' + (selected ? ' selected' : '');
      item.dataset.feedbackPolicy = mode;
      item.dataset.feedbackPolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-feedback-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-feedback-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityFeedbackPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-feedback-policy-item'));
  }

  _moveQualityFeedbackPolicySelection(delta) {
    const items = this._qualityFeedbackPolicyItems();
    if (!items.length) return;
    const next = (this._qualityFeedbackPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityFeedbackPolicySelection(next);
  }

  _setQualityFeedbackPolicySelection(index) {
    const items = this._qualityFeedbackPolicyItems();
    if (!items.length) return;
    this._qualityFeedbackPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityFeedbackPolicySelection();
  }

  _syncQualityFeedbackPolicySelection(shouldFocus = true) {
    const items = this._qualityFeedbackPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-feedback-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityFeedbackPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.feedbackPolicyActiveIndex = String(this._qualityFeedbackPolicyActiveIndex);
  }

  _activateQualityFeedbackPolicySelection() {
    const item = this._qualityFeedbackPolicyItems()[this._qualityFeedbackPolicyActiveIndex];
    if (!item) return;
    const feedback = item.dataset.feedbackPolicy || 'standard';
    this.setFeedbackPreference(feedback);
    this._sendWindowCmd('quality_feedback_policy', { feedback_policy: feedback });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _qualityStatusSnapshot() {
    const hud = document.querySelector('.wm-system-hud');
    const privacy = document.querySelector('.wm-privacy-indicator');
    const notificationCenter = document.querySelector('.wm-notification-center');
    const activity = document.querySelector('.wm-live-activity');
    const privacyRows = privacy ? privacy.querySelectorAll('[data-privacy-service]').length : 0;
    const unread = notificationCenter ? notificationCenter.querySelectorAll('.wm-notification-card.unread').length : 0;
    const progressEl = activity ? activity.querySelector('[data-live-progress]') : null;
    const progressRaw = progressEl ? parseInt(progressEl.getAttribute('data-live-progress') || '0', 10) : 0;
    const progress = Number.isFinite(progressRaw) ? Math.max(0, Math.min(100, progressRaw)) : 0;
    const hudLive = hud ? String(hud.getAttribute('aria-live') || '').trim() : '';
    const activityLive = activity ? String(activity.getAttribute('aria-live') || '').trim() : '';
    return {
      hud: hudLive || 'none',
      privacy: privacyRows + ' services',
      notify: unread + ' unread',
      activity: progress + '%',
      hudOk: !!hud && hud.getAttribute('role') === 'status' && hudLive === 'polite',
      privacyOk: !!privacy && privacyRows >= 3,
      notifyOk: !!notificationCenter && unread >= 1,
      activityOk: !!activity && activity.getAttribute('role') === 'status' && activityLive === 'polite' && progress >= 0 && progress <= 100
    };
  }

  _makeQualityComputedProductivityPreview() {
    const snapshot = this._qualityProductivitySnapshot();
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-productivity-preview';
    preview.dataset.qualityComputedProductivity = 'live';
    preview.appendChild(this._makeQualityComputedProductivityMetric('Clipboard', snapshot.clipboard, 'clipboard', snapshot.clipboardOk));
    preview.appendChild(this._makeQualityComputedProductivityMetric('Quick', snapshot.quick, 'quick', snapshot.quickOk));
    preview.appendChild(this._makeQualityComputedProductivityMetric('Notify', snapshot.notify, 'notify', snapshot.notifyOk));
    preview.appendChild(this._makeQualityComputedProductivityMetric('Capture', snapshot.capture, 'capture', snapshot.captureOk));
    return preview;
  }

  _makeQualityComputedProductivityMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-productivity-metric ' + (good ? 'good' : 'warn');
    metric.dataset.computedProductivityMetric = kind;
    const indicator = document.createElement('span');
    indicator.className = 'wm-quality-computed-productivity-indicator';
    indicator.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-productivity-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-productivity-value';
    result.textContent = value;
    metric.appendChild(indicator);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityProductivitySnapshot() {
    const clipboard = this._ensureClipboardHistory();
    this._renderClipboardHistory();
    const clips = clipboard.querySelectorAll('.wm-clipboard-item').length;
    const clipFilters = clipboard.querySelectorAll('[data-clipboard-filter]').length;
    const quick = this._ensureQuickSettings();
    this._renderQuickSettings();
    const quickItems = quick.querySelectorAll('.wm-quick-setting').length;
    const quickSliders = quick.querySelectorAll('.wm-quick-slider').length;
    const notify = this._ensureNotificationCenter();
    this._renderNotificationCenter();
    const notifications = notify.querySelectorAll('.wm-notification-card').length;
    const notifyActions = notify.querySelectorAll('[data-notification-action]').length;
    const capture = this._ensureScreenCapture();
    this._renderScreenCapture();
    const captureModes = capture.querySelectorAll('[data-capture-mode]').length;
    const captureActions = capture.querySelectorAll('[data-capture-action]').length;
    return {
      clipboard: String(clips) + ' clips',
      clipboardOk: clips >= 3 && clipFilters >= 4,
      quick: String(quickItems) + '/' + String(quickSliders) + ' controls',
      quickOk: quickItems >= 5 && quickSliders >= 2,
      notify: String(notifications) + ' cards',
      notifyOk: notifications >= 3 && notifyActions >= 4,
      capture: String(captureModes) + ' modes',
      captureOk: captureModes >= 3 && captureActions >= 2
    };
  }

  _makeQualityMotionPreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-motion-preview';
    preview.dataset.qualityMotion = this._normalizeMotionPreference(this._readMotionPreference());
    preview.appendChild(this._makeQualityMotionStep('Open', root.getPropertyValue('--ui-motion-open-ms') || '260'));
    preview.appendChild(this._makeQualityMotionStep('Close', root.getPropertyValue('--ui-motion-close-ms') || '180'));
    preview.appendChild(this._makeQualityMotionStep('Minimize', root.getPropertyValue('--ui-motion-minimize-ms') || '210'));
    preview.appendChild(this._makeQualityMotionStep('Easing', root.getPropertyValue('--ui-motion-spring') || 'spring'));
    preview.appendChild(this._makeQualityMotionPolicy());
    return preview;
  }

  _makeQualityMotionStep(label, value) {
    const step = document.createElement('span');
    step.className = 'wm-quality-motion-step';
    step.dataset.motionStep = label.toLowerCase();
    const name = document.createElement('span');
    name.className = 'wm-quality-motion-label';
    name.textContent = label;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-motion-sample';
    sample.setAttribute('aria-hidden', 'true');
    const duration = document.createElement('strong');
    duration.className = 'wm-quality-motion-value';
    duration.textContent = value.trim();
    step.appendChild(name);
    step.appendChild(sample);
    step.appendChild(duration);
    return step;
  }

  _makeQualityMotionPolicy() {
    const policy = document.createElement('div');
    policy.className = 'wm-quality-motion-policy';
    [
      ['standard', 'Standard', 'Full animation'],
      ['reduced', 'Reduced', 'Short, no blur'],
      ['off', 'Off', 'No animation']
    ].forEach(([mode, label, value]) => {
      const item = document.createElement('span');
      item.className = 'wm-quality-motion-policy-item';
      item.dataset.motionPolicy = mode;
      const name = document.createElement('span');
      name.className = 'wm-quality-motion-policy-label';
      name.textContent = label;
      const rule = document.createElement('strong');
      rule.className = 'wm-quality-motion-policy-value';
      rule.textContent = value;
      item.appendChild(name);
      item.appendChild(rule);
      policy.appendChild(item);
    });
    return policy;
  }

  _makeQualityAnimationPreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-animation-preview';
    preview.dataset.qualityAnimation = 'timeline';
    preview.appendChild(this._makeQualityAnimationTrack('Window', root.getPropertyValue('--ui-motion-open-ms') || '260', 'open'));
    preview.appendChild(this._makeQualityAnimationTrack('Dock', '160', 'dock'));
    preview.appendChild(this._makeQualityAnimationTrack('Command', '180', 'command'));
    preview.appendChild(this._makeQualityAnimationTrack('Backdrop', 'ambient', 'background'));
    preview.appendChild(this._makeQualityAnimationStylePolicy());
    return preview;
  }

  _makeQualityAnimationTrack(label, value, kind) {
    const track = document.createElement('span');
    track.className = 'wm-quality-animation-track';
    track.dataset.animationTrack = kind;
    const rail = document.createElement('span');
    rail.className = 'wm-quality-animation-rail';
    rail.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-animation-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-animation-value';
    result.textContent = value.trim();
    track.appendChild(rail);
    track.appendChild(name);
    track.appendChild(result);
    return track;
  }

  _makeQualityAnimationStylePolicy() {
    const entries = [
      ['spring', 'Spring', 'expressive bounce'],
      ['calm', 'Calm', 'slower easing'],
      ['snappy', 'Snappy', 'fast response']
    ];
    const style = this._normalizeAnimationStyle(document.documentElement.dataset.wmAnimationStyle || this._readAnimationStyle());
    const currentIndex = entries.findIndex(([mode]) => mode === style);
    if (currentIndex >= 0) this._qualityAnimationStylePolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-animation-style-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Animation style policy');
    policy.dataset.animationStylePolicyActiveIndex = String(this._qualityAnimationStylePolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-animation-style-policy-${this._qualityAnimationStylePolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityAnimationStylePolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-animation-style-policy-${index}`;
      item.className = 'wm-quality-animation-style-policy-item' + (selected ? ' selected' : '');
      item.dataset.animationStylePolicy = mode;
      item.dataset.animationStylePolicyIndex = String(index);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      const name = document.createElement('span');
      name.className = 'wm-quality-animation-style-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-animation-style-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityAnimationStylePolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-animation-style-policy-item'));
  }

  _moveQualityAnimationStylePolicySelection(delta) {
    const items = this._qualityAnimationStylePolicyItems();
    if (!items.length) return;
    const next = (this._qualityAnimationStylePolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityAnimationStylePolicySelection(next);
  }

  _setQualityAnimationStylePolicySelection(index) {
    const items = this._qualityAnimationStylePolicyItems();
    if (!items.length) return;
    this._qualityAnimationStylePolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityAnimationStylePolicySelection();
  }

  _syncQualityAnimationStylePolicySelection(shouldFocus = true) {
    const items = this._qualityAnimationStylePolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-animation-style-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityAnimationStylePolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.animationStylePolicyActiveIndex = String(this._qualityAnimationStylePolicyActiveIndex);
  }

  _activateQualityAnimationStylePolicySelection() {
    const item = this._qualityAnimationStylePolicyItems()[this._qualityAnimationStylePolicyActiveIndex];
    if (!item) return;
    const style = item.dataset.animationStylePolicy || 'spring';
    this.setAnimationStyle(style);
    this._sendWindowCmd('quality_animation_style_policy', { animation_style_policy: style });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityWidgetPreview() {
    const widgets = document.querySelectorAll('.wm-desktop-widget');
    const gallery = document.querySelector('.wm-widget-gallery');
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-widget-preview';
    preview.dataset.qualityWidget = 'desktop';
    preview.appendChild(this._makeQualityWidgetMetric('Stack', widgets.length + ' widgets', 'stack'));
    preview.appendChild(this._makeQualityWidgetMetric('Controls', 'pin/remove', 'controls'));
    preview.appendChild(this._makeQualityWidgetMetric('Shape', 'round glass', 'shape'));
    preview.appendChild(this._makeQualityWidgetMetric('Gallery', this._qualityElementWidth(gallery) || '440', 'gallery'));
    preview.dataset.widgetMaxWidth = this._qualityCssPx(root, '--ui-layout-safe-area-px', 16) + 'px safe';
    return preview;
  }

  _makeQualityWidgetMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-widget-metric';
    metric.dataset.widgetMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-widget-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-widget-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-widget-value';
    result.textContent = String(value).trim();
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedWidgetPreview() {
    const widgets = document.querySelectorAll('.wm-desktop-widget');
    const firstWidget = widgets[0];
    const gallery = document.querySelector('.wm-widget-gallery');
    const controls = firstWidget ? firstWidget.querySelectorAll('.wm-widget-control') : [];
    const radius = firstWidget ? getComputedStyle(firstWidget).borderRadius : '';
    const galleryWidth = this._qualityElementWidth(gallery);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-widget-preview';
    preview.dataset.qualityComputedWidget = 'live';
    preview.appendChild(this._makeQualityComputedWidgetMetric('Count', widgets.length + ' live', 'count', widgets.length >= 3));
    preview.appendChild(this._makeQualityComputedWidgetMetric('Shape', radius || 'missing', 'shape', radius.includes('20') || radius.includes('999')));
    preview.appendChild(this._makeQualityComputedWidgetMetric('Controls', controls.length + ' actions', 'controls', controls.length >= 2));
    preview.appendChild(this._makeQualityComputedWidgetMetric('Gallery', (galleryWidth || 440) + 'px', 'gallery', (galleryWidth || 440) <= 440));
    preview.appendChild(this._makeQualityWidgetStackPolicy());
    return preview;
  }

  _makeQualityComputedWidgetMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-widget-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedWidgetMetric = kind;
    const glyph = document.createElement('span');
    glyph.className = 'wm-quality-computed-widget-glyph';
    glyph.setAttribute('aria-hidden', 'true');
    glyph.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-widget-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-widget-value';
    result.textContent = String(value).trim();
    metric.appendChild(glyph);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityWidgetStackPolicy() {
    const shelf = this._ensureDesktopWidgets();
    const gallery = this._widgetGallery;
    const activeMode = gallery && !gallery.hidden ? 'gallery' : shelf && shelf.classList.contains('collapsed') ? 'hidden' : 'visible';
    const entries = [
      ['visible', 'Visible', 'show widgets'],
      ['gallery', 'Gallery', 'add widgets'],
      ['hidden', 'Hidden', 'quiet desktop']
    ];
    const currentIndex = entries.findIndex(([mode]) => mode === activeMode);
    if (currentIndex >= 0) this._qualityWidgetStackPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-widget-stack-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Widget stack policy');
    policy.dataset.widgetStackPolicyActiveIndex = String(this._qualityWidgetStackPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-widget-stack-policy-${this._qualityWidgetStackPolicyActiveIndex}`);
    entries.forEach(([mode, label, value], index) => {
      const selected = index === this._qualityWidgetStackPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-widget-stack-policy-${index}`;
      item.className = 'wm-quality-widget-stack-policy-item' + (selected ? ' selected' : '');
      item.dataset.widgetStackPolicy = mode;
      item.dataset.widgetStackPolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-widget-stack-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-widget-stack-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityWidgetStackPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-widget-stack-policy-item'));
  }

  _moveQualityWidgetStackPolicySelection(delta) {
    const items = this._qualityWidgetStackPolicyItems();
    if (!items.length) return;
    const next = (this._qualityWidgetStackPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityWidgetStackPolicySelection(next);
  }

  _setQualityWidgetStackPolicySelection(index) {
    const items = this._qualityWidgetStackPolicyItems();
    if (!items.length) return;
    this._qualityWidgetStackPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityWidgetStackPolicySelection();
  }

  _syncQualityWidgetStackPolicySelection(shouldFocus = true) {
    const items = this._qualityWidgetStackPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-widget-stack-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityWidgetStackPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.widgetStackPolicyActiveIndex = String(this._qualityWidgetStackPolicyActiveIndex);
  }

  _activateQualityWidgetStackPolicySelection() {
    const item = this._qualityWidgetStackPolicyItems()[this._qualityWidgetStackPolicyActiveIndex];
    if (!item) return;
    const mode = item.dataset.widgetStackPolicy || 'visible';
    const shelf = this._ensureDesktopWidgets();
    if (mode === 'hidden') {
      if (shelf) shelf.classList.add('collapsed');
      this._toggleWidgetGallery(false);
    } else if (mode === 'gallery') {
      if (shelf) shelf.classList.remove('collapsed');
      this._toggleWidgetGallery(true);
    } else {
      if (shelf) shelf.classList.remove('collapsed');
      this._toggleWidgetGallery(false);
    }
    this._sendWindowCmd('quality_widget_stack_policy', { widget_stack_policy: mode });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityMaterialPreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-material-preview';
    preview.dataset.qualityMaterial = this._normalizeTransparencyPreference(this._readTransparencyPreference());
    preview.appendChild(this._makeQualityMaterialMetric('Blur', this._qualityCssPx(root, '--ui-glass-blur-px', 24) + 'px'));
    preview.appendChild(this._makeQualityMaterialMetric('Floor', this._qualityCssPx(root, '--ui-glass-opacity-floor-x100', 6) + '%'));
    preview.appendChild(this._makeQualityMaterialMetric('Solid', this._qualityCssPx(root, '--ui-solid-surface-opacity-x100', 96) + '%'));
    preview.appendChild(this._makeQualityMaterialMetric('Mode', this._normalizeTransparencyPreference(this._readTransparencyPreference())));
    preview.appendChild(this._makeQualityMaterialPolicy());
    return preview;
  }

  _makeQualityMaterialMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-material-metric';
    metric.dataset.materialMetric = label.toLowerCase();
    const name = document.createElement('span');
    name.className = 'wm-quality-material-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-material-value';
    result.textContent = value;
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityMaterialPolicy() {
    const mode = this._normalizeTransparencyPreference(document.documentElement.dataset.wmTransparency || this._readTransparencyPreference());
    const entries = [
      ['standard', 'Standard', 'glass vibrancy'],
      ['reduced', 'Reduced', 'lighter blur'],
      ['off', 'Solid', 'no glass']
    ];
    const currentIndex = entries.findIndex(([material]) => material === mode);
    if (currentIndex >= 0) this._qualityMaterialPolicyActiveIndex = currentIndex;
    const policy = document.createElement('div');
    policy.className = 'wm-quality-material-policy';
    policy.setAttribute('role', 'listbox');
    policy.setAttribute('aria-label', 'Material transparency policy');
    policy.dataset.materialPolicyActiveIndex = String(this._qualityMaterialPolicyActiveIndex);
    policy.setAttribute('aria-activedescendant', `wm-quality-material-policy-${this._qualityMaterialPolicyActiveIndex}`);
    entries.forEach(([material, label, value], index) => {
      const selected = index === this._qualityMaterialPolicyActiveIndex;
      const item = document.createElement('button');
      item.id = `wm-quality-material-policy-${index}`;
      item.className = 'wm-quality-material-policy-item' + (selected ? ' selected' : '');
      item.dataset.materialPolicy = material;
      item.dataset.materialPolicyIndex = String(index);
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      item.tabIndex = selected ? 0 : -1;
      const name = document.createElement('span');
      name.className = 'wm-quality-material-policy-label';
      name.textContent = label;
      const result = document.createElement('strong');
      result.className = 'wm-quality-material-policy-value';
      result.textContent = value;
      item.appendChild(name);
      item.appendChild(result);
      policy.appendChild(item);
    });
    return policy;
  }

  _qualityMaterialPolicyItems() {
    if (!this._qualityInspector) return [];
    return Array.from(this._qualityInspector.querySelectorAll('.wm-quality-material-policy-item'));
  }

  _moveQualityMaterialPolicySelection(delta) {
    const items = this._qualityMaterialPolicyItems();
    if (!items.length) return;
    const next = (this._qualityMaterialPolicyActiveIndex + delta + items.length) % items.length;
    this._setQualityMaterialPolicySelection(next);
  }

  _setQualityMaterialPolicySelection(index) {
    const items = this._qualityMaterialPolicyItems();
    if (!items.length) return;
    this._qualityMaterialPolicyActiveIndex = Math.max(0, Math.min(index, items.length - 1));
    this._syncQualityMaterialPolicySelection();
  }

  _syncQualityMaterialPolicySelection(shouldFocus = true) {
    const items = this._qualityMaterialPolicyItems();
    if (!items.length) return;
    const policy = items[0].closest('.wm-quality-material-policy');
    items.forEach((item, index) => {
      const selected = index === this._qualityMaterialPolicyActiveIndex;
      item.classList.toggle('selected', selected);
      item.tabIndex = selected ? 0 : -1;
      item.setAttribute('aria-selected', selected ? 'true' : 'false');
      if (selected && policy) policy.setAttribute('aria-activedescendant', item.id);
      if (selected && shouldFocus) item.focus();
    });
    if (policy) policy.dataset.materialPolicyActiveIndex = String(this._qualityMaterialPolicyActiveIndex);
  }

  _activateQualityMaterialPolicySelection() {
    const item = this._qualityMaterialPolicyItems()[this._qualityMaterialPolicyActiveIndex];
    if (!item) return;
    const material = item.dataset.materialPolicy || 'standard';
    this.setTransparencyPreference(material);
    this._sendWindowCmd('quality_material_policy', { material_policy: material });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityComputedMaterialPreview() {
    const mode = this._normalizeTransparencyPreference(this._readTransparencyPreference());
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-material-preview';
    preview.dataset.qualityComputedMaterial = mode;
    [
      ['Window', '.wm-window.focused, .wm-window', 'window'],
      ['Command', '.wm-command-palette, .wm-title-input, .wm-command-bar', 'command'],
      ['Taskbar', '#wm-taskbar', 'taskbar'],
      ['Widget', '.wm-desktop-widget, .widget-panel', 'widget']
    ].forEach(([label, selector, kind]) => {
      const evidence = this._qualityComputedMaterialEvidence(selector, mode);
      preview.appendChild(this._makeQualityComputedMaterialMetric(label, evidence.label, kind, evidence.good));
    });
    return preview;
  }

  _makeQualityComputedMaterialMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-material-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedMaterialMetric = kind;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-computed-material-sample';
    sample.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-material-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-material-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityComputedMaterialEvidence(selector, mode) {
    const el = document.querySelector(selector);
    if (!el) return { label: 'missing', good: false };
    const style = getComputedStyle(el);
    const backdrop = String(style.backdropFilter || style.webkitBackdropFilter || '').trim();
    const alpha = this._qualityCssAlpha(style.backgroundColor);
    if (mode === 'off') {
      return { label: 'solid ' + Math.round(alpha * 100) + '%', good: (!backdrop || backdrop === 'none') && alpha >= 0.9 };
    }
    const hasBlur = backdrop.includes('blur');
    const label = hasBlur ? backdrop.split(')')[0] + ')' : 'no blur';
    return { label, good: hasBlur || mode === 'reduced' };
  }

  _qualityCssAlpha(value) {
    const text = String(value || '').trim();
    const rgba = text.match(/rgba?\(([^)]+)\)/i);
    if (!rgba) return 1;
    const parts = rgba[1].split(',').map((part) => part.trim());
    if (parts.length < 4) return 1;
    const alpha = parseFloat(parts[3]);
    return Number.isFinite(alpha) ? Math.max(0, Math.min(1, alpha)) : 1;
  }

  _makeQualitySurfacePreview() {
    const root = getComputedStyle(document.documentElement);
    const preview = document.createElement('div');
    preview.className = 'wm-quality-surface-preview';
    preview.dataset.qualitySurface = 'transparency';
    preview.appendChild(this._makeQualitySurfaceMetric('Window', this._qualityCssPx(root, '--ui-glass-blur-px', 24) + 'px', 'window'));
    preview.appendChild(this._makeQualitySurfaceMetric('Command', 'glass', 'command'));
    preview.appendChild(this._makeQualitySurfaceMetric('Taskbar', 'glass', 'taskbar'));
    preview.appendChild(this._makeQualitySurfaceMetric('Widget', 'glass', 'widget'));
    return preview;
  }

  _makeQualitySurfaceMetric(label, value, kind) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-surface-metric';
    metric.dataset.surfaceMetric = kind;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-surface-sample';
    sample.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-surface-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-surface-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualityComputedSurfacePreview() {
    const mode = this._normalizeTransparencyPreference(this._readTransparencyPreference());
    const preview = document.createElement('div');
    preview.className = 'wm-quality-computed-surface-preview';
    preview.dataset.qualityComputedSurface = mode;
    [
      ['Window', '.wm-window.focused, .wm-window', 'window'],
      ['Command', '.wm-command-palette, .wm-title-input, .wm-command-bar', 'command'],
      ['Taskbar', '#wm-taskbar', 'taskbar'],
      ['Widget', '.wm-desktop-widget, .widget-panel', 'widget']
    ].forEach(([label, selector, kind]) => {
      const evidence = this._qualityComputedSurfaceEvidence(selector, mode);
      preview.appendChild(this._makeQualityComputedSurfaceMetric(label, evidence.label, kind, evidence.good));
    });
    return preview;
  }

  _makeQualityComputedSurfaceMetric(label, value, kind, good) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-computed-surface-metric' + (good ? ' good' : ' warn');
    metric.dataset.computedSurfaceMetric = kind;
    const sample = document.createElement('span');
    sample.className = 'wm-quality-computed-surface-sample';
    sample.setAttribute('aria-hidden', 'true');
    const name = document.createElement('span');
    name.className = 'wm-quality-computed-surface-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-computed-surface-value';
    result.textContent = value;
    metric.appendChild(sample);
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _qualityComputedSurfaceEvidence(selector, mode) {
    const el = document.querySelector(selector);
    if (!el) return { label: 'missing', good: false };
    const style = getComputedStyle(el);
    const alpha = this._qualityCssAlpha(style.backgroundColor);
    const percent = Math.round(alpha * 100);
    if (mode === 'off') return { label: 'solid ' + percent + '%', good: alpha >= 0.9 };
    return { label: percent + '% alpha', good: alpha < 0.98 };
  }

  _makeQualityCheckDetail(items) {
    const selected = items.find((item) => item.key === this._selectedQualityCheck) || items[0];
    const panel = document.createElement('div');
    panel.className = 'wm-quality-check-detail';
    panel.dataset.qualityDetail = selected.key;
    const head = document.createElement('div');
    head.className = 'wm-quality-check-head';
    const title = document.createElement('strong');
    title.className = 'wm-quality-check-title';
    title.textContent = selected.label;
    const category = document.createElement('span');
    category.className = 'wm-quality-check-category';
    category.textContent = selected.category;
    head.appendChild(title);
    head.appendChild(category);
    panel.appendChild(head);
    const metrics = document.createElement('div');
    metrics.className = 'wm-quality-check-metrics';
    metrics.appendChild(this._makeQualityCheckMetric('Measured', selected.value));
    metrics.appendChild(this._makeQualityCheckMetric('Threshold', selected.threshold || 'n/a'));
    metrics.appendChild(this._makeQualityCheckMetric('Source', selected.source || 'runtime'));
    metrics.appendChild(this._makeQualityCheckMetric('Fix', selected.fix || 'Review theme tokens'));
    panel.appendChild(metrics);
    const apply = document.createElement('button');
    apply.type = 'button';
    apply.className = 'wm-quality-fix';
    apply.dataset.qualityFix = selected.key;
    apply.textContent = 'Apply fix';
    panel.appendChild(apply);
    return panel;
  }

  _makeQualityRecommendations(items) {
    const panel = document.createElement('div');
    panel.className = 'wm-quality-recommendations';
    panel.dataset.qualityRecommendations = 'actionable';
    const title = document.createElement('div');
    title.className = 'wm-quality-recommendations-title';
    title.textContent = 'Recommended changes';
    panel.appendChild(title);
    const list = document.createElement('div');
    list.className = 'wm-quality-recommendations-list';
    this._qualityRecommendationItems(items).forEach((item) => {
      const action = document.createElement('button');
      action.type = 'button';
      action.className = 'wm-quality-recommendation wm-quality-fix';
      action.dataset.qualityFix = item.key;
      const label = document.createElement('span');
      label.className = 'wm-quality-recommendation-label';
      label.textContent = item.label;
      const change = document.createElement('strong');
      change.className = 'wm-quality-recommendation-change';
      change.textContent = item.fix || 'Review theme tokens';
      const evidence = document.createElement('span');
      evidence.className = 'wm-quality-recommendation-evidence';
      evidence.textContent = (item.value || 'n/a') + ' vs ' + (item.threshold || 'policy');
      action.appendChild(label);
      action.appendChild(change);
      action.appendChild(evidence);
      list.appendChild(action);
    });
    panel.appendChild(list);
    return panel;
  }

  _qualityRecommendationItems(items) {
    const checks = items || this._qualityInspectorItems();
    const preferred = ['color', 'motion', 'material', 'touch', 'titlebar', 'input', 'bounds'];
    const picked = [];
    const add = (item) => {
      if (item && !picked.some((candidate) => candidate.key === item.key)) picked.push(item);
    };
    checks.filter((item) => !item.good).forEach(add);
    preferred.forEach((key) => add(checks.find((item) => item.key === key)));
    return picked.slice(0, 3);
  }

  _makeQualityReportPreview(items) {
    const report = this._qualityReportText(items);
    const panel = document.createElement('div');
    panel.className = 'wm-quality-report';
    panel.dataset.qualityReport = 'shareable';
    const title = document.createElement('div');
    title.className = 'wm-quality-report-title';
    title.textContent = 'Quality report';
    panel.appendChild(title);
    const summary = document.createElement('div');
    summary.className = 'wm-quality-report-summary';
    summary.textContent = report.split('\n').slice(0, 4).join(' | ');
    panel.appendChild(summary);
    const copy = document.createElement('button');
    copy.type = 'button';
    copy.className = 'wm-quality-report-copy';
    copy.dataset.qualityAction = 'copy_report';
    copy.textContent = 'Copy report';
    panel.appendChild(copy);
    return panel;
  }

  _qualityReportText(items = null) {
    const checks = items || this._qualityInspectorItems();
    const passed = checks.filter((item) => item.good).length;
    const total = Math.max(1, checks.length);
    const score = Math.round((passed / total) * 100);
    const lines = [
      'Simple WM quality report',
      'Score: ' + score + '%',
      'Checks: ' + passed + '/' + total,
      'Motion: ' + this._normalizeMotionPreference(this._readMotionPreference()),
      'Material: ' + this._normalizeTransparencyPreference(this._readTransparencyPreference()),
      'Density: ' + this._densityMode,
      'Window motion: ' + this._windowTransitionMode
    ];
    checks.forEach((item) => {
      lines.push((item.good ? 'PASS ' : 'WARN ') + item.label + ': ' + item.value + ' target ' + (item.threshold || 'n/a'));
    });
    return lines.join('\n');
  }

  _copyQualityReport() {
    const report = this._qualityReportText();
    if (typeof navigator !== 'undefined' && navigator.clipboard?.writeText) {
      navigator.clipboard.writeText(report).catch(() => {});
    }
    this._sendWindowCmd('quality_report_copy', { quality_report: report, quality_score: this._qualityReportScore(report) });
    this._showSystemHud('Quality report', 'Copied', 1500);
  }

  _qualityReportScore(report) {
    const match = String(report || '').match(/Score:\s*(\d+)%/);
    return match ? Number(match[1]) : 0;
  }

  _applyQualityFix(check) {
    const target = check || this._selectedQualityCheck;
    if (target === 'color') {
      this._toggleAccentPalette(true);
    } else if (target === 'motion') {
      this.setMotionPreference('reduced');
    } else if (target === 'material') {
      this.setTransparencyPreference('reduced');
    } else {
      this._toggleWindowArrangePalette(true);
    }
    this._sendWindowCmd('quality_fix', { quality_check: target });
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _makeQualityCheckMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-check-metric';
    const name = document.createElement('span');
    name.className = 'wm-quality-check-label';
    name.textContent = label;
    const result = document.createElement('strong');
    result.className = 'wm-quality-check-value';
    result.textContent = value;
    metric.appendChild(name);
    metric.appendChild(result);
    return metric;
  }

  _makeQualitySwatches(root) {
    const swatches = document.createElement('div');
    swatches.className = 'wm-quality-swatches';
    [
      ['Background', root.getPropertyValue('--ui-bg') || '#0a0a0f'],
      ['Text', root.getPropertyValue('--ui-text') || '#f8fafc'],
      ['Accent', root.getPropertyValue('--ui-accent') || '#7dd3fc']
    ].forEach(([label, value]) => {
      const item = document.createElement('span');
      item.className = 'wm-quality-swatch';
      item.dataset.qualitySwatch = label.toLowerCase();
      const chip = document.createElement('span');
      chip.className = 'wm-quality-swatch-chip';
      chip.style.background = value.trim();
      const text = document.createElement('span');
      text.className = 'wm-quality-swatch-label';
      text.textContent = label;
      item.appendChild(chip);
      item.appendChild(text);
      swatches.appendChild(item);
    });
    return swatches;
  }

  _makeQualityMetric(label, value) {
    const metric = document.createElement('span');
    metric.className = 'wm-quality-metric';
    metric.dataset.qualityMetric = label.toLowerCase().replace(/\s+/g, '_');
    const name = document.createElement('span');
    name.className = 'wm-quality-metric-label';
    name.textContent = label;
    const number = document.createElement('strong');
    number.className = 'wm-quality-metric-value';
    number.textContent = value;
    metric.appendChild(name);
    metric.appendChild(number);
    return metric;
  }

  _makeQualityAuditPolicy() {
    const policy = document.createElement('div');
    policy.className = 'wm-quality-audit-policy';
    [
      ['contrast', 'WCAG contrast', '>= 4.5:1'],
      ['layout', 'Layout tokens', 'safe 16px / gap 12px'],
      ['touch', 'Touch target', '>= 44px'],
      ['bounds', 'Panel bounds', '<= 680px']
    ].forEach(([key, label, value]) => {
      const item = document.createElement('span');
      item.className = 'wm-quality-policy-item';
      item.dataset.qualityPolicy = key;
      const name = document.createElement('span');
      name.className = 'wm-quality-policy-label';
      name.textContent = label;
      const rule = document.createElement('strong');
      rule.className = 'wm-quality-policy-value';
      rule.textContent = value;
      item.appendChild(name);
      item.appendChild(rule);
      policy.appendChild(item);
    });
    return policy;
  }

  _makeQualityEvidencePreview() {
    const preview = document.createElement('div');
    preview.className = 'wm-quality-evidence-preview';
    preview.dataset.qualityEvidence = 'review-ready';
    [
      ['tokens', 'Theme tokens', '--ui-bg / --ui-text / --ui-motion'],
      ['dom', 'DOM metrics', 'bounds, hit target, titlebar'],
      ['fixture', 'Preview fixture', 'build/simple_wm_modern_preview.html'],
      ['capture', 'Capture path', 'screen capture + copied report']
    ].forEach(([kind, label, value]) => {
      preview.appendChild(this._makeQualityEvidenceItem(kind, label, value));
    });
    return preview;
  }

  _makeQualityEvidenceItem(kind, label, value) {
    const item = document.createElement('span');
    item.className = 'wm-quality-evidence-item';
    item.dataset.qualityEvidenceSource = kind;
    const mark = document.createElement('span');
    mark.className = 'wm-quality-evidence-mark';
    mark.setAttribute('aria-hidden', 'true');
    mark.textContent = label.charAt(0);
    const name = document.createElement('span');
    name.className = 'wm-quality-evidence-label';
    name.textContent = label;
    const detail = document.createElement('strong');
    detail.className = 'wm-quality-evidence-value';
    detail.textContent = value;
    item.appendChild(mark);
    item.appendChild(name);
    item.appendChild(detail);
    return item;
  }

  _makeQualityActions() {
    const actions = document.createElement('div');
    actions.className = 'wm-quality-actions';
    actions.setAttribute('role', 'group');
    actions.setAttribute('aria-label', 'Quality inspector actions');
    [
      ['motion', 'Reduce motion'],
      ['material', 'Reduce glass'],
      ['energy_low', 'Low power'],
      ['energy_critical', 'Critical saver'],
      ['calm_mode', 'Calm mode'],
      ['layout', 'Open layout tools'],
      ['contrast', 'Accent palette'],
      ['copy_report', 'Copy report']
    ].forEach(([action, label]) => {
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'wm-quality-action';
      button.dataset.qualityAction = action;
      button.textContent = label;
      actions.appendChild(button);
    });
    return actions;
  }

  _activateQualityInspectorAction(action) {
    if (action === 'motion') {
      this.setMotionPreference('reduced');
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'reduced' });
    } else if (action === 'material') {
      this.setTransparencyPreference('reduced');
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'reduced' });
    } else if (action === 'energy_low') {
      this.setEnergyPreference('low');
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'low' });
    } else if (action === 'energy_critical') {
      this.setEnergyPreference('critical');
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'critical' });
    } else if (action === 'calm_mode') {
      this.setQuietModePreference('on');
      this.setBackdropMotionPreference('static');
      this.setBackdropIntensityPreference('quiet');
      this.setChromeVerbosityPreference('minimal');
      this.setDockVisibilityPreference('auto');
      this.setFeedbackPreference('subtle');
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'quiet_static_minimal' });
    } else if (action === 'layout') {
      this._toggleWindowArrangePalette(true);
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'layout_tools' });
    } else if (action === 'contrast') {
      this._toggleAccentPalette(true);
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'accent_palette' });
    } else if (action === 'copy_report') {
      this._copyQualityReport();
      this._sendWindowCmd('quality_action', { quality_action: action, value: 'report' });
    }
    if (this._qualityInspector && !this._qualityInspector.hidden) this._renderQualityInspector();
  }

  _qualityCssPx(style, name, fallback) {
    return Math.round(parseFloat(style.getPropertyValue(name) || '') || fallback);
  }

  _makeQualityInspectorRow(item) {
    const row = document.createElement('button');
    const selected = item.key === this._selectedQualityCheck;
    row.type = 'button';
    row.className = 'wm-quality-row' + (item.good ? ' good' : ' warn') + (selected ? ' active' : '');
    row.dataset.qualityCheck = item.key;
    row.setAttribute('aria-pressed', selected ? 'true' : 'false');
    const label = document.createElement('span');
    label.className = 'wm-quality-label';
    label.textContent = item.label;
    const value = document.createElement('span');
    value.className = 'wm-quality-value';
    value.textContent = item.value;
    row.appendChild(label);
    row.appendChild(value);
    return row;
  }

  _qualityElementHeight(el) {
    if (!el) return 0;
    return Math.round(el.getBoundingClientRect().height);
  }

  _qualityElementWidth(el) {
    if (!el) return 0;
    return Math.round(el.getBoundingClientRect().width);
  }

  _qualityElementMinHeight(el) {
    if (!el) return 0;
    const style = getComputedStyle(el);
    return Math.round(parseFloat(style.minHeight || '0') || this._qualityElementHeight(el));
  }

  _qualityElementFontSize(el, fallback) {
    if (!el) return fallback;
    const style = getComputedStyle(el);
    return Math.round(parseFloat(style.fontSize || '') || fallback);
  }

  _qualityElementZIndex(el, fallback) {
    if (!el) return String(fallback);
    const value = getComputedStyle(el).zIndex;
    return value && value !== 'auto' ? value : String(fallback);
  }

  _qualityContrastRatio(bg, fg) {
    const a = this._qualityRgb(bg);
    const b = this._qualityRgb(fg);
    const la = this._qualityLuminance(a);
    const lb = this._qualityLuminance(b);
    const hi = Math.max(la, lb);
    const lo = Math.min(la, lb);
    return Math.round(((hi + 0.05) / (lo + 0.05)) * 10) / 10;
  }

  _qualityRgb(value) {
    const text = String(value || '').trim();
    const hex = text.match(/^#([0-9a-f]{6})$/i);
    if (hex) {
      return [parseInt(hex[1].slice(0, 2), 16), parseInt(hex[1].slice(2, 4), 16), parseInt(hex[1].slice(4, 6), 16)];
    }
    const rgb = text.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)/i);
    if (rgb) return [Number(rgb[1]), Number(rgb[2]), Number(rgb[3])];
    return [10, 10, 15];
  }

  _qualityLuminance(rgb) {
    const channels = rgb.map((v) => {
      const n = Math.max(0, Math.min(255, v)) / 255;
      return n <= 0.03928 ? n / 12.92 : Math.pow((n + 0.055) / 1.055, 2.4);
    });
    return channels[0] * 0.2126 + channels[1] * 0.7152 + channels[2] * 0.0722;
  }

  _ensureWidgetGallery() {
    if (this._widgetGallery && this._widgetGallery.isConnected) return this._widgetGallery;
    const gallery = document.createElement('aside');
    gallery.className = 'wm-widget-gallery';
    gallery.hidden = true;
    gallery.setAttribute('role', 'dialog');
    gallery.setAttribute('aria-label', 'Widget gallery');
    gallery.addEventListener('pointerdown', (event) => event.stopPropagation());
    gallery.addEventListener('mousedown', (event) => event.stopPropagation());
    gallery.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const card = target?.closest('.wm-widget-gallery-card');
      if (!card || !gallery.contains(card)) return;
      this._widgetGalleryActiveIndex = Number(card.dataset.widgetIndex || '0') || 0;
      this._activateWidgetGallerySelection();
    });
    gallery.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveWidgetGallerySelection(1);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveWidgetGallerySelection(-1);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._moveWidgetGallerySelection(-999);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._moveWidgetGallerySelection(999);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._activateWidgetGallerySelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleWidgetGallery(false);
      }
    });
    document.body.appendChild(gallery);
    this._widgetGallery = gallery;
    return gallery;
  }

  _toggleWidgetGallery(open = null) {
    const gallery = this._ensureWidgetGallery();
    const shouldOpen = open == null ? gallery.hidden : open;
    gallery.hidden = !shouldOpen;
    if (shouldOpen) this._renderWidgetGallery();
    return shouldOpen;
  }

  _renderWidgetGallery() {
    const gallery = this._ensureWidgetGallery();
    gallery.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-widget-gallery-title';
    title.textContent = 'Widget gallery';
    gallery.appendChild(title);
    const grid = document.createElement('div');
    grid.className = 'wm-widget-gallery-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Available widgets');
    grid.setAttribute('aria-activedescendant', `wm-widget-gallery-card-${this._widgetGalleryActiveIndex}`);
    grid.appendChild(this._makeWidgetGalleryCard('clock', 'Clock', this._desktopClockLabel(), 'Local time', 0));
    grid.appendChild(this._makeWidgetGalleryCard('system', 'Motion', this._normalizeMotionPreference(this._readMotionPreference()), 'Preferences', 1));
    grid.appendChild(this._makeWidgetGalleryCard('workspace', 'Workspace', 'Simple WM', 'Wallpaper', 2));
    gallery.appendChild(grid);
    const status = document.createElement('div');
    status.className = 'wm-widget-gallery-status';
    status.setAttribute('role', 'status');
    status.setAttribute('aria-live', 'polite');
    status.textContent = 'Choose a widget to add';
    gallery.appendChild(status);
    this._syncWidgetGallerySelection(false);
  }

  _makeWidgetGalleryCard(kind, title, value, meta, index) {
    const card = document.createElement('button');
    card.type = 'button';
    const active = index === this._widgetGalleryActiveIndex;
    card.id = `wm-widget-gallery-card-${index}`;
    card.className = 'wm-widget-gallery-card' + (active ? ' active' : '');
    card.dataset.widgetKind = kind;
    card.dataset.widgetIndex = String(index);
    card.setAttribute('role', 'option');
    card.setAttribute('aria-selected', active ? 'true' : 'false');
    card.tabIndex = active ? 0 : -1;
    card.setAttribute('aria-label', `Add ${title} widget`);
    card.appendChild(this._makeRoundIcon('wm-overview-icon', title));
    const titleEl = document.createElement('span');
    titleEl.className = 'wm-widget-gallery-card-title';
    titleEl.textContent = title;
    card.appendChild(titleEl);
    const valueEl = document.createElement('strong');
    valueEl.className = 'wm-widget-gallery-card-value';
    valueEl.textContent = value;
    card.appendChild(valueEl);
    const metaEl = document.createElement('span');
    metaEl.className = 'wm-widget-gallery-card-meta';
    metaEl.textContent = meta;
    card.appendChild(metaEl);
    return card;
  }

  _moveWidgetGallerySelection(delta) {
    const gallery = this._ensureWidgetGallery();
    const cards = Array.from(gallery.querySelectorAll('.wm-widget-gallery-card'));
    if (!cards.length) return;
    const max = cards.length - 1;
    this._widgetGalleryActiveIndex = Math.max(0, Math.min(max, this._widgetGalleryActiveIndex + delta));
    this._syncWidgetGallerySelection(true);
  }

  _syncWidgetGallerySelection(shouldFocus = true) {
    const gallery = this._ensureWidgetGallery();
    const grid = gallery.querySelector('.wm-widget-gallery-grid');
    const cards = Array.from(gallery.querySelectorAll('.wm-widget-gallery-card'));
    if (!cards.length) return;
    const activeIndex = Math.max(0, Math.min(cards.length - 1, this._widgetGalleryActiveIndex));
    this._widgetGalleryActiveIndex = activeIndex;
    if (grid) grid.setAttribute('aria-activedescendant', `wm-widget-gallery-card-${activeIndex}`);
    cards.forEach((card, index) => {
      const active = index === activeIndex;
      card.classList.toggle('active', active);
      card.setAttribute('aria-selected', active ? 'true' : 'false');
      card.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) card.focus();
    });
  }

  _activateWidgetGallerySelection() {
    const gallery = this._ensureWidgetGallery();
    const card = gallery.querySelector(`.wm-widget-gallery-card[data-widget-index="${this._widgetGalleryActiveIndex}"]`);
    const kind = card?.dataset.widgetKind || '';
    const added = this._addWidgetFromGallery(kind);
    const status = gallery.querySelector('.wm-widget-gallery-status');
    if (status) status.textContent = added ? `${kind || 'widget'} widget added` : 'Widget could not be added';
    if (added) this._toggleWidgetGallery(false);
    return added;
  }

  _addWidgetFromGallery(kind) {
    const shelf = this._ensureDesktopWidgets();
    if (!shelf) return false;
    shelf.classList.remove('collapsed');
    const widgetKind = String(kind || '').trim().toLowerCase();
    if (widgetKind === 'clock') {
      const widget = this._makeDesktopWidget('wm-widget-clock', 'Local', this._desktopClockLabel(), 'Clock');
      shelf.appendChild(widget);
      this._markDesktopWidgetAction(widget, 'add');
      this._sendWindowCmd('widget_add', { widget_kind: widgetKind });
      return true;
    }
    if (widgetKind === 'system') {
      const widget = this._makeDesktopWidget('wm-widget-system', 'Motion', this._normalizeMotionPreference(this._readMotionPreference()), 'Settings');
      shelf.appendChild(widget);
      this._markDesktopWidgetAction(widget, 'add');
      this._sendWindowCmd('widget_add', { widget_kind: widgetKind });
      return true;
    }
    if (widgetKind === 'workspace') {
      const widget = this._makeDesktopWidget('wm-widget-workspace', 'Workspace', 'Simple WM', 'wallpaper: ' + this._normalizeWallpaperPreference(this._readWallpaperPreference()));
      shelf.appendChild(widget);
      this._markDesktopWidgetAction(widget, 'add');
      this._sendWindowCmd('widget_add', { widget_kind: widgetKind });
      return true;
    }
    return false;
  }

  _ensureAppLauncher() {
    if (this._appLauncher && this._appLauncher.isConnected) return this._appLauncher;
    const launcher = document.createElement('aside');
    launcher.className = 'wm-app-launcher';
    launcher.hidden = true;
    launcher.setAttribute('role', 'dialog');
    launcher.setAttribute('aria-label', 'App launcher');
    launcher.addEventListener('pointerdown', (event) => event.stopPropagation());
    launcher.addEventListener('mousedown', (event) => event.stopPropagation());
    const input = document.createElement('input');
    input.className = 'wm-app-launcher-input';
    input.type = 'text';
    input.placeholder = 'Search apps';
    input.setAttribute('aria-label', 'Search apps');
    input.setAttribute('aria-controls', 'wm-app-launcher-grid');
    input.setAttribute('aria-activedescendant', 'wm-app-launcher-tile-0');
    input.addEventListener('input', () => this._renderAppLauncher());
    input.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveAppLauncherSelection(1);
      } else if (event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveAppLauncherSelection(-1);
      } else if (event.key === 'Enter') {
        event.preventDefault();
        this._executeAppLauncherSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleAppLauncher(false);
      }
    });
    launcher.appendChild(input);
    const filters = document.createElement('div');
    filters.className = 'wm-app-launcher-filters';
    filters.setAttribute('aria-label', 'App categories');
    filters.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const filter = target?.closest('[data-app-category]');
      if (!filter || !filters.contains(filter)) return;
      this._setAppLauncherCategory(filter.dataset.appCategory || 'all');
    });
    launcher.appendChild(filters);
    const grid = document.createElement('div');
    grid.id = 'wm-app-launcher-grid';
    grid.className = 'wm-app-launcher-grid';
    grid.setAttribute('role', 'listbox');
    grid.setAttribute('aria-label', 'Applications');
    grid.setAttribute('aria-activedescendant', 'wm-app-launcher-tile-0');
    grid.addEventListener('click', (event) => {
      const target = event.target instanceof Element ? event.target : event.target?.parentElement;
      const tile = target?.closest('.wm-app-launcher-tile');
      if (!tile || !grid.contains(tile)) return;
      this._appLauncherActiveIndex = Number(tile.dataset.launcherIndex || '0') || 0;
      this._executeAppLauncherSelection();
    });
    grid.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveAppLauncherSelection(1, true);
      } else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveAppLauncherSelection(-1, true);
      } else if (event.key === 'Home') {
        event.preventDefault();
        this._setAppLauncherSelection(0, true);
      } else if (event.key === 'End') {
        event.preventDefault();
        this._setAppLauncherSelection(this._appLauncherItems.length - 1, true);
      } else if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        this._executeAppLauncherSelection();
      } else if (event.key === 'Escape') {
        event.preventDefault();
        this._toggleAppLauncher(false);
      }
    });
    launcher.appendChild(grid);
    document.body.appendChild(launcher);
    this._appLauncher = launcher;
    this._appLauncherInput = input;
    this._appLauncherFilters = filters;
    this._appLauncherGrid = grid;
    return launcher;
  }

  _toggleAppLauncher(open = null) {
    const launcher = this._ensureAppLauncher();
    const shouldOpen = open == null ? launcher.hidden : open;
    launcher.hidden = !shouldOpen;
    if (shouldOpen) {
      this._appLauncherInput.value = '';
      this._appLauncherCategory = 'all';
      this._appLauncherActiveIndex = 0;
      this._renderAppLauncher();
      this._appLauncherInput.focus();
    }
    return shouldOpen;
  }

  _appLauncherApps() {
    if (this._launcherApps.length) return this._launcherApps;
    return [
      { app_id: 'simple.ide', display_name: 'Simple IDE', icon: 'I', category: 'work' },
      { app_id: 'simple.browser', display_name: 'Browser', icon: 'B', category: 'work' },
      { app_id: 'simple.terminal', display_name: 'Terminal', icon: 'T', category: 'tools' },
      { app_id: 'simple.settings', display_name: 'Settings', icon: 'S', category: 'system' }
    ];
  }

  _renderAppLauncher() {
    if (!this._appLauncherGrid) return;
    const query = String(this._appLauncherInput?.value || '').trim().toLowerCase();
    if (this._appLauncherFilters) this._renderAppLauncherFilters();
    const apps = this._appLauncherApps().filter((app) => {
      const category = this._appLauncherCategoryForApp(app.app_id || '', app.display_name || '', app.category || '');
      const label = `${app.display_name || ''} ${app.app_id || ''} ${category}`.toLowerCase();
      return (this._appLauncherCategory === 'all' || category === this._appLauncherCategory) && (!query || label.includes(query));
    });
    this._appLauncherItems = apps;
    this._appLauncherActiveIndex = Math.min(this._appLauncherActiveIndex, Math.max(apps.length - 1, 0));
    this._appLauncherGrid.innerHTML = '';
    if (apps.length) {
      this._appLauncherGrid.setAttribute('aria-activedescendant', `wm-app-launcher-tile-${this._appLauncherActiveIndex}`);
      this._appLauncherInput?.setAttribute('aria-activedescendant', `wm-app-launcher-tile-${this._appLauncherActiveIndex}`);
    } else {
      this._appLauncherGrid.removeAttribute('aria-activedescendant');
      this._appLauncherInput?.removeAttribute('aria-activedescendant');
    }
    apps.forEach((app, index) => {
      const active = index === this._appLauncherActiveIndex;
      const tile = document.createElement('button');
      tile.type = 'button';
      tile.id = `wm-app-launcher-tile-${index}`;
      tile.className = 'wm-app-launcher-tile' + (active ? ' active' : '');
      tile.dataset.launcherIndex = String(index);
      tile.dataset.appId = app.app_id || '';
      tile.dataset.appCategory = this._appLauncherCategoryForApp(app.app_id || '', app.display_name || '', app.category || '');
      tile.tabIndex = active ? 0 : -1;
      tile.setAttribute('role', 'option');
      tile.setAttribute('aria-selected', active ? 'true' : 'false');
      tile.setAttribute('aria-label', `Launch ${app.display_name || app.app_id}`);
      tile.appendChild(this._makeRoundIcon('wm-app-launcher-icon', app.icon || app.display_name || app.app_id));
      const name = document.createElement('span');
      name.className = 'wm-app-launcher-name';
      name.textContent = app.display_name || app.app_id;
      tile.appendChild(name);
      const category = document.createElement('span');
      category.className = 'wm-app-launcher-category';
      category.textContent = this._appLauncherCategoryLabel(tile.dataset.appCategory);
      tile.appendChild(category);
      this._appLauncherGrid.appendChild(tile);
    });
    if (!apps.length) {
      const empty = document.createElement('div');
      empty.className = 'wm-app-launcher-empty';
      empty.textContent = 'No matching apps';
      this._appLauncherGrid.appendChild(empty);
    }
  }

  _appLauncherCategories() {
    return [
      { id: 'all', label: 'All' },
      { id: 'work', label: 'Work' },
      { id: 'system', label: 'System' },
      { id: 'tools', label: 'Tools' }
    ];
  }

  _renderAppLauncherFilters() {
    this._appLauncherFilters.innerHTML = '';
    for (const category of this._appLauncherCategories()) this._appLauncherFilters.appendChild(this._makeAppLauncherCategoryButton(category));
  }

  _makeAppLauncherCategoryButton(category) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-app-launcher-filter' + (this._appLauncherCategory === category.id ? ' active' : '');
    button.dataset.appCategory = category.id;
    button.setAttribute('aria-pressed', this._appLauncherCategory === category.id ? 'true' : 'false');
    button.textContent = category.label;
    return button;
  }

  _setAppLauncherCategory(categoryId) {
    const next = this._appLauncherCategories().some((category) => category.id === categoryId) ? categoryId : 'all';
    if (this._appLauncherCategory === next) return;
    this._appLauncherCategory = next;
    this._appLauncherActiveIndex = 0;
    this._renderAppLauncher();
  }

  _appLauncherCategoryForApp(appId, label = '', explicit = '') {
    const normalized = String(explicit || '').toLowerCase();
    if (normalized === 'work' || normalized === 'system' || normalized === 'tools') return normalized;
    const value = `${appId || ''} ${label || ''}`.toLowerCase();
    if (value.includes('setting') || value.includes('control')) return 'system';
    if (value.includes('terminal') || value.includes('tool') || value.includes('debug')) return 'tools';
    return 'work';
  }

  _appLauncherCategoryLabel(categoryId) {
    const category = this._appLauncherCategories().find((item) => item.id === categoryId);
    return category ? category.label : 'Work';
  }

  _moveAppLauncherSelection(delta, shouldFocus = false) {
    if (!this._appLauncher || this._appLauncher.hidden) return;
    const count = this._appLauncherItems.length;
    if (!count) return;
    this._appLauncherActiveIndex = (this._appLauncherActiveIndex + delta + count) % count;
    this._syncAppLauncherSelection(shouldFocus);
  }

  _setAppLauncherSelection(index, shouldFocus = false) {
    if (!this._appLauncher || this._appLauncher.hidden) return;
    const count = this._appLauncherItems.length;
    if (!count) return;
    this._appLauncherActiveIndex = Math.max(0, Math.min(count - 1, index));
    this._syncAppLauncherSelection(shouldFocus);
  }

  _syncAppLauncherSelection(shouldFocus = false) {
    if (!this._appLauncherGrid) return;
    const tiles = Array.from(this._appLauncherGrid.querySelectorAll('.wm-app-launcher-tile'));
    if (!tiles.length) return;
    const activeIndex = Math.max(0, Math.min(tiles.length - 1, this._appLauncherActiveIndex));
    this._appLauncherActiveIndex = activeIndex;
    const activeId = `wm-app-launcher-tile-${activeIndex}`;
    this._appLauncherGrid.setAttribute('aria-activedescendant', activeId);
    this._appLauncherInput?.setAttribute('aria-activedescendant', activeId);
    tiles.forEach((tile, index) => {
      const active = index === activeIndex;
      tile.classList.toggle('active', active);
      tile.setAttribute('aria-selected', active ? 'true' : 'false');
      tile.tabIndex = active ? 0 : -1;
      if (active && shouldFocus) tile.focus();
    });
  }

  _executeAppLauncherSelection() {
    if (!this._appLauncher || this._appLauncher.hidden) return false;
    const app = this._appLauncherItems[this._appLauncherActiveIndex];
    if (!app || !app.app_id) return false;
    const tile = this._appLauncherGrid?.querySelector(`.wm-app-launcher-tile[data-app-id="${CSS.escape(app.app_id)}"]`);
    this._sendLaunch(app.app_id, tile);
    this._toggleAppLauncher(false);
    return true;
  }

  _isImageIcon(value) {
    return value.startsWith('/') || value.startsWith('data:') || value.startsWith('http://') || value.startsWith('https://');
  }

  _makeTaskbarLabel(text) {
    const label = document.createElement('span');
    label.className = 'wm-taskbar-label';
    label.textContent = text || '';
    return label;
  }

  async _handleHostWindowCommand(payload) {
    const api = window.simpleUI;
    if (!api) return;
    const action = payload.action || '';
    const windowId = payload.window_id || '';
    try {
      if (this.transport === 'electron-ipc' && !this.nativeHostWindows) {
        this._handleEmbeddedHostWindowCommand(action, payload);
        return;
      }
      if (action === 'spawn_native_window' && api.spawnNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['focus'], () =>
          api.spawnNativeWindow(
            windowId,
            payload.url || '',
            payload.width || 800,
            payload.height || 600,
            payload.title || ''
          )
        );
      } else if (action === 'close_native_window' && api.closeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['close'], () => api.closeNativeWindow(windowId));
      } else if (action === 'focus_native_window' && api.focusNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['focus'], () => api.focusNativeWindow(windowId));
      } else if (action === 'minimize_native_window' && api.minimizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['minimize'], () => api.minimizeNativeWindow(windowId));
      } else if (action === 'restore_native_window' && api.restoreNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['restore'], () => api.restoreNativeWindow(windowId));
      } else if (action === 'move_native_window' && api.moveNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['move'], () => api.moveNativeWindow(windowId, payload.x || 0, payload.y || 0));
      } else if (action === 'resize_native_window' && api.resizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['resize'], () => api.resizeNativeWindow(windowId, payload.width || 800, payload.height || 600));
      } else if (action === 'maximize_native_window' && api.maximizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['maximize'], () => api.maximizeNativeWindow(windowId));
      } else if (action === 'unmaximize_native_window' && api.unmaximizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['unmaximize'], () => api.unmaximizeNativeWindow(windowId));
      } else if (action === 'set_native_window_title' && api.setNativeWindowTitle) {
        await this._runSuppressedNativeCommand(windowId, ['title'], () => api.setNativeWindowTitle(windowId, payload.title || ''));
      }
    } catch (err) {
      console.error('[WM] host window command failed:', action, err);
    }
  }

  _handleEmbeddedHostWindowCommand(action, payload) {
    const windowId = payload.window_id || payload.windowId || payload.surface_id || '';
    if (!windowId) return;
    if (action === 'spawn_native_window') {
      this._electronOpenWindow({
        windowId,
        title: payload.title || windowId,
        x: payload.x || 80,
        y: payload.y || 80,
        width: payload.width || 800,
        height: payload.height || 600,
        html: this._embeddedHostWindowHtml(payload)
      });
      this._sendWindowCmd('focus', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'close_native_window') {
      this._electronCloseWindow(windowId);
      this._sendWindowCmd('close', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'focus_native_window') {
      this._electronFocusWindow(windowId);
      this._sendWindowCmd('focus', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'minimize_native_window') {
      this._electronMinimizeWindow(windowId);
      this._sendWindowCmd('minimize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'restore_native_window') {
      this._electronFocusWindow(windowId);
      this._sendWindowCmd('restore', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'move_native_window') {
      this._electronMoveWindow(windowId, payload.x || 0, payload.y || 0);
      this._sendWindowCmd('move', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE, x: payload.x || 0, y: payload.y || 0 });
    } else if (action === 'resize_native_window') {
      this._electronResizeWindow(windowId, payload.width || 800, payload.height || 600);
      this._sendWindowCmd('resize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE, w: payload.width || 800, h: payload.height || 600 });
    } else if (action === 'maximize_native_window') {
      this._electronMaximizeWindow(windowId);
      this._sendWindowCmd('maximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'unmaximize_native_window') {
      this._electronUnmaximizeWindow(windowId);
      this._sendWindowCmd('unmaximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'set_native_window_title') {
      this._electronSetWindowTitle(windowId, payload.title || '');
      this._sendWindowCmd('set_title', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE, title: payload.title || '' });
    }
  }

  _embeddedHostWindowHtml(payload) {
    const url = payload.url || '';
    if (url && !url.startsWith('/')) {
      const safeUrl = _escapeAttr(url);
      return `<iframe src="${safeUrl}" style="display:block;width:100%;height:100%;border:0;background:transparent;" sandbox="allow-scripts allow-same-origin allow-forms allow-popups"></iframe>`;
    }
    const title = _escapeHtml(payload.title || payload.app_id || 'Simple App');
    const appId = _escapeHtml(payload.app_id || '');
    return `<div style="padding:20px"><h1>${title}</h1><p>${appId}</p></div>`;
  }

  _handleNativeWindowEvent(msg) {
    const type = msg.type || '';
    const windowId = msg.windowId || '';
    if (!type || !windowId) return;
    if (this._consumeNativeWindowEventSuppression(windowId, type)) return;
    if (type === 'focus') {
      this._sendWindowCmd('focus', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'minimize') {
      this._sendWindowCmd('minimize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'restore') {
      this._sendWindowCmd('restore', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'maximize') {
      this._sendWindowCmd('maximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'unmaximize') {
      this._sendWindowCmd('unmaximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'move') {
      this._sendNativeWindowCmdDebounced(windowId, type, () => this._sendWindowCmd('move', {
        window_id_hint: windowId,
        source: HOST_NATIVE_EVENT_SOURCE,
        x: Math.round(msg.x ?? msg.bounds?.x ?? 0),
        y: Math.round(msg.y ?? msg.bounds?.y ?? 0)
      }));
    } else if (type === 'resize') {
      this._sendNativeWindowCmdDebounced(windowId, type, () => this._sendWindowCmd('resize', {
        window_id_hint: windowId,
        source: HOST_NATIVE_EVENT_SOURCE,
        w: Math.round(msg.width ?? msg.bounds?.width ?? 0),
        h: Math.round(msg.height ?? msg.bounds?.height ?? 0)
      }));
    } else if (type === 'title') {
      this._sendNativeWindowCmdDebounced(windowId, type, () => this._sendWindowCmd('set_title', {
        window_id_hint: windowId,
        source: HOST_NATIVE_EVENT_SOURCE,
        title: msg.title || ''
      }));
    } else if (type === 'close') {
      this._sendWindowCmd('close', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    }
  }

  async _runSuppressedNativeCommand(windowId, types, invoke) {
    const tokens = types.map((type) => this._beginNativeWindowEventSuppression(windowId, type));
    try {
      const result = await invoke();
      const accepted = result !== false;
      for (const token of tokens) this._finishNativeWindowEventSuppression(token, accepted);
      return result;
    } catch (err) {
      for (const token of tokens) this._finishNativeWindowEventSuppression(token, false);
      throw err;
    }
  }

  _beginNativeWindowEventSuppression(windowId, type) {
    if (!windowId || !type) return null;
    const key = `${windowId}:${type}`;
    const existing = this._nativeWindowEventSuppressions.get(key);
    if (existing && existing.timer) clearTimeout(existing.timer);
    const entry = {
      key,
      expiresAt: Date.now() + NATIVE_SUPPRESSION_TTL_MS,
      timer: setTimeout(() => this._nativeWindowEventSuppressions.delete(key), NATIVE_SUPPRESSION_TTL_MS)
    };
    this._nativeWindowEventSuppressions.set(key, entry);
    return key;
  }

  _finishNativeWindowEventSuppression(token, accepted) {
    if (!token) return;
    if (accepted) return;
    const entry = this._nativeWindowEventSuppressions.get(token);
    if (entry && entry.timer) clearTimeout(entry.timer);
    this._nativeWindowEventSuppressions.delete(token);
  }

  _consumeNativeWindowEventSuppression(windowId, type) {
    const key = `${windowId}:${type}`;
    const entry = this._nativeWindowEventSuppressions.get(key);
    if (!entry) return false;
    if (Date.now() > entry.expiresAt) {
      if (entry.timer) clearTimeout(entry.timer);
      this._nativeWindowEventSuppressions.delete(key);
      return false;
    }
    return true;
  }

  _sendNativeWindowCmdDebounced(windowId, type, sendFn) {
    const key = `${windowId}:${type}`;
    const existing = this._nativeWindowBurstTimers.get(key);
    if (existing) clearTimeout(existing);
    const timer = setTimeout(() => {
      this._nativeWindowBurstTimers.delete(key);
      sendFn();
    }, NATIVE_BURST_DEBOUNCE_MS);
    this._nativeWindowBurstTimers.set(key, timer);
  }

  receiveFrame(frame) {
    if (!frame || typeof frame !== 'object') return;
    this._dispatch(frame);
  }

  handleMessage(frame) {
    this.receiveFrame(frame);
  }

  receiveElectronMessage(msg) {
    if (!msg || !msg.type) return;
    switch (msg.type) {
      case 'openWindow':
        this._electronOpenWindow(msg);
        break;
      case 'renderWindow':
        this._electronRenderWindow(msg.windowId, msg.html || '');
        break;
      case 'closeWindow':
        this._electronCloseWindow(msg.windowId);
        break;
      case 'moveWindow':
        this._electronMoveWindow(msg.windowId, msg.x, msg.y);
        break;
      case 'resizeWindow':
        this._electronResizeWindow(msg.windowId, msg.width, msg.height);
        break;
      case 'focusWindow':
        this._electronFocusWindow(msg.windowId);
        break;
      case 'minimizeWindow':
        this._electronMinimizeWindow(msg.windowId);
        break;
      default:
        break;
    }
  }

  _electronOpenWindow(msg) {
    const windowId = String(msg.windowId || '');
    if (!windowId || !this.desktop) return;
    if (this._electronWindows.has(windowId)) {
      this._electronRenderWindow(windowId, msg.html || '');
      this._electronFocusWindow(windowId);
      return;
    }
    const winEl = document.createElement('div');
    winEl.className = 'wm-window';
    winEl.dataset.surfaceId = windowId;
    winEl.dataset.canonicalId = `${windowId}#root`;
    winEl.style.left = `${Number(msg.x) || 80}px`;
    winEl.style.top = `${Number(msg.y) || 80}px`;
    winEl.style.width = `${Number(msg.width) || 720}px`;
    winEl.style.height = `${Number(msg.height) || 480}px`;

    const titlebar = document.createElement('div');
    titlebar.className = 'wm-titlebar';
    const lights = document.createElement('div');
    lights.className = 'wm-traffic-lights';
    for (const [action, label, aria] of [['close', 'x', 'Close window'], ['minimize', '-', 'Minimize window'], ['maximize', '+', 'Maximize window']]) {
      const btn = document.createElement('button');
      btn.dataset.action = action;
      btn.textContent = label;
      btn.className = `wm-btn-${action}`;
      btn.setAttribute('aria-label', aria);
      if (action === 'maximize') {
        btn.setAttribute('aria-haspopup', 'dialog');
        btn.setAttribute('aria-controls', 'wm-snap-layout-palette');
      }
      lights.appendChild(btn);
    }
    const icon = this._makeRoundIcon('wm-titlebar-icon', msg.icon || msg.title || windowId || 'S');
    const title = document.createElement('div');
    title.className = 'wm-title';
    title.textContent = msg.title || windowId;
    const command = this._makeTitleInput(msg);
    const context = document.createElement('div');
    context.className = 'wm-title-context';
    context.textContent = msg.context || msg.appId || msg.app_id || windowId;
    titlebar.appendChild(lights);
    titlebar.appendChild(icon);
    titlebar.appendChild(title);
    titlebar.appendChild(command);
    titlebar.appendChild(context);
    winEl.appendChild(titlebar);

    const body = document.createElement('div');
    body.className = 'wm-body';
    body.dataset.surfaceId = windowId;
    body.innerHTML = msg.html || '';
    winEl.appendChild(body);
    this.desktop.appendChild(winEl);
    this._markWindowLifecycle(winEl, 'opening');
    this._electronWindows.set(windowId, {
      winEl,
      body,
      title,
      titleText: msg.title || windowId,
      minimized: false,
      restoreBounds: null
    });
    this._electronFocusWindow(windowId);
  }

  _electronRenderWindow(windowId, html) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (entry) entry.body.innerHTML = html;
  }

  _titleCommandKind(value) {
    const commandText = String(value || '').trim();
    if (!commandText) return 'empty';
    if (commandText.startsWith('/') || commandText.startsWith('./') || commandText.includes('/')) return 'path';
    if (commandText.startsWith('http://') || commandText.startsWith('https://')) return 'url';
    if (commandText.includes(' ')) return 'search';
    return 'command';
  }

  _submitTitleCommandInput(input) {
    if (!input) return false;
    const commandText = String(input.value || '').trim();
    if (!commandText) return false;
    const win = input.closest('.wm-window');
    const commandKind = this._titleCommandKind(commandText);
    const commandContext = input.placeholder || win?.querySelector('.wm-title-context')?.textContent || '';
    input.dataset.lastSubmittedValue = commandText;
    this._markTitleCommandSubmitted(input, commandKind, commandText);
    this._sendWindowCmd('title_command', {
      window_id_hint: win?.dataset.surfaceId || win?.dataset.canonicalId || '',
      command_text: commandText,
      command_kind: commandKind,
      command_context: commandContext
    });
    this._showTitleCommandSuggestions(input, false);
    return true;
  }

  _markTitleCommandSubmitted(input, commandKind = '', commandText = '') {
    if (!input) return;
    const prior = this._titleCommandFeedbackTimers.get(input);
    if (prior) window.clearTimeout(prior);
    const kind = String(commandKind || this._titleCommandKind(commandText || input.value || '') || 'command');
    const winEl = input.closest('.wm-window');
    input.classList.remove('command-submitted');
    void input.offsetWidth;
    input.classList.add('command-submitted');
    input.dataset.commandFeedback = 'submitted';
    input.dataset.commandKind = kind;
    if (winEl) winEl.dataset.titleCommandFeedback = kind;
    const timer = window.setTimeout(() => {
      input.classList.remove('command-submitted');
      delete input.dataset.commandFeedback;
      if (winEl && winEl.dataset.titleCommandFeedback === kind) delete winEl.dataset.titleCommandFeedback;
      this._titleCommandFeedbackTimers.delete(input);
    }, 560);
    this._titleCommandFeedbackTimers.set(input, timer);
  }

  _focusActiveTitleInput() {
    const focused = this.desktop?.querySelector('.wm-window.focused .wm-title-input');
    const fallback = this.desktop?.querySelector('.wm-window .wm-title-input');
    const input = focused || fallback;
    if (!input) return false;
    input.focus();
    input.select();
    this._showTitleCommandSuggestions(input, true);
    return true;
  }

  _ensureTitleCommandSuggestions() {
    if (this._titleCommandSuggestionsPanel && this._titleCommandSuggestionsPanel.isConnected) return this._titleCommandSuggestionsPanel;
    const panel = document.createElement('aside');
    panel.className = 'wm-title-suggestions';
    panel.hidden = true;
    panel.setAttribute('role', 'listbox');
    panel.setAttribute('aria-label', 'Window command suggestions');
    panel.addEventListener('mousedown', (event) => event.preventDefault());
    panel.addEventListener('click', (event) => {
      const item = event.target.closest('.wm-title-suggestion-item');
      if (!item || !panel.contains(item)) return;
      this._applyTitleCommandSuggestion(item.dataset.value || '');
    });
    document.body.appendChild(panel);
    this._titleCommandSuggestionsPanel = panel;
    return panel;
  }

  _showTitleCommandSuggestions(input, open = true) {
    const panel = this._ensureTitleCommandSuggestions();
    if (!open || !input) {
      panel.hidden = true;
      return;
    }
    const value = String(input.value || input.placeholder || '').trim();
    const commandKind = this._titleCommandKind(value);
    const suggestions = this._titleCommandSuggestions(value, commandKind);
    panel.dataset.commandKind = commandKind;
    panel.innerHTML = '';
    this._titleCommandSuggestionItems = suggestions;
    this._titleCommandSuggestionIndex = 0;
    panel.dataset.activeSuggestionIndex = '0';
    panel.dataset.activeSuggestionKind = suggestions[0]?.kind || commandKind;
    const rect = input.getBoundingClientRect();
    panel.style.left = `${Math.round(rect.left)}px`;
    panel.style.top = `${Math.round(rect.bottom + 6)}px`;
    panel.style.width = `${Math.max(280, Math.round(rect.width))}px`;
    panel.appendChild(this._makeTitleCommandModeChips(commandKind));
    panel.appendChild(this._makeTitleCommandProfileChips(input));
    suggestions.forEach((suggestion, index) => {
      const item = document.createElement('button');
      item.type = 'button';
      item.className = 'wm-title-suggestion-item' + (index === 0 ? ' active previewed' : '');
      item.dataset.value = suggestion.value;
      item.dataset.commandKind = suggestion.kind;
      item.dataset.suggestionFeedback = index === 0 ? 'previewed' : 'idle';
      item.setAttribute('role', 'option');
      item.setAttribute('aria-selected', index === 0 ? 'true' : 'false');
      const label = document.createElement('span');
      label.className = 'wm-title-suggestion-label';
      label.textContent = suggestion.label;
      const meta = document.createElement('span');
      meta.className = 'wm-title-suggestion-meta';
      meta.textContent = suggestion.meta;
      item.appendChild(label);
      item.appendChild(meta);
      panel.appendChild(item);
    });
    this._syncTitleCommandSuggestionPreview(panel, Array.from(panel.querySelectorAll('.wm-title-suggestion-item')));
    panel.hidden = false;
  }

  _titleCommandModes() {
    return [
      { id: 'path', label: 'Open', prefix: '' },
      { id: 'url', label: 'URL', prefix: 'https://' },
      { id: 'search', label: 'Search', prefix: 'search ' },
      { id: 'command', label: 'Run', prefix: '>' }
    ];
  }

  _makeTitleCommandModeChips(activeKind) {
    const row = document.createElement('div');
    row.className = 'wm-title-command-modes';
    row.setAttribute('role', 'group');
    row.setAttribute('aria-label', 'Command modes');
    for (const mode of this._titleCommandModes()) {
      const chip = document.createElement('button');
      chip.type = 'button';
      chip.className = 'wm-title-command-mode' + (mode.id === activeKind ? ' active' : '');
      chip.dataset.commandKind = mode.id;
      chip.textContent = mode.label;
      chip.addEventListener('click', () => this._applyTitleCommandMode(mode));
      row.appendChild(chip);
    }
    return row;
  }

  _titleCommandProfiles() {
    return [
      { id: 'ide', label: 'IDE', value: 'src/app/ui.web/html.spl', meta: 'VS Code-like file command' },
      { id: 'browser', label: 'Browser', value: 'https://simple.local', meta: 'browser URL command' }
    ];
  }

  _makeTitleCommandProfileChips(input) {
    const row = document.createElement('div');
    row.className = 'wm-title-command-profiles';
    row.setAttribute('role', 'group');
    row.setAttribute('aria-label', 'Command profiles');
    const current = String(input?.placeholder || input?.value || '').toLowerCase();
    for (const profile of this._titleCommandProfiles()) {
      const chip = document.createElement('button');
      chip.type = 'button';
      chip.className = 'wm-title-command-profile' + (current.includes(profile.id) ? ' active' : '');
      chip.dataset.commandProfile = profile.id;
      chip.title = profile.meta;
      chip.textContent = profile.label;
      chip.addEventListener('click', () => this._applyTitleCommandProfile(profile));
      row.appendChild(chip);
    }
    return row;
  }

  _titleCommandSuggestions(value, kind) {
    const text = String(value || '').trim();
    const base = text || 'src/app';
    return [
      { label: base, meta: kind === 'empty' ? 'path' : kind, value: base, kind: kind === 'empty' ? 'path' : kind },
      { label: `Search workspace for ${base}`, meta: 'workspace search', value: `search ${base}`, kind: 'search' },
      { label: `Open ${base}`, meta: 'open path or URL', value: base, kind: this._titleCommandKind(base) },
      { label: `Run > ${base}`, meta: 'command action', value: `>${base}`, kind: 'command' }
    ];
  }

  _applyTitleCommandMode(mode) {
    const input = document.activeElement?.classList?.contains('wm-title-input') ? document.activeElement : this.desktop?.querySelector('.wm-window.focused .wm-title-input');
    if (!input || !mode) return false;
    const current = String(input.value || '').trim();
    if (mode.id === 'url' && !current.startsWith('http://') && !current.startsWith('https://')) input.value = mode.prefix + current;
    else if (mode.id === 'search' && !current.startsWith('search ')) input.value = mode.prefix + current;
    else if (mode.id === 'command' && !current.startsWith('>')) input.value = mode.prefix + current;
    this._showTitleCommandSuggestions(input, true);
    input.focus();
    return true;
  }

  _applyTitleCommandProfile(profile) {
    const input = document.activeElement?.classList?.contains('wm-title-input') ? document.activeElement : this.desktop?.querySelector('.wm-window.focused .wm-title-input');
    if (!input || !profile) return false;
    input.value = profile.value;
    input.placeholder = profile.label + ' command';
    this._showTitleCommandSuggestions(input, true);
    input.focus();
    return true;
  }

  _moveTitleCommandSuggestionSelection(delta) {
    const panel = this._titleCommandSuggestionsPanel;
    if (!panel || panel.hidden) return false;
    const items = Array.from(panel.querySelectorAll('.wm-title-suggestion-item'));
    if (items.length === 0) return false;
    this._titleCommandSuggestionIndex = (this._titleCommandSuggestionIndex + delta + items.length) % items.length;
    this._syncTitleCommandSuggestionPreview(panel, items);
    return true;
  }

  _syncTitleCommandSuggestionPreview(panel, items) {
    items.forEach((item, index) => {
      const active = index === this._titleCommandSuggestionIndex;
      item.classList.toggle('active', active);
      item.classList.toggle('previewed', active);
      if (!item.classList.contains('accepted')) item.dataset.suggestionFeedback = active ? 'previewed' : 'idle';
      item.setAttribute('aria-selected', active ? 'true' : 'false');
    });
    const active = items[this._titleCommandSuggestionIndex] || null;
    if (panel) {
      panel.dataset.activeSuggestionIndex = String(this._titleCommandSuggestionIndex);
      panel.dataset.activeSuggestionKind = active?.dataset?.commandKind || '';
      panel.dataset.activeSuggestionValue = active?.dataset?.value || '';
    }
  }

  _executeTitleCommandSuggestion() {
    const panel = this._titleCommandSuggestionsPanel;
    if (!panel || panel.hidden) return false;
    const active = panel.querySelector('.wm-title-suggestion-item.active');
    return this._applyTitleCommandSuggestion(active?.dataset.value || '');
  }

  _applyTitleCommandSuggestion(value) {
    const input = document.activeElement?.classList?.contains('wm-title-input') ? document.activeElement : this.desktop?.querySelector('.wm-window.focused .wm-title-input');
    if (!input) return false;
    const panel = this._titleCommandSuggestionsPanel;
    const active = panel && !panel.hidden ? panel.querySelector('.wm-title-suggestion-item.active') : null;
    const kind = active?.dataset?.commandKind || this._titleCommandKind(value);
    this._markTitleCommandSuggestionAccepted(active, input, kind, value);
    input.value = value;
    this._submitTitleCommandInput(input);
    return true;
  }

  _markTitleCommandSuggestionAccepted(item, input, kind, value) {
    if (this._titleCommandSuggestionFeedbackTimer) clearTimeout(this._titleCommandSuggestionFeedbackTimer);
    const winEl = input?.closest?.('.wm-window');
    const feedbackKind = String(kind || this._titleCommandKind(value || input?.value || '') || 'command');
    if (item) {
      item.classList.add('accepted');
      item.dataset.suggestionFeedback = 'accepted';
    }
    if (this._titleCommandSuggestionsPanel) this._titleCommandSuggestionsPanel.dataset.suggestionFeedback = 'accepted';
    if (input) {
      input.dataset.acceptedSuggestionKind = feedbackKind;
      input.dataset.acceptedSuggestionValue = String(value || '');
    }
    if (winEl) winEl.dataset.titleSuggestionFeedback = feedbackKind;
    this._titleCommandSuggestionFeedbackTimer = window.setTimeout(() => {
      if (item) {
        item.classList.remove('accepted');
        if (item.classList.contains('active')) item.dataset.suggestionFeedback = 'previewed';
      }
      if (this._titleCommandSuggestionsPanel?.dataset?.suggestionFeedback === 'accepted') delete this._titleCommandSuggestionsPanel.dataset.suggestionFeedback;
      if (input?.dataset?.acceptedSuggestionKind === feedbackKind) {
        delete input.dataset.acceptedSuggestionKind;
        delete input.dataset.acceptedSuggestionValue;
      }
      if (winEl?.dataset?.titleSuggestionFeedback === feedbackKind) delete winEl.dataset.titleSuggestionFeedback;
      this._titleCommandSuggestionFeedbackTimer = 0;
    }, 560);
  }

  _makeTitleInput(payload) {
    const input = document.createElement('input');
    input.className = 'wm-title-input wm-command-bar';
    input.type = 'text';
    input.value = payload.command || payload.command_text || payload.url || payload.path || payload.workspace || '';
    input.placeholder = payload.placeholder || payload.context || payload.appId || payload.app_id || 'Command';
    input.setAttribute('aria-label', 'Window command');
    input.addEventListener('pointerdown', (event) => event.stopPropagation());
    input.addEventListener('mousedown', (event) => event.stopPropagation());
    input.addEventListener('dblclick', (event) => event.stopPropagation());
    input.addEventListener('focus', () => this._showTitleCommandSuggestions(input, true));
    input.addEventListener('input', () => this._showTitleCommandSuggestions(input, true));
    input.addEventListener('blur', () => setTimeout(() => this._showTitleCommandSuggestions(input, false), 120));
    input.addEventListener('keydown', (event) => {
      if (event.key === 'Enter') {
        event.preventDefault();
        if (!this._executeTitleCommandSuggestion()) this._submitTitleCommandInput(input);
      }
      if (event.key === 'ArrowDown') {
        event.preventDefault();
        this._moveTitleCommandSuggestionSelection(1);
      }
      if (event.key === 'ArrowUp') {
        event.preventDefault();
        this._moveTitleCommandSuggestionSelection(-1);
      }
      if (event.key === 'Escape') {
        event.preventDefault();
        this._showTitleCommandSuggestions(input, false);
      }
    });
    return input;
  }

  _electronCloseWindow(windowId) {
    const key = String(windowId || '');
    const entry = this._electronWindows.get(key);
    if (!entry) return;
    this._animateRemoveWindow(entry.winEl);
    this._electronWindows.delete(key);
    if (this._electronActiveWindowId === key) {
      this._electronActiveWindowId = '';
    }
    this._renderElectronTaskbar();
  }

  _electronMoveWindow(windowId, x, y) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    if (x != null) entry.winEl.style.left = `${Number(x) || 0}px`;
    if (y != null) entry.winEl.style.top = `${Number(y) || 0}px`;
  }

  _electronResizeWindow(windowId, width, height) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    if (width != null) entry.winEl.style.width = `${Number(width) || 1}px`;
    if (height != null) entry.winEl.style.height = `${Number(height) || 1}px`;
  }

  _electronFocusWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    for (const item of this._electronWindows.values()) item.winEl.classList.remove('focused');
    entry.winEl.classList.add('focused');
    this._markWindowFocusAcquired(entry.winEl);
    entry.winEl.classList.remove('minimized', 'minimizing');
    this._clearWindowMinimizeTarget(entry.winEl);
    entry.winEl.style.display = '';
    if (entry.minimized) this._markWindowLifecycle(entry.winEl, 'restoring');
    entry.winEl.style.zIndex = String(++this._electronZCounter);
    entry.minimized = false;
    this._electronActiveWindowId = String(windowId || '');
    this._renderElectronTaskbar();
  }

  _electronMinimizeWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    entry.minimized = true;
    this._setWindowMinimizeTarget(entry.winEl, windowId);
    this._markWindowLifecycle(entry.winEl, 'minimizing');
    setTimeout(() => {
      if (entry.minimized) {
        entry.winEl.classList.remove('minimizing');
        entry.winEl.classList.add('minimized');
        entry.winEl.style.display = 'none';
      }
    }, WM_EXIT_ANIMATION_MS);
    if (this._electronActiveWindowId === String(windowId || '')) {
      this._electronActiveWindowId = '';
    }
    this._renderElectronTaskbar();
  }

  _electronMaximizeWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    if (!entry.restoreBounds) {
      entry.restoreBounds = {
        left: entry.winEl.style.left,
        top: entry.winEl.style.top,
        width: entry.winEl.style.width,
        height: entry.winEl.style.height
      };
    }
    entry.winEl.style.left = '0px';
    entry.winEl.style.top = '0px';
    entry.winEl.style.width = '100%';
    entry.winEl.style.height = '100%';
    this._electronFocusWindow(windowId);
  }

  _electronUnmaximizeWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry || !entry.restoreBounds) return;
    entry.winEl.style.left = entry.restoreBounds.left;
    entry.winEl.style.top = entry.restoreBounds.top;
    entry.winEl.style.width = entry.restoreBounds.width;
    entry.winEl.style.height = entry.restoreBounds.height;
    entry.restoreBounds = null;
    this._electronFocusWindow(windowId);
  }

  _electronSetWindowTitle(windowId, title) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    entry.titleText = title || String(windowId || '');
    entry.title.textContent = entry.titleText;
    this._renderElectronTaskbar();
  }

  _animateRemoveWindow(winEl) {
    if (!winEl) return;
    winEl.classList.remove('opening', 'restoring', 'minimizing');
    winEl.classList.add('closing');
    setTimeout(() => winEl.remove(), WM_EXIT_ANIMATION_MS);
  }

  _markWindowLifecycle(winEl, className) {
    if (!winEl) return;
    winEl.classList.remove('opening', 'restoring', 'closing', 'minimizing', 'minimized');
    winEl.classList.add(className);
    setTimeout(() => winEl.classList.remove(className), WM_EXIT_ANIMATION_MS + 80);
  }

  _markWindowFocusAcquired(winEl) {
    if (!winEl) return;
    const prior = this._focusAcquiredTimers.get(winEl);
    if (prior) window.clearTimeout(prior);
    winEl.classList.remove('focus-acquired');
    // Restart the CSS keyframe even when focus returns to the same window.
    void winEl.offsetWidth;
    winEl.classList.add('focus-acquired');
    winEl.dataset.focusTransition = 'acquired';
    const timer = window.setTimeout(() => {
      winEl.classList.remove('focus-acquired');
      delete winEl.dataset.focusTransition;
      this._focusAcquiredTimers.delete(winEl);
    }, 420);
    this._focusAcquiredTimers.set(winEl, timer);
  }

  _markTrafficCommandFeedback(button, action = '') {
    if (!button) return;
    const prior = this._trafficCommandTimers.get(button);
    if (prior) window.clearTimeout(prior);
    const command = String(action || button.dataset.action || 'window').trim() || 'window';
    const winEl = button.closest('.wm-window');
    button.classList.remove('commanding');
    void button.offsetWidth;
    button.classList.add('commanding');
    button.dataset.windowCommandFeedback = command;
    if (winEl) winEl.dataset.windowCommandFeedback = command;
    const timer = window.setTimeout(() => {
      button.classList.remove('commanding');
      delete button.dataset.windowCommandFeedback;
      if (winEl && winEl.dataset.windowCommandFeedback === command) delete winEl.dataset.windowCommandFeedback;
      this._trafficCommandTimers.delete(button);
    }, 320);
    this._trafficCommandTimers.set(button, timer);
  }

  _setWindowMinimizeTarget(winEl, windowId) {
    if (!winEl) return;
    const id = String(windowId || winEl.dataset.surfaceId || winEl.dataset.canonicalId || '').trim();
    const taskbarItem = id && this.taskbar
      ? this.taskbar.querySelector(`.wm-taskbar-item[data-window-id-hint="${CSS.escape(id)}"]`)
      : null;
    const winRect = winEl.getBoundingClientRect();
    const targetRect = taskbarItem
      ? taskbarItem.getBoundingClientRect()
      : (this.taskbar ? this.taskbar.getBoundingClientRect() : null);
    if (!targetRect || !winRect.width || !winRect.height) {
      this._clearWindowMinimizeTarget(winEl);
      return;
    }
    const deltaX = Math.round((targetRect.left + targetRect.width / 2) - (winRect.left + winRect.width / 2));
    const deltaY = Math.round((targetRect.top + targetRect.height / 2) - (winRect.top + winRect.height));
    winEl.style.setProperty('--wm-minimize-target-x', `${deltaX}px`);
    winEl.style.setProperty('--wm-minimize-target-y', `${deltaY}px`);
    winEl.dataset.minimizeTarget = taskbarItem ? 'dock-item' : 'dock';
  }

  _clearWindowMinimizeTarget(winEl) {
    if (!winEl) return;
    winEl.style.removeProperty('--wm-minimize-target-x');
    winEl.style.removeProperty('--wm-minimize-target-y');
    delete winEl.dataset.minimizeTarget;
  }

  _renderElectronTaskbar() {
    if (!this.taskbar) return;
    if (this._electronWindows.size === 0) {
      this.taskbar.innerHTML = '';
      return;
    }
    const running = [];
    for (const [windowId, entry] of this._electronWindows.entries()) {
      running.push({
        window_id: windowId,
        title: entry.titleText || windowId,
        minimized: !!entry.minimized,
        active: windowId === this._electronActiveWindowId
      });
    }
    this.renderTaskbarModel({ pinned: [], running, tray: [] });
  }

  // -------------------------------------------------------------------------
  // Ack timer
  // -------------------------------------------------------------------------

  _startAckTimer() {
    if (this._ackTimer) return;
    this._ackTimer = setInterval(() => {
      if (!this.renderer) return;
      const seq = this.renderer.lastSequence;
      if (seq >= 0) {
        this._send({
          t: 'ack', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
          payload: { last_applied_sequence: seq }
        });
      }
    }, ACK_INTERVAL_MS);
  }

  _stopAckTimer() {
    if (this._ackTimer) { clearInterval(this._ackTimer); this._ackTimer = null; }
  }

  // -------------------------------------------------------------------------
  // Ghost overlay (optimistic drag/resize)
  // -------------------------------------------------------------------------

  _createGhost(winEl) {
    const ghost = document.createElement('div');
    ghost.className = 'wm-ghost drag-lifted';
    ghost.dataset.dragFeedback = 'lifted';
    ghost.setAttribute('aria-hidden', 'true');
    const r = winEl.getBoundingClientRect();
    const dr = this.desktop.getBoundingClientRect();
    ghost.style.cssText = `
      position:absolute;
      left:${r.left - dr.left}px;top:${r.top - dr.top}px;
      width:${r.width}px;height:${r.height}px;
      pointer-events:none;box-sizing:border-box;z-index:99999;
    `;
    this.desktop.appendChild(ghost);
    return ghost;
  }

  _setDragFeedback(winEl, ghostEl, active) {
    if (!this.desktop) return;
    this.desktop.dataset.wmDragState = active ? 'active' : 'idle';
    if (winEl) winEl.classList.toggle('dragging', !!active);
    if (ghostEl) ghostEl.classList.toggle('drag-lifted', !!active);
  }

  _clearDragFeedback() {
    if (this.desktop) {
      this.desktop.dataset.wmDragState = 'idle';
      this.desktop.dataset.wmSnapTarget = 'none';
    }
    if (this.dragState?.winEl) this.dragState.winEl.classList.remove('dragging');
    if (this.dragState?.ghostEl) this.dragState.ghostEl.classList.remove('drag-lifted');
  }

  _cancelGhost() {
    if (this.dragState && this.dragState.ghostEl) {
      this.dragState.ghostEl.remove();
      clearTimeout(this.dragState.timer);
      this.dragState = null;
    }
    if (this.resizeState && this.resizeState.ghostEl) {
      if (this.resizeState.winEl) {
        this.resizeState.winEl.dataset.resizeActive = 'false';
        delete this.resizeState.winEl.dataset.resizeDirection;
      }
      this.resizeState.ghostEl.remove();
      clearTimeout(this.resizeState.timer);
      this.resizeState = null;
    }
    this._clearDragFeedback();
    this._clearSnapPreview();
  }

  _ensureSnapPreview() {
    if (this._snapPreview && this._snapPreview.isConnected) return this._snapPreview;
    if (!this.desktop) return null;
    const preview = document.createElement('div');
    preview.className = 'wm-snap-preview';
    preview.setAttribute('aria-hidden', 'true');
    this.desktop.appendChild(preview);
    this._snapPreview = preview;
    return preview;
  }

  _detectSnapZone(e) {
    if (!this.desktop) return '';
    const r = this.desktop.getBoundingClientRect();
    const x = e.clientX - r.left;
    const y = e.clientY - r.top;
    const threshold = 34;
    if (y <= threshold) return 'full';
    if (x <= threshold) return 'left';
    if (x >= r.width - threshold) return 'right';
    return '';
  }

  _snapRectForZone(zone) {
    if (!this.desktop || !zone) return null;
    const r = this.desktop.getBoundingClientRect();
    const gap = 10;
    const taskbarReserve = 68;
    const height = Math.max(240, Math.round(r.height - taskbarReserve - gap * 2));
    const halfWidth = Math.max(300, Math.round((r.width - gap * 3) / 2));
    if (zone === 'left') return { x: gap, y: gap, w: halfWidth, h: height };
    if (zone === 'right') return { x: Math.round(r.width - halfWidth - gap), y: gap, w: halfWidth, h: height };
    if (zone === 'full') return { x: gap, y: gap, w: Math.max(420, Math.round(r.width - gap * 2)), h: height };
    return null;
  }

  _applySnapPreview(zone) {
    const preview = this._ensureSnapPreview();
    const rect = this._snapRectForZone(zone);
    if (!preview || !rect) {
      this._clearSnapPreview();
      return;
    }
    preview.dataset.snapZone = zone;
    if (this.desktop) this.desktop.dataset.wmSnapTarget = zone;
    preview.style.left = `${rect.x}px`;
    preview.style.top = `${rect.y}px`;
    preview.style.width = `${rect.w}px`;
    preview.style.height = `${rect.h}px`;
    preview.classList.add('active');
    this._lastSnapZone = zone;
  }

  _clearSnapPreview() {
    if (this._snapPreview) {
      this._snapPreview.classList.remove('active');
      this._snapPreview.dataset.snapZone = '';
    }
    if (this.desktop) this.desktop.dataset.wmSnapTarget = 'none';
    this._lastSnapZone = '';
  }

  _windowElementById(windowId) {
    const key = String(windowId || '');
    if (!key) return null;
    if (this.transport === 'electron-ipc' && this._electronWindows.has(key)) {
      return this._electronWindows.get(key)?.winEl || null;
    }
    if (!this.desktop) return null;
    const escaped = key.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
    return this.desktop.querySelector(`.wm-window[data-surface-id="${escaped}"], .wm-window[data-canonical-id="${escaped}"]`);
  }

  _markSnapCommitted(winEl, zone) {
    if (!winEl || !zone) return;
    if (winEl._wmSnapCommitTimer) window.clearTimeout(winEl._wmSnapCommitTimer);
    winEl.dataset.snapCommitZone = zone;
    winEl.classList.remove('snap-committed');
    void winEl.offsetWidth;
    winEl.classList.add('snap-committed');
    winEl._wmSnapCommitTimer = window.setTimeout(() => {
      winEl.classList.remove('snap-committed');
      winEl.dataset.snapCommitZone = '';
      winEl._wmSnapCommitTimer = 0;
    }, WM_SNAP_COMMIT_MS);
  }

  _ensureSnapLayoutPalette() {
    if (this._snapLayoutPalette && this._snapLayoutPalette.isConnected) return this._snapLayoutPalette;
    const panel = document.createElement('aside');
    panel.id = 'wm-snap-layout-palette';
    panel.className = 'wm-snap-layout-palette';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Snap layout chooser');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const choice = event.target.closest('[data-snap-layout]');
      if (!choice || !panel.contains(choice)) return;
      this._applySnapLayoutChoice(panel.dataset.windowIdHint || '', choice.dataset.snapLayout || '');
    });
    document.body.appendChild(panel);
    this._snapLayoutPalette = panel;
    return panel;
  }

  _toggleSnapLayoutPalette(winEl, anchorEl, open = null) {
    const panel = this._ensureSnapLayoutPalette();
    const shouldOpen = open == null ? panel.hidden : open;
    if (!shouldOpen) {
      panel.hidden = true;
      this._clearSnapPreview();
      return false;
    }
    this._renderSnapLayoutPalette(winEl, anchorEl);
    panel.hidden = false;
    return true;
  }

  _renderSnapLayoutPalette(winEl, anchorEl) {
    const panel = this._ensureSnapLayoutPalette();
    const surfaceId = winEl?.dataset?.surfaceId || '';
    panel.dataset.windowIdHint = surfaceId;
    panel.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-snap-layout-title';
    title.textContent = 'Snap layouts';
    panel.appendChild(title);
    const grid = document.createElement('div');
    grid.className = 'wm-snap-layout-grid';
    for (const layout of this._snapLayoutItems()) grid.appendChild(this._makeSnapLayoutChoice(layout));
    panel.appendChild(grid);
    const rect = anchorEl?.getBoundingClientRect?.() || winEl?.getBoundingClientRect?.();
    if (rect) {
      panel.style.left = Math.max(12, Math.round(rect.left - 18)) + 'px';
      panel.style.top = Math.max(44, Math.round(rect.bottom + 10)) + 'px';
    }
  }

  _snapLayoutItems() {
    return [
      { id: 'left', label: 'Left half', meta: 'Split left' },
      { id: 'right', label: 'Right half', meta: 'Split right' },
      { id: 'full', label: 'Fullscreen', meta: 'Fill workspace' }
    ];
  }

  _makeSnapLayoutChoice(layout) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-snap-layout-choice';
    button.dataset.snapLayout = layout.id;
    button.appendChild(this._makeSnapLayoutPreview(layout.id));
    const body = document.createElement('span');
    body.className = 'wm-snap-layout-body';
    const label = document.createElement('strong');
    label.className = 'wm-snap-layout-label';
    label.textContent = layout.label;
    body.appendChild(label);
    const meta = document.createElement('span');
    meta.className = 'wm-snap-layout-meta';
    meta.textContent = layout.meta;
    body.appendChild(meta);
    button.appendChild(body);
    button.addEventListener('pointerenter', () => this._applySnapPreview(layout.id));
    button.addEventListener('focus', () => this._applySnapPreview(layout.id));
    return button;
  }

  _makeSnapLayoutPreview(zone) {
    const preview = document.createElement('span');
    preview.className = 'wm-snap-layout-preview';
    preview.dataset.snapPreview = zone;
    for (const part of ['a', 'b']) {
      const cell = document.createElement('span');
      cell.className = 'wm-snap-layout-cell ' + part;
      preview.appendChild(cell);
    }
    return preview;
  }

  _applySnapLayoutChoice(windowId, zone) {
    const rect = this._snapRectForZone(zone);
    if (!windowId || !rect) return;
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(windowId);
    if (isElectronWindow) {
      this._electronMoveWindow(windowId, rect.x, rect.y);
      this._electronResizeWindow(windowId, rect.w, rect.h);
    }
    this._markSnapCommitted(this._windowElementById(windowId), zone);
    const source = isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {};
    this._sendWindowCmd('focus', { window_id_hint: windowId, ...source });
    this._sendWindowCmd('move', { window_id_hint: windowId, ...source, x: rect.x, y: rect.y, snap_zone: zone });
    this._sendWindowCmd('resize', { window_id_hint: windowId, ...source, w: rect.w, h: rect.h, snap_zone: zone });
    this._showSystemHud('Snap layout', zone, 1500);
    this._toggleSnapLayoutPalette(null, null, false);
  }

  _ensureWindowArrangePalette() {
    if (this._windowArrangePalette && this._windowArrangePalette.isConnected) return this._windowArrangePalette;
    const panel = document.createElement('aside');
    panel.id = 'wm-window-arrange-palette';
    panel.className = 'wm-window-arrange-palette';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Window arrangement');
    panel.addEventListener('pointerdown', (event) => event.stopPropagation());
    panel.addEventListener('mousedown', (event) => event.stopPropagation());
    panel.addEventListener('click', (event) => {
      const choice = event.target.closest('[data-arrange-mode]');
      if (!choice || !panel.contains(choice)) return;
      this._applyWindowArrangement(choice.dataset.arrangeMode || '');
    });
    document.body.appendChild(panel);
    this._windowArrangePalette = panel;
    return panel;
  }

  _toggleWindowArrangePalette(open = null) {
    const panel = this._ensureWindowArrangePalette();
    const shouldOpen = open == null ? panel.hidden : open;
    panel.hidden = !shouldOpen;
    if (shouldOpen) this._renderWindowArrangePalette();
    return shouldOpen;
  }

  _renderWindowArrangePalette() {
    const panel = this._ensureWindowArrangePalette();
    panel.innerHTML = '';
    const title = document.createElement('div');
    title.className = 'wm-arrange-title';
    title.textContent = 'Arrange windows';
    panel.appendChild(title);
    const grid = document.createElement('div');
    grid.className = 'wm-arrange-grid';
    for (const mode of this._arrangeModes()) grid.appendChild(this._makeArrangeModeButton(mode));
    panel.appendChild(grid);
  }

  _arrangeModes() {
    return [
      { id: 'tile_grid', label: 'Tile grid', meta: 'Fit visible windows' },
      { id: 'cascade', label: 'Cascade', meta: 'Stack with offsets' },
      { id: 'focus_left', label: 'Focus left', meta: 'Active plus rail' },
      { id: 'center_stage', label: 'Center stage', meta: 'Front and centered' }
    ];
  }

  _makeArrangeModeButton(mode) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-arrange-mode';
    button.dataset.arrangeMode = mode.id;
    button.appendChild(this._makeArrangePreview(mode.id));
    const body = document.createElement('span');
    body.className = 'wm-arrange-body';
    const label = document.createElement('strong');
    label.className = 'wm-arrange-label';
    label.textContent = mode.label;
    body.appendChild(label);
    const meta = document.createElement('span');
    meta.className = 'wm-arrange-meta';
    meta.textContent = mode.meta;
    body.appendChild(meta);
    button.appendChild(body);
    return button;
  }

  _makeArrangePreview(modeId) {
    const preview = document.createElement('span');
    preview.className = 'wm-arrange-preview';
    preview.dataset.arrangePreview = modeId;
    for (const part of ['a', 'b', 'c']) {
      const cell = document.createElement('span');
      cell.className = 'wm-arrange-cell ' + part;
      preview.appendChild(cell);
    }
    return preview;
  }

  _arrangeVisibleWindows() {
    const items = [];
    if (this.transport === 'electron-ipc' && this._electronWindows.size) {
      for (const [windowId, entry] of this._electronWindows.entries()) {
        if (!entry.minimized && entry.winEl?.isConnected) items.push({ id: windowId, el: entry.winEl, active: windowId === this._electronActiveWindowId });
      }
      return items;
    }
    if (!this.desktop) return items;
    for (const win of this.desktop.querySelectorAll('.wm-window')) {
      const id = win.dataset.surfaceId || win.dataset.canonicalId || '';
      if (!id || win.classList.contains('minimized') || win.hidden) continue;
      items.push({ id, el: win, active: win.classList.contains('focused') });
    }
    return items;
  }

  _workspaceArrangeBounds() {
    const rect = this.desktop?.getBoundingClientRect?.();
    const width = Math.max(320, Math.round(rect?.width || window.innerWidth || 1024));
    const height = Math.max(240, Math.round(rect?.height || window.innerHeight || 768));
    return { x: 18, y: 58, w: Math.max(300, width - 36), h: Math.max(220, height - 140) };
  }

  _arrangeRectForIndex(index, count, modeId, bounds) {
    const gap = 14;
    if (modeId === 'cascade') {
      const w = Math.round(bounds.w * 0.62);
      const h = Math.round(bounds.h * 0.68);
      return { x: bounds.x + index * 34, y: bounds.y + index * 30, w, h };
    }
    if (modeId === 'focus_left') {
      if (index === 0) return { x: bounds.x, y: bounds.y, w: Math.round(bounds.w * 0.64), h: bounds.h };
      const railW = Math.max(220, Math.round(bounds.w * 0.28));
      const railH = Math.max(130, Math.floor((bounds.h - gap * (count - 2)) / Math.max(1, count - 1)));
      return { x: bounds.x + bounds.w - railW, y: bounds.y + (index - 1) * (railH + gap), w: railW, h: railH };
    }
    if (modeId === 'center_stage') {
      if (index === 0) return { x: bounds.x + Math.round(bounds.w * 0.14), y: bounds.y + Math.round(bounds.h * 0.08), w: Math.round(bounds.w * 0.72), h: Math.round(bounds.h * 0.78) };
      return { x: bounds.x + bounds.w - 190, y: bounds.y + 24 + (index - 1) * 74, w: 170, h: 120 };
    }
    const cols = Math.ceil(Math.sqrt(Math.max(1, count)));
    const rows = Math.ceil(Math.max(1, count) / cols);
    const col = index % cols;
    const row = Math.floor(index / cols);
    const w = Math.floor((bounds.w - gap * (cols - 1)) / cols);
    const h = Math.floor((bounds.h - gap * (rows - 1)) / rows);
    return { x: bounds.x + col * (w + gap), y: bounds.y + row * (h + gap), w, h };
  }

  _applyWindowArrangement(modeId) {
    const windows = this._arrangeVisibleWindows().sort((a, b) => Number(b.active) - Number(a.active));
    if (!windows.length) {
      this._showSystemHud('Arrange windows', 'no windows', 1500);
      this._toggleWindowArrangePalette(false);
      return;
    }
    const mode = this._arrangeModes().find((item) => item.id === modeId) || this._arrangeModes()[0];
    const bounds = this._workspaceArrangeBounds();
    this._sendWindowCmd('arrange_windows', { arrange_mode: mode.id, window_count: windows.length });
    windows.forEach((win, index) => {
      const rect = this._arrangeRectForIndex(index, windows.length, mode.id, bounds);
      const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(win.id);
      if (isElectronWindow) {
        this._electronMoveWindow(win.id, rect.x, rect.y);
        this._electronResizeWindow(win.id, rect.w, rect.h);
      }
      const source = isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {};
      this._sendWindowCmd('move', { window_id_hint: win.id, ...source, x: rect.x, y: rect.y, arrange_mode: mode.id });
      this._sendWindowCmd('resize', { window_id_hint: win.id, ...source, w: rect.w, h: rect.h, arrange_mode: mode.id });
    });
    this._showSystemHud('Arrange windows', mode.label, 1500);
    this._toggleWindowArrangePalette(false);
  }

  _ensureWindowContextMenu() {
    if (this._windowContextMenu && this._windowContextMenu.isConnected) return this._windowContextMenu;
    const menu = document.createElement('aside');
    menu.className = 'wm-window-context-menu';
    menu.hidden = true;
    menu.setAttribute('role', 'menu');
    menu.setAttribute('aria-label', 'Window context menu');
    menu.addEventListener('pointerdown', (event) => event.stopPropagation());
    menu.addEventListener('mousedown', (event) => event.stopPropagation());
    menu.addEventListener('click', (event) => {
      const item = event.target.closest('[data-context-action]');
      if (!item || !menu.contains(item)) return;
      this._activateWindowContextAction(item.dataset.contextAction || '', menu.dataset.windowIdHint || '', item.dataset.contextWorkspaceId || '');
    });
    menu.addEventListener('keydown', (event) => this._handleWindowContextMenuKeydown(event));
    document.body.appendChild(menu);
    this._windowContextMenu = menu;
    return menu;
  }

  _showWindowContextMenu(winEl, event) {
    const menu = this._ensureWindowContextMenu();
    this._renderWindowContextMenu(winEl);
    const width = 280;
    const left = Math.max(12, Math.min(Math.round(event.clientX), window.innerWidth - width - 12));
    const top = Math.max(44, Math.min(Math.round(event.clientY), window.innerHeight - 320));
    menu.style.left = `${left}px`;
    menu.style.top = `${top}px`;
    menu.hidden = false;
    const first = menu.querySelector('.wm-window-context-item.active') || menu.querySelector('.wm-window-context-item');
    if (first) first.focus({ preventScroll: true });
  }

  _hideWindowContextMenu() {
    if (!this._windowContextMenu) return;
    this._windowContextMenu.hidden = true;
    this._windowContextMenuWindowId = '';
  }

  _renderWindowContextMenu(winEl) {
    const menu = this._ensureWindowContextMenu();
    const windowId = winEl?.dataset?.surfaceId || winEl?.dataset?.canonicalId || '';
    const titleText = winEl?.querySelector?.('.wm-title')?.textContent || winEl?.dataset?.title || windowId || 'Window';
    this._windowContextMenuWindowId = windowId;
    menu.dataset.windowIdHint = windowId;
    menu.dataset.windowTitle = titleText;
    menu.innerHTML = '';
    menu.appendChild(this._makeWindowContextHeader(winEl, titleText, windowId));
    for (const group of this._windowContextMenuGroups()) {
      const section = document.createElement('div');
      section.className = 'wm-window-context-group';
      section.setAttribute('role', 'group');
      section.setAttribute('aria-label', group.label);
      for (const item of group.items) section.appendChild(this._makeWindowContextItem(item));
      menu.appendChild(section);
    }
  }

  _makeWindowContextHeader(winEl, titleText, windowId) {
    const header = document.createElement('div');
    header.className = 'wm-window-context-header';
    header.appendChild(this._makeRoundIcon('wm-window-context-icon', titleText || windowId || 'W'));
    const body = document.createElement('span');
    body.className = 'wm-window-context-heading';
    const title = document.createElement('span');
    title.className = 'wm-window-context-title';
    title.textContent = titleText;
    body.appendChild(title);
    const status = document.createElement('span');
    status.className = 'wm-window-context-status';
    status.textContent = winEl?.classList?.contains('focused') || winEl?.dataset?.windowFocus === 'focused' ? 'Active window' : 'Background window';
    body.appendChild(status);
    header.appendChild(body);
    return header;
  }

  _windowContextMenuGroups() {
    return [
      {
        label: 'Window actions',
        items: [
          { action: 'focus', label: 'Focus window', shortcut: 'Enter', active: true },
          { action: 'minimize', label: 'Minimize', shortcut: 'M', glyph: '-' },
          { action: 'pin_stage', label: 'Pin to Stage', shortcut: 'P', glyph: '+' }
        ]
      },
      {
        label: 'Layout actions',
        items: [
          { action: 'snap_left', label: 'Snap left', shortcut: 'Left', glyph: '<' },
          { action: 'snap_right', label: 'Snap right', shortcut: 'Right', glyph: '>' },
          { action: 'snap_full', label: 'Fill workspace', shortcut: 'Up', glyph: '^' }
        ]
      },
      {
        label: 'Move to workspace',
        items: this._workspaceItems().map((workspace) => ({
          action: 'move_workspace',
          label: 'Move to ' + workspace.label,
          shortcut: workspace.label.slice(0, 1).toUpperCase(),
          workspaceId: workspace.id,
          glyph: workspace.label.slice(0, 1).toUpperCase()
        }))
      },
      {
        label: 'Utility actions',
        items: [
          { action: 'copy_title', label: 'Copy title', shortcut: 'C', glyph: '=' },
          { action: 'close', label: 'Close', shortcut: 'Esc', glyph: 'x' }
        ]
      }
    ];
  }

  _makeWindowContextItem(item) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'wm-window-context-item' + (item.active ? ' active' : '');
    button.dataset.contextAction = item.action;
    if (item.workspaceId) button.dataset.contextWorkspaceId = item.workspaceId;
    button.setAttribute('role', 'menuitem');
    const glyph = document.createElement('span');
    glyph.className = 'wm-window-context-glyph wm-round-icon';
    glyph.textContent = item.glyph || item.label.slice(0, 1).toUpperCase();
    button.appendChild(glyph);
    const label = document.createElement('span');
    label.className = 'wm-window-context-label';
    label.textContent = item.label;
    button.appendChild(label);
    const shortcut = document.createElement('span');
    shortcut.className = 'wm-window-context-shortcut';
    shortcut.textContent = item.shortcut;
    button.appendChild(shortcut);
    return button;
  }

  _handleWindowContextMenuKeydown(event) {
    if (!this._windowContextMenu || this._windowContextMenu.hidden) return;
    if (event.key === 'Escape') {
      event.preventDefault();
      this._hideWindowContextMenu();
      return;
    }
    if (event.key === 'ArrowDown' || event.key === 'ArrowUp') {
      event.preventDefault();
      this._moveWindowContextMenuSelection(event.key === 'ArrowDown' ? 1 : -1);
      return;
    }
    if (event.key === 'Home' || event.key === 'End') {
      event.preventDefault();
      this._focusWindowContextMenuItem(event.key === 'Home' ? 0 : -1);
      return;
    }
    if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      const item = document.activeElement?.closest?.('[data-context-action]');
      if (!item || !this._windowContextMenu.contains(item)) return;
      this._activateWindowContextAction(item.dataset.contextAction || '', this._windowContextMenu.dataset.windowIdHint || '', item.dataset.contextWorkspaceId || '');
    }
  }

  _moveWindowContextMenuSelection(delta) {
    const items = Array.from(this._windowContextMenu?.querySelectorAll('.wm-window-context-item') || []);
    if (!items.length) return;
    const current = items.indexOf(document.activeElement);
    const next = current < 0 ? 0 : (current + delta + items.length) % items.length;
    items[next].focus({ preventScroll: true });
  }

  _focusWindowContextMenuItem(index) {
    const items = Array.from(this._windowContextMenu?.querySelectorAll('.wm-window-context-item') || []);
    if (!items.length) return;
    const next = index < 0 ? items.length - 1 : Math.min(index, items.length - 1);
    items[next].focus({ preventScroll: true });
  }

  _activateWindowContextAction(action, windowId, workspaceId = '') {
    if (!action || !windowId) return;
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(windowId);
    const source = isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {};
    if (action === 'focus') {
      if (isElectronWindow) this._electronFocusWindow(windowId);
      this._sendWindowCmd('focus', { window_id_hint: windowId, ...source });
    } else if (action === 'minimize') {
      if (isElectronWindow) this._electronMinimizeWindow(windowId);
      this._sendWindowCmd('minimize', { window_id_hint: windowId, ...source });
    } else if (action === 'close') {
      if (isElectronWindow) this._electronCloseWindow(windowId);
      this._sendWindowCmd('close', { window_id_hint: windowId, ...source });
    } else if (action === 'snap_left') {
      this._applySnapLayoutChoice(windowId, 'left');
    } else if (action === 'snap_right') {
      this._applySnapLayoutChoice(windowId, 'right');
    } else if (action === 'snap_full') {
      this._applySnapLayoutChoice(windowId, 'full');
    } else if (action === 'pin_stage') {
      this._sendWindowCmd('stage_pin', { window_id_hint: windowId });
      this._showSystemHud('Stage', 'pinned', 1400);
    } else if (action === 'move_workspace') {
      const targetWorkspace = workspaceId || this._activeWorkspaceId;
      const workspace = this._workspaceItems().find((item) => item.id === targetWorkspace);
      this._sendWindowCmd('window_move_workspace', { window_id_hint: windowId, workspace_id: targetWorkspace });
      this._showSystemHud('Move window', workspace?.label || targetWorkspace, 1400);
    } else if (action === 'copy_title') {
      const title = this._windowContextMenu?.dataset?.windowTitle || windowId;
      if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(title).catch(() => {});
      this._sendWindowCmd('window_copy_title', { window_id_hint: windowId, title });
      this._showSystemHud('Copied', title, 1400);
    }
    this._hideWindowContextMenu();
  }

  // -------------------------------------------------------------------------
  // Input / drag
  // -------------------------------------------------------------------------

  _onTitlebarMousedown(e, winEl) {
    if (e.target.closest('.wm-traffic-lights')) return;
    const surfaceId = winEl.dataset.surfaceId ?? '';
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId);
    if (isElectronWindow) {
      this._electronFocusWindow(surfaceId);
    }
    // Bring to front request (server decides z-order).
    this._sendWindowCmd('focus', {
      window_id_hint: surfaceId,
      ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
    });

    const ghost = isElectronWindow ? null : this._createGhost(winEl);
    this._setDragFeedback(winEl, ghost, true);
    this.dragState = {
      surfaceId, ghostEl: ghost, timer: null, isElectronWindow,
      startX: e.clientX, startY: e.clientY,
      origLeft: parseFloat(winEl.style.left || 0),
      origTop:  parseFloat(winEl.style.top  || 0),
      winEl
    };
    e.preventDefault();
  }

  _onResizeMousedown(e, winEl, direction) {
    const surfaceId = winEl.dataset.surfaceId ?? '';
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId);
    if (isElectronWindow) {
      this._electronFocusWindow(surfaceId);
    }
    this._sendWindowCmd('focus', {
      window_id_hint: surfaceId,
      ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
    });

    const ghost = isElectronWindow ? null : this._createGhost(winEl);
    const r = winEl.getBoundingClientRect();
    winEl.dataset.resizeActive = 'true';
    winEl.dataset.resizeDirection = String(direction || '');
    if (ghost) {
      ghost.dataset.resizeFeedback = 'directional';
      ghost.dataset.resizeDirection = String(direction || '');
      ghost.classList.add('resize-active');
    }
    this.resizeState = {
      surfaceId, ghostEl: ghost, timer: null, direction, isElectronWindow,
      startX: e.clientX, startY: e.clientY,
      origW: r.width, origH: r.height,
      winEl
    };
    this._showResizeHud(r.width, r.height, direction);
    e.preventDefault();
  }

  _onMousemove(e) {
    if (this.dragState) {
      const ds = this.dragState;
      const dx = e.clientX - ds.startX;
      const dy = e.clientY - ds.startY;
      const nextX = ds.origLeft + dx;
      const nextY = ds.origTop + dy;
      const snapZone = this._detectSnapZone(e);
      if (snapZone) this._applySnapPreview(snapZone);
      else this._clearSnapPreview();
      if (ds.ghostEl) ds.ghostEl.dataset.snapZone = snapZone || 'free';
      if (ds.isElectronWindow) {
        this._electronMoveWindow(ds.surfaceId, Math.round(nextX), Math.round(nextY));
      } else if (ds.ghostEl) {
        if (ds.winEl) {
          ds.winEl.style.left = nextX + 'px';
          ds.winEl.style.top = nextY + 'px';
        }
        ds.ghostEl.style.left = nextX + 'px';
        ds.ghostEl.style.top  = nextY + 'px';
      }
    }
    if (this.resizeState) {
      const rs = this.resizeState;
      const dx = e.clientX - rs.startX;
      const dy = e.clientY - rs.startY;
      const dir = rs.direction;
      const minW = 200, minH = 120;
      let w = rs.origW, h = rs.origH;
      if (dir.includes('e')) w = Math.max(minW, rs.origW + dx);
      if (dir.includes('s')) h = Math.max(minH, rs.origH + dy);
      if (dir.includes('w')) w = Math.max(minW, rs.origW - dx);
      if (dir === 'n' || dir.includes('n')) h = Math.max(minH, rs.origH - dy);
      if (rs.isElectronWindow) {
        this._electronResizeWindow(rs.surfaceId, Math.round(w), Math.round(h));
      } else if (rs.ghostEl) {
        if (rs.winEl) {
          rs.winEl.style.width = w + 'px';
          rs.winEl.style.height = h + 'px';
        }
        rs.ghostEl.style.width  = w + 'px';
        rs.ghostEl.style.height = h + 'px';
        rs.ghostEl.dataset.resizeDirection = dir;
      }
      this._showResizeHud(w, h, dir);
    }
  }

  _onMouseup(e) {
    if (this.dragState) {
      const ds = this.dragState;
      const dx = e.clientX - ds.startX;
      const dy = e.clientY - ds.startY;
      var newX = ds.origLeft + dx;
      var newY = ds.origTop  + dy;
      var snappedRect = this._snapRectForZone(this._detectSnapZone(e) || this._lastSnapZone);
      if (snappedRect) {
        newX = snappedRect.x;
        newY = snappedRect.y;
      }
      if (this.transport === 'electron-ipc' && this._electronWindows.has(ds.surfaceId)) {
        this._electronMoveWindow(ds.surfaceId, Math.round(newX), Math.round(newY));
        if (snappedRect) this._electronResizeWindow(ds.surfaceId, snappedRect.w, snappedRect.h);
      } else if (ds.winEl) {
        ds.winEl.style.left = Math.round(newX) + 'px';
        ds.winEl.style.top = Math.round(newY) + 'px';
        if (snappedRect) {
          ds.winEl.style.width = snappedRect.w + 'px';
          ds.winEl.style.height = snappedRect.h + 'px';
        }
      }
      // Send authoritative move request; server will reconcile and patch back.
      // window_id_hint is a HINT only; server resolves via UiWindowSurfaceRegistry.
      this._sendWindowCmd('move', {
        window_id_hint: ds.surfaceId,
        ...(ds.isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
        x: Math.round(newX),
        y: Math.round(newY)
      });
      if (snappedRect) {
        this._sendWindowCmd('resize', {
          window_id_hint: ds.surfaceId,
          ...(ds.isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
          w: snappedRect.w,
          h: snappedRect.h,
          snap_zone: this._lastSnapZone || this._detectSnapZone(e)
        });
        this._markSnapCommitted(ds.winEl, this._lastSnapZone || this._detectSnapZone(e));
      }
      if (ds.ghostEl) ds.ghostEl.remove();
      this._clearDragFeedback();
      this._clearSnapPreview();
      clearTimeout(ds.timer);
      this.dragState = null;
    }
    if (this.resizeState) {
      const rs = this.resizeState;
      const dx = e.clientX - rs.startX;
      const dy = e.clientY - rs.startY;
      const dir = rs.direction;
      const minW = 200, minH = 120;
      let w = rs.origW, h = rs.origH;
      if (dir.includes('e')) w = Math.max(minW, rs.origW + dx);
      if (dir.includes('s')) h = Math.max(minH, rs.origH + dy);
      if (dir.includes('w')) w = Math.max(minW, rs.origW - dx);
      if (dir === 'n' || dir.includes('n')) h = Math.max(minH, rs.origH - dy);
      if (this.transport === 'electron-ipc' && this._electronWindows.has(rs.surfaceId)) {
        this._electronResizeWindow(rs.surfaceId, Math.round(w), Math.round(h));
      } else if (rs.winEl) {
        rs.winEl.style.width = Math.round(w) + 'px';
        rs.winEl.style.height = Math.round(h) + 'px';
      }
      this._sendWindowCmd('resize', {
        window_id_hint: rs.surfaceId,
        ...(rs.isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
        w: Math.round(w),
        h: Math.round(h)
      });
      if (rs.ghostEl) rs.ghostEl.remove();
      if (rs.winEl) {
        rs.winEl.dataset.resizeActive = 'false';
        delete rs.winEl.dataset.resizeDirection;
      }
      clearTimeout(rs.timer);
      this.resizeState = null;
      this._hideResizeHud(900);
    }
  }

  // -------------------------------------------------------------------------
  // Global event binding
  // -------------------------------------------------------------------------

  _bindGlobalEvents() {
    this._ensureTopMenuBar();
    this._ensureCommandPalette();
    this._ensureHotCorners();
    this._ensureDesktopItems();
    document.addEventListener('mousemove', (e) => {
      this._updateDesktopBackdropPointer(e);
      this._onMousemove(e);
      this._updateHotCornerPreview(e);
    });
    document.addEventListener('mouseup',   (e) => this._onMouseup(e));

    document.addEventListener('mousedown', (e) => {
      if (this.taskbar && this.taskbar.contains(e.target)) return;
      this._sendHostWmPointer(e, 'down');
      const titlebar = e.target.closest('.wm-titlebar');
      if (titlebar) {
        const winEl = titlebar.closest('.wm-window');
        if (winEl) { this._onTitlebarMousedown(e, winEl); return; }
      }
      const handle = e.target.closest('.wm-resize-handle');
      if (handle) {
        const winEl = handle.closest('.wm-window');
        if (winEl) { this._onResizeMousedown(e, winEl, handle.dataset.direction); return; }
      }
      // Click anywhere on a window — request focus.
      const win = e.target.closest('.wm-window');
      if (win) {
        const surfaceId = win.dataset.surfaceId ?? win.dataset.canonicalId ?? '';
        const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId);
        if (this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId)) {
          this._electronFocusWindow(surfaceId);
        }
        if (surfaceId) {
          this._sendWindowCmd('focus', {
            window_id_hint: surfaceId,
            ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
          });
        }
      }
    });

    document.addEventListener('pointerover', (e) => this._showWmTooltipForEvent(e));
    document.addEventListener('pointermove', (e) => this._positionWmTooltipForEvent(e));
    document.addEventListener('pointerout', (e) => this._hideWmTooltipForEvent(e));
    document.addEventListener('focusin', (e) => this._showWmTooltipForEvent(e));
    document.addEventListener('focusout', (e) => this._hideWmTooltipForEvent(e));

    document.addEventListener('contextmenu', (e) => {
      const target = e.target instanceof Element ? e.target : e.target?.parentElement;
      const win = target?.closest?.('.wm-window');
      if (!win) return;
      e.preventDefault();
      this._showWindowContextMenu(win, e);
    });
    document.addEventListener('pointerdown', (e) => {
      const target = e.target instanceof Element ? e.target : e.target?.parentElement;
      if (!target) return;
      if (target.closest('.wm-window-context-menu')) return;
      if (this._windowContextMenu && !this._windowContextMenu.hidden) this._hideWindowContextMenu();
    });

    // Traffic-light buttons.
    document.addEventListener('pointerover', (e) => {
      const btn = e.target.closest('.wm-traffic-lights .wm-btn-maximize');
      if (!btn) return;
      const win = btn.closest('.wm-window');
      if (win) this._toggleSnapLayoutPalette(win, btn, true);
    });
    document.addEventListener('focusin', (e) => {
      const btn = e.target.closest('.wm-traffic-lights .wm-btn-maximize');
      if (!btn) return;
      const win = btn.closest('.wm-window');
      if (win) this._toggleSnapLayoutPalette(win, btn, true);
    });
    document.addEventListener('pointerdown', (e) => {
      const target = e.target instanceof Element ? e.target : e.target?.parentElement;
      if (!target) return;
      if (target.closest('.wm-snap-layout-palette') || target.closest('.wm-traffic-lights .wm-btn-maximize')) return;
      if (this._snapLayoutPalette && !this._snapLayoutPalette.hidden) this._toggleSnapLayoutPalette(null, null, false);
      if (target.closest('.wm-window-arrange-palette')) return;
      if (this._windowArrangePalette && !this._windowArrangePalette.hidden) this._toggleWindowArrangePalette(false);
    });
    document.addEventListener('click', (e) => {
      const btn = e.target.closest('.wm-traffic-lights button');
      if (!btn) return;
      const win = btn.closest('.wm-window');
      if (!win) return;
      const surfaceId = win.dataset.surfaceId ?? '';
      const action = btn.dataset.action;
      this._markTrafficCommandFeedback(btn, action);
      if (this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId)) {
        if (action === 'close') this._electronCloseWindow(surfaceId);
        else if (action === 'minimize') this._electronMinimizeWindow(surfaceId);
        else if (action === 'maximize') this._electronMaximizeWindow(surfaceId);
      }
      const commandPayload = {
        window_id_hint: surfaceId,
        ...(this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId) ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
      };
      if      (action === 'close')    this._sendWindowCmd('close', commandPayload);
      else if (action === 'minimize') this._sendWindowCmd('minimize', commandPayload);
      else if (action === 'maximize') this._sendWindowCmd('maximize', commandPayload);
    });

    // Forward pointer events inside windows as input_event frames.
    document.addEventListener('pointerdown', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0 };
      this._sendInputEvent(surfId, widId, {
        kind: 'pointer_down',
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top),
        button: e.button
      });
    });

    document.addEventListener('pointerup', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0 };
      this._sendInputEvent(surfId, widId, {
        kind: 'pointer_up',
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top),
        button: e.button
      });
    });

    document.addEventListener('pointermove', (e) => {
      // Only forward when inside a known surface.
      const widget = e.target.closest('[data-surface-id]');
      if (!widget) return;
      const surfId = widget.dataset.surfaceId ?? '';
      if (!surfId) return;
      const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0 };
      this._sendInputEvent(surfId, '', {
        kind: 'pointer_move',
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top)
      });
    });

    document.addEventListener('wheel', (e) => {
      if (this._handleTrackpadGesture(e)) return;
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      this._sendInputEvent(surfId, widId, {
        kind: 'wheel',
        delta_x: Math.round(e.deltaX),
        delta_y: Math.round(e.deltaY)
      });
    });

    document.addEventListener('keydown', (e) => {
      const wantsPalette = (e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k';
      if (wantsPalette) {
        e.preventDefault();
        this._toggleCommandPalette();
        return;
      }
      const wantsAppLauncher = (e.metaKey || e.ctrlKey) && e.key === ' ';
      if (wantsAppLauncher) {
        e.preventDefault();
        this._toggleAppLauncher();
        return;
      }
      const wantsShortcutOverlay = (e.metaKey || e.ctrlKey) && e.key === '/';
      if (wantsShortcutOverlay) {
        e.preventDefault();
        this._toggleShortcutOverlay();
        return;
      }
      const wantsWindowSwitcher = (e.metaKey || e.ctrlKey || e.altKey) && e.key === 'Tab';
      if (wantsWindowSwitcher) {
        e.preventDefault();
        if (this._windowSwitcher && !this._windowSwitcher.hidden) {
          this._moveWindowSwitcherSelection(e.shiftKey ? -1 : 1);
        } else {
          this._windowSwitcherActiveIndex = 0;
          this._toggleWindowSwitcher(true);
        }
        return;
      }
      const wantsOverview = (e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'o';
      const wantsStageRail = wantsOverview && e.shiftKey;
      if (wantsStageRail) {
        e.preventDefault();
        this._toggleStageRail();
        return;
      }
      if (wantsOverview) {
        e.preventDefault();
        this._toggleWindowOverview();
        return;
      }
      const wantsControlCenter = (e.metaKey || e.ctrlKey) && e.key === ',';
      if (wantsControlCenter) {
        e.preventDefault();
        this._toggleControlCenter();
        return;
      }
      const wantsSystemHud = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'h';
      if (wantsSystemHud) {
        e.preventDefault();
        this._showSystemHud('System', 'ready', 2600);
        return;
      }
      const wantsPrivacyIndicator = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'p';
      if (wantsPrivacyIndicator) {
        e.preventDefault();
        this._togglePrivacyIndicator();
        return;
      }
      const wantsWorkspaceSwitcher = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'w';
      if (wantsWorkspaceSwitcher) {
        e.preventDefault();
        this._toggleWorkspaceSwitcher();
        return;
      }
      const wantsClipboardHistory = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'v';
      if (wantsClipboardHistory) {
        e.preventDefault();
        this._toggleClipboardHistory();
        return;
      }
      const wantsScreenCapture = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 's';
      if (wantsScreenCapture) {
        e.preventDefault();
        this._toggleScreenCapture();
        return;
      }
      const wantsQuickSettings = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'q';
      if (wantsQuickSettings) {
        e.preventDefault();
        this._toggleQuickSettings();
        return;
      }
      const wantsNotificationCenter = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'n';
      if (wantsNotificationCenter) {
        e.preventDefault();
        this._toggleNotificationCenter();
        return;
      }
      const wantsLiveActivity = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'a';
      if (wantsLiveActivity) {
        e.preventDefault();
        this._toggleLiveActivity();
        return;
      }
      const wantsGestureHints = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'g';
      if (wantsGestureHints) {
        e.preventDefault();
        this._toggleGestureHints();
        return;
      }
      const wantsDockStack = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'd';
      if (wantsDockStack) {
        e.preventDefault();
        this._toggleDockStack();
        return;
      }
      const wantsQualityInspector = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'i';
      if (wantsQualityInspector) {
        e.preventDefault();
        this._toggleQualityInspector();
        return;
      }
      const wantsAccentPalette = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'c';
      if (wantsAccentPalette) {
        e.preventDefault();
        this._toggleAccentPalette();
        return;
      }
      const wantsFocusMode = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'f';
      if (wantsFocusMode) {
        e.preventDefault();
        this._toggleFocusMode();
        return;
      }
      const wantsWallpaperPicker = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'b';
      if (wantsWallpaperPicker) {
        e.preventDefault();
        this._toggleWallpaperPicker();
        return;
      }
      const wantsDesktopPeek = (e.metaKey || e.ctrlKey) && e.shiftKey && e.key.toLowerCase() === 'm';
      if (wantsDesktopPeek) {
        e.preventDefault();
        this._toggleDesktopPeek();
        return;
      }
      const wantsTitleCommand = (e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'l';
      const wantsWindowArrange = wantsTitleCommand && e.shiftKey;
      if (wantsWindowArrange) {
        e.preventDefault();
        this._toggleWindowArrangePalette();
        return;
      }
      if (wantsTitleCommand) {
        if (this._focusActiveTitleInput()) {
          e.preventDefault();
          return;
        }
      }
      if (this._windowContextMenu && !this._windowContextMenu.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._hideWindowContextMenu();
          return;
        }
      }
      if (this._appLauncher && !this._appLauncher.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleAppLauncher(false);
          return;
        }
      }
      if (this._shortcutOverlay && !this._shortcutOverlay.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleShortcutOverlay(false);
          return;
        }
      }
      if (this._controlCenter && !this._controlCenter.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleControlCenter(false);
          return;
        }
      }
      if (this._wallpaperPicker && !this._wallpaperPicker.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleWallpaperPicker(false);
          return;
        }
      }
      if (this._accentPalette && !this._accentPalette.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleAccentPalette(false);
          return;
        }
      }
      if (this._snapLayoutPalette && !this._snapLayoutPalette.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleSnapLayoutPalette(null, null, false);
          return;
        }
      }
      if (this._windowArrangePalette && !this._windowArrangePalette.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleWindowArrangePalette(false);
          return;
        }
      }
      if (this._dockStack && !this._dockStack.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleDockStack(false);
          return;
        }
      }
      if (this._qualityInspector && !this._qualityInspector.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleQualityInspector(false);
          return;
        }
      }
      if (this._stageRail && !this._stageRail.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleStageRail(false);
          return;
        }
      }
      if (this._windowSwitcher && !this._windowSwitcher.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleWindowSwitcher(false);
          return;
        }
        if (e.key === 'ArrowRight' || e.key === 'ArrowDown') {
          e.preventDefault();
          this._moveWindowSwitcherSelection(1);
          return;
        }
        if (e.key === 'ArrowLeft' || e.key === 'ArrowUp') {
          e.preventDefault();
          this._moveWindowSwitcherSelection(-1);
          return;
        }
        if (e.key === 'Enter') {
          e.preventDefault();
          this._activateWindowSwitcherSelection();
          return;
        }
      }
      if (this._workspaceSwitcher && !this._workspaceSwitcher.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleWorkspaceSwitcher(false);
          return;
        }
      }
      if (this._clipboardHistory && !this._clipboardHistory.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleClipboardHistory(false);
          return;
        }
      }
      if (this._screenCaptureOverlay && !this._screenCaptureOverlay.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleScreenCapture(false);
          return;
        }
      }
      if (this._quickSettings && !this._quickSettings.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleQuickSettings(false);
          return;
        }
      }
      if (this._notificationCenter && !this._notificationCenter.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleNotificationCenter(false);
          return;
        }
      }
      if (this._liveActivity && !this._liveActivity.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleLiveActivity(false);
          return;
        }
      }
      if (this._gestureHints && !this._gestureHints.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleGestureHints(false);
          return;
        }
      }
      if (this._privacyIndicator && !this._privacyIndicator.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._togglePrivacyIndicator(false);
          return;
        }
      }
      if (this._windowOverview && !this._windowOverview.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleWindowOverview(false);
          return;
        }
      }
      if (this._commandPalette && !this._commandPalette.hidden) {
        if (e.key === 'Escape') {
          e.preventDefault();
          this._toggleCommandPalette(false);
          return;
        }
        if (e.key === 'ArrowDown') {
          e.preventDefault();
          this._moveCommandPaletteSelection(1);
          return;
        }
        if (e.key === 'ArrowUp') {
          e.preventDefault();
          this._moveCommandPaletteSelection(-1);
          return;
        }
        if (e.key === 'Enter') {
          e.preventDefault();
          this._executeCommandPaletteAction();
          return;
        }
        return;
      }
      if (!this.renderer || !this.renderer.activeSurface) return;
      const surfId = this.renderer.activeSurface;
      this._sendInputEvent(surfId, '', {
        kind: 'key_down',
        key: e.key,
        key_code: e.keyCode,
        modifiers: _modifiers(e),
        repeat: e.repeat
      });
    });

    document.addEventListener('keyup', (e) => {
      if (!this.renderer || !this.renderer.activeSurface) return;
      const surfId = this.renderer.activeSurface;
      this._sendInputEvent(surfId, '', {
        kind: 'key_up',
        key: e.key,
        key_code: e.keyCode,
        modifiers: _modifiers(e)
      });
    });

    document.addEventListener('input', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      this._sendInputEvent(surfId, widId, {
        kind: 'text_input',
        text: e.target.value ?? e.data ?? ''
      });
    });
  }

  // -------------------------------------------------------------------------
  // Toast (error display)
  // -------------------------------------------------------------------------

  _showToast(msg) {
    if (!this._feedbackAllows('critical')) return;
    const t = document.createElement('div');
    t.className = 'wm-toast';
    t.textContent = msg;
    document.body.appendChild(t);
    setTimeout(() => t.remove(), 4000);
  }
}

// -------------------------------------------------------------------------
// Helpers
// -------------------------------------------------------------------------

function _modifiers(e) {
  return (e.shiftKey ? 1 : 0) | (e.ctrlKey ? 2 : 0) | (e.altKey ? 4 : 0) | (e.metaKey ? 8 : 0);
}

function _escapeHtml(value) {
  return String(value || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function _escapeAttr(value) {
  return _escapeHtml(value).replace(/`/g, '&#96;');
}

// Global instance — initialized by inline boot script.
var simpleWM = null;
