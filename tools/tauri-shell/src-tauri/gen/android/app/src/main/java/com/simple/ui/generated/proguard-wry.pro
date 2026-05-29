# THIS FILE IS AUTO-GENERATED. DO NOT MODIFY!!

# Copyright 2020-2023 Tauri Programme within The Commons Conservancy
# SPDX-License-Identifier: Apache-2.0
# SPDX-License-Identifier: MIT

-keep class com.simple.ui.* {
  native <methods>;
}

-keep class com.simple.ui.WryActivity {
  public <init>(...);

  void setWebView(com.simple.ui.RustWebView);
  java.lang.Class getAppClass(...);
  java.lang.String getVersion();
}

-keep class com.simple.ui.Ipc {
  public <init>(...);

  @android.webkit.JavascriptInterface public <methods>;
}

-keep class com.simple.ui.RustWebView {
  public <init>(...);

  void loadUrlMainThread(...);
  void loadHTMLMainThread(...);
  void evalScript(...);
}

-keep class com.simple.ui.RustWebChromeClient,com.simple.ui.RustWebViewClient {
  public <init>(...);
}
