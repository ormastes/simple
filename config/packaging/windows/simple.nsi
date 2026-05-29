; Simple Language NSIS Installer Script
; Template with ${VARIABLE} placeholders substituted at build time.
;
; Build from Linux: makensis -NOCD -DOUTFILE=output.exe simple-installer.nsi
; Requires: apt install nsis

!include "MUI2.nsh"

; ---- Variables (substituted by backend_nsis.spl) ----
!define PRODUCT_NAME "Simple Language"
!define PRODUCT_VERSION "${VERSION}"
!define PRODUCT_PUBLISHER "${PUBLISHER}"
!define PRODUCT_WEB_SITE "${HOMEPAGE}"
!define PRODUCT_DIR_REGKEY "Software\Microsoft\Windows\CurrentVersion\App Paths\simple.exe"
!define PRODUCT_UNINST_KEY "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_NAME}"
!define PRODUCT_UNINST_ROOT_KEY "HKLM"

; ---- General ----
Name "${PRODUCT_NAME} ${PRODUCT_VERSION}"
OutFile "${OUTPUT_DIR}\${PACKAGE_NAME}-${VERSION}-setup.exe"
InstallDir "$PROGRAMFILES\Simple"
InstallDirRegKey HKLM "${PRODUCT_DIR_REGKEY}" ""
ShowInstDetails show
ShowUnInstDetails show

; ---- MUI Settings ----
!define MUI_ABORTWARNING
!define MUI_ICON "${NSISDIR}\Contrib\Graphics\Icons\modern-install.ico"
!define MUI_UNICON "${NSISDIR}\Contrib\Graphics\Icons\modern-uninstall.ico"

; ---- Pages ----
!insertmacro MUI_PAGE_WELCOME
!insertmacro MUI_PAGE_LICENSE "${SOURCE_DIR}\doc\LICENSE"
!insertmacro MUI_PAGE_DIRECTORY
!insertmacro MUI_PAGE_INSTFILES
!insertmacro MUI_PAGE_FINISH

!insertmacro MUI_UNPAGE_INSTFILES

; ---- Language ----
!insertmacro MUI_LANGUAGE "English"

; ---- Installer Section ----
Section "Simple Language" SEC01
    SetOutPath "$INSTDIR\bin"
    File "${SOURCE_DIR}\bin\simple.exe"

    SetOutPath "$INSTDIR\lib"
    File /r "${SOURCE_DIR}\lib\*.*"

    SetOutPath "$INSTDIR\doc"
    File /nonfatal "${SOURCE_DIR}\doc\README.md"
    File /nonfatal "${SOURCE_DIR}\doc\LICENSE"
SectionEnd

Section -AdditionalIcons
    CreateDirectory "$SMPROGRAMS\Simple Language"
    CreateShortCut "$SMPROGRAMS\Simple Language\Simple REPL.lnk" "$INSTDIR\bin\simple.exe"
    CreateShortCut "$SMPROGRAMS\Simple Language\Uninstall.lnk" "$INSTDIR\uninst.exe"
    CreateShortCut "$DESKTOP\Simple REPL.lnk" "$INSTDIR\bin\simple.exe"
SectionEnd

Section -Post
    WriteUninstaller "$INSTDIR\uninst.exe"
    WriteRegStr HKLM "${PRODUCT_DIR_REGKEY}" "" "$INSTDIR\bin\simple.exe"
    WriteRegStr ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}" "DisplayName" "$(^Name)"
    WriteRegStr ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}" "UninstallString" "$INSTDIR\uninst.exe"
    WriteRegStr ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}" "DisplayIcon" "$INSTDIR\bin\simple.exe"
    WriteRegStr ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}" "DisplayVersion" "${PRODUCT_VERSION}"
    WriteRegStr ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}" "URLInfoAbout" "${PRODUCT_WEB_SITE}"
    WriteRegStr ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}" "Publisher" "${PRODUCT_PUBLISHER}"

    ; Add to PATH
    ReadRegStr $0 HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path"
    WriteRegExpandStr HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path" "$0;$INSTDIR\bin"
    SendMessage ${HWND_BROADCAST} ${WM_WININICHANGE} 0 "STR:Environment" /TIMEOUT=5000
SectionEnd

; ---- Uninstaller Section ----
Section Uninstall
    ; Remove from PATH
    ReadRegStr $0 HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path"
    ${WordReplace} $0 ";$INSTDIR\bin" "" "+" $0
    WriteRegExpandStr HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path" "$0"

    ; Remove shortcuts
    Delete "$SMPROGRAMS\Simple Language\Simple REPL.lnk"
    Delete "$SMPROGRAMS\Simple Language\Uninstall.lnk"
    Delete "$DESKTOP\Simple REPL.lnk"
    RMDir "$SMPROGRAMS\Simple Language"

    ; Remove files
    RMDir /r "$INSTDIR\bin"
    RMDir /r "$INSTDIR\lib"
    RMDir /r "$INSTDIR\doc"
    Delete "$INSTDIR\uninst.exe"
    RMDir "$INSTDIR"

    ; Remove registry keys
    DeleteRegKey ${PRODUCT_UNINST_ROOT_KEY} "${PRODUCT_UNINST_KEY}"
    DeleteRegKey HKLM "${PRODUCT_DIR_REGKEY}"

    SendMessage ${HWND_BROADCAST} ${WM_WININICHANGE} 0 "STR:Environment" /TIMEOUT=5000
SectionEnd
