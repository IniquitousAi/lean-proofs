@echo off
rem Re-run every claim in RERUN-RECEIPT.md on this Windows PC. Double-click it, or run it in a window.
rem Needs Git for Windows (for bash): https://git-scm.com/download/win . Everything else RERUN.sh checks for you.
setlocal
cd /d "%~dp0"
echo Humanities Helping Hands engine, built by Daniel Steadham
set "BASH=%ProgramFiles%\Git\bin\bash.exe"
if not exist "%BASH%" set "BASH=%LocalAppData%\Programs\Git\bin\bash.exe"
if not exist "%BASH%" (
  echo RERUN: Git for Windows is missing. Install it from https://git-scm.com/download/win , then run RERUN.cmd again.
  pause
  exit /b 1
)
set "PATH=%UserProfile%\.elan\bin;%PATH%"
set "RERUN_BASH=%BASH%"
"%BASH%" RERUN.sh %*
set "CODE=%ERRORLEVEL%"
echo.
echo RERUN finished (exit %CODE%). The full Lean output is in AUDIT.log.
pause
exit /b %CODE%
