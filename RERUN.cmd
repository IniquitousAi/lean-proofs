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
  rem Logged to runs\steps.jsonl, append only. With no bash the time is cmd's own DATE and TIME, in this PC's date format.
  rem No parentheses in these lines: inside this block one would end it.
  if not exist runs mkdir runs
  >>runs\steps.jsonl echo {"at":"%DATE% %TIME%","script":"RERUN.cmd","ran":"RERUN.cmd","found":"no Git bash: bash.exe is not in Program Files or LocalAppData Programs","result":"FAIL","exit":1}
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
