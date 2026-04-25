@echo off
setlocal

cd /d "C:\Software Logic\MissileAffineProject"

echo.
echo Building geomanim...
call lake build geomanim
if errorlevel 1 (
  echo.
  echo Build failed.
  pause
  exit /b 1
)

echo.
echo Generating anim.json...
powershell -NoProfile -ExecutionPolicy Bypass -Command "$json = lake exe geomanim; $utf8NoBom = New-Object System.Text.UTF8Encoding($false); [System.IO.File]::WriteAllText('C:\Software Logic\MissileAffineProject\Content\B05_Geometry\viz\anim.json', $json, $utf8NoBom)"
if errorlevel 1 (
  echo.
  echo Failed to generate anim.json.
  pause
  exit /b 1
)

echo.
echo Starting local server...
start "MissileAffineServer" cmd /k "cd /d C:\Software Logic\MissileAffineProject\Content\B05_Geometry\viz && py -m http.server 8080"

timeout /t 2 /nobreak >nul

echo.
echo Opening browser...
start http://localhost:8080/animated.html?v=%RANDOM%

echo.
echo Done.
exit /b 0