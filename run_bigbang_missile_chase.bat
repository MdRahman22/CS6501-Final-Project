@echo off
cd /d "%~dp0"

echo Building BigBang MissileChase module...
lake build Content.B06_CoinductiveGameEngine.games.MissileChase

if errorlevel 1 (
  echo Build failed
  pause
  exit /b 1
)

echo.
echo Regenerating BigBang missile chase JSON...
powershell -NoProfile -ExecutionPolicy Bypass -Command "lake env lean --run Content/B06_CoinductiveGameEngine/viz/MissileChaseMain.lean | Set-Content -Encoding utf8 Content/B06_CoinductiveGameEngine/viz/missile-demo.json"

if errorlevel 1 (
  echo Failed to generate missile-demo.json
  pause
  exit /b 1
)

echo.
echo Starting server for BigBang missile chase...
echo Open this in your browser:
echo http://localhost:8002/missile.html
echo.
cd Content\B06_CoinductiveGameEngine\viz
python -m http.server 8002
pause
