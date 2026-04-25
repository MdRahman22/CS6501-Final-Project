#!/usr/bin/env bash
# Build standalone HTML visualizations with embedded data.
# Run from the project root:
#   bash Content/B05_Geometry/viz/build.sh
#
# Prerequisites: lake build geomviz geomanim

set -euo pipefail

VIZ_DIR="Content/B05_Geometry/viz"

echo "Generating scene data..."
.lake/build/bin/geomviz  > "$VIZ_DIR/scene.json"
.lake/build/bin/geomanim > "$VIZ_DIR/anim.json"

echo "Building standalone HTML files..."
python3 -c "
import re

VIZ = '$VIZ_DIR'

# --- Static visualization ---
with open(f'{VIZ}/index.html') as f:
    html = f.read()
with open(f'{VIZ}/scene.json') as f:
    data = f.read().strip()

# Replace d3.json fetch with inline data
html = re.sub(
    r'd3\.json\(\"scene\.json\"\)\.then\(render\)\.catch\(err => \{[^}]+\}\);',
    'render(' + data.replace('\\\\', '\\\\\\\\') + ');',
    html,
    flags=re.DOTALL
)
with open(f'{VIZ}/static.html', 'w') as f:
    f.write(html)
print(f'  {VIZ}/static.html')

# --- Animated visualization ---
with open(f'{VIZ}/animated.html') as f:
    html = f.read()
with open(f'{VIZ}/anim.json') as f:
    data = f.read().strip()

# Replace d3.json fetch with IIFE using inline data
html = re.sub(
    r'd3\.json\(\"anim\.json\"\)\.then\(animData => \{',
    '(function(animData) {',
    html
)
html = re.sub(
    r'\}\)\.catch\(err => \{[^}]+\}\);',
    '})(' + data.replace('\\\\', '\\\\\\\\') + ');',
    html,
    flags=re.DOTALL
)
with open(f'{VIZ}/animation.html', 'w') as f:
    f.write(html)
print(f'  {VIZ}/animation.html')
"

echo "Copying standalone files to src for mdBook..."
cp "$VIZ_DIR/static.html" "src/$VIZ_DIR/static.html"
cp "$VIZ_DIR/animation.html" "src/$VIZ_DIR/animation.html"

echo "Done."
ls -lh "$VIZ_DIR/static.html" "$VIZ_DIR/animation.html"
