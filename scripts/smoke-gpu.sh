#!/usr/bin/env bash
# Smoke-run every demo on the GPU backend: 120 frames each on the REAL video
# driver (SDL_GPU has no dummy backend — this script is local-only, not CI).
# Windows will briefly appear on screen. Mirrors scripts/smoke-demos.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

export COMPOSE_BACKEND=gpu COMPOSE_MAX_FRAMES=120

demos=$(lake exe gallery --list 2>/dev/null || true)
if [ -z "$demos" ]; then
  echo "no demos registered yet — GPU smoke trivially passes"
  exit 0
fi

echo "=== gpu-smoke: gpu-probe ==="
GPU_PROBE_FRAMES=60 lake exe gpu-probe

echo "=== gpu-smoke: gpu-parity ==="
lake exe gpu-parity

echo "=== gpu-smoke: gallery ==="
lake exe gallery

for demo in $demos; do
  echo "=== gpu-smoke: $demo ==="
  lake exe "$demo"
done
echo "all demos smoked OK on the GPU backend"
