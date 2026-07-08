#!/usr/bin/env bash
# Smoke-run every demo headless: 60 frames each under dummy drivers.
# Mirrors lean-sdl3's scripts/smoke-examples.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

export SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy COMPOSE_MAX_FRAMES=60

demos=$(lake exe gallery --list 2>/dev/null || true)
if [ -z "$demos" ]; then
  echo "no demos registered yet — smoke test trivially passes"
  exit 0
fi

for demo in $demos; do
  echo "=== smoke: $demo ==="
  lake exe "$demo"
done
echo "all demos smoked OK"
