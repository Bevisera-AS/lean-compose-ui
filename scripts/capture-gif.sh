#!/usr/bin/env bash
# Record a demo as an animated GIF.
#
#   scripts/capture-gif.sh <demo-exe> <out.gif> [frames] [fps] [width]
#
# Drives the demo through `COMPOSE_CAPTURE` (see `Compose.captureFrames`),
# which writes raw RGBA frames on a virtual clock — deterministic, so a
# re-run reproduces the same GIF — then packs them with ffmpeg.
#
# Honors COMPOSE_BACKEND (default `gpu`, so the GIF shows what the GPU
# renderer actually draws: real offscreen layers, blur, SDF edges). The GPU
# backend has no dummy-driver support, so this is local-only and a window
# briefly appears; `COMPOSE_BACKEND=sdl` runs headless under
# SDL_VIDEO_DRIVER=dummy.
#
# `width` rescales the output (captures are at device pixels — 2× on a HiDPI
# display — so pass the demo's Dp width to land on the same scale as the
# stills in docs/screenshots/).
set -euo pipefail

if [ $# -lt 2 ]; then
  sed -n '2,17p' "$0" | sed 's/^# \{0,1\}//'
  exit 2
fi

exe=$1
out=$2
frames=${3:-60}
fps=${4:-20}
outWidth=${5:-0}

command -v ffmpeg >/dev/null || { echo "capture-gif: ffmpeg not found" >&2; exit 1; }

export COMPOSE_BACKEND=${COMPOSE_BACKEND:-gpu}
raw=$(mktemp -t compose-capture).rgba
trap 'rm -f "$raw" "$raw.pal.png"' EXIT

echo "capture-gif: $exe -> $out ($frames frames @ ${fps}fps, backend=$COMPOSE_BACKEND)"
lake build "$exe" >/dev/null

log=$(COMPOSE_CAPTURE="$raw" COMPOSE_CAPTURE_FRAMES="$frames" \
      COMPOSE_CAPTURE_FPS="$fps" lake exe "$exe")
info=$(printf '%s\n' "$log" | grep COMPOSE_CAPTURE_INFO) || {
  echo "capture-gif: demo produced no capture info:" >&2
  printf '%s\n' "$log" >&2
  exit 1
}
eval "$(printf '%s\n' "$info" | tr ' ' '\n' | grep -E '^(width|height)=')"
echo "capture-gif: ${info#COMPOSE_CAPTURE_INFO }"

# Two-pass palette: Material's gradients, ripples and progress fades band
# badly under GIF's 256 colors with a single global palette picked blind.
# stats_mode=diff weights the palette toward what actually moves.
scale=
if [ "$outWidth" -gt 0 ]; then
  scale="scale=$outWidth:-1:flags=lanczos,"
fi

ffmpeg -y -loglevel error \
  -f rawvideo -pix_fmt rgba -s "${width}x${height}" -r "$fps" -i "$raw" \
  -filter_complex "${scale}split[a][b];[a]palettegen=stats_mode=diff[p];[b][p]paletteuse=dither=bayer:bayer_scale=3" \
  -loop 0 "$out"

echo "capture-gif: wrote $out ($(du -h "$out" | cut -f1))"
