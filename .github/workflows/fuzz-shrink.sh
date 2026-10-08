#!/usr/bin/env bash
# Shrinks the target's first finding with `cargo fuzz tmin` into `shrunk-<finding>` beside it,
# the intermediate steps removed, and writes it decoded to `shrunk.txt` with the assertion it
# trips: `tmin` keeps a crash, not the same one. Nothing is written when it cannot shrink.
set -euo pipefail

target="$1"
dir="fuzz/artifacts/$target"
finding="$(ls "$dir"/crash-* "$dir"/timeout-* "$dir"/oom-* 2>/dev/null | head -1 || true)"
[ -n "$finding" ] || exit 0
# Most byte removals leave an input the target rejects before checking anything, so the attempts
# are many; each is cheap.
log="$(cargo fuzz tmin -s none -r 200000 "$target" "$finding" -- -max_total_time=120 2>&1 || true)"
final="$(printf '%s\n' "$log" | grep -oE 'failed to minimize beyond [^ ]+' | tail -1 \
  | sed 's/failed to minimize beyond //' || true)"
if [ -z "$final" ] || [ ! -f "$final" ] || [ "$(realpath "$final")" = "$(realpath "$finding")" ]; then
  rm -f "$dir"/minimized-from-*
  exit 0
fi
shrunk="$dir/shrunk-$(basename "$finding")"
mv "$final" "$shrunk"
rm -f "$dir"/minimized-from-*
scratch="$(mktemp -d)"
{
  echo "$(wc -c < "$shrunk") bytes, from $(wc -c < "$finding")"
  cargo run --locked -q -p sumi-test --bin fuzz-show -- "$target" "$shrunk"
  echo "--- trips ---"
  cargo fuzz run -s none "$target" "$shrunk" -- -artifact_prefix="$scratch/" 2>&1 \
    | grep -A1 -m1 'panicked at' | tail -n +2 || true
} > shrunk.txt
rm -rf "$scratch"
