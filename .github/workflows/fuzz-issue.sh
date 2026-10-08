#!/usr/bin/env bash
# Opens or updates the issue for a fuzz finding from the target's log: `TARGET`, `RUN_URL`,
# `GH_TOKEN`, and `GH_REPO` name the target, the run, and where the issue goes. A second argument
# is `fuzz-shrink.sh`'s decoded shrink to quote; `DRY_RUN` prints the issue instead of filing it.
set -euo pipefail

log="$1"
shrunk="${2:-}"
summary="$(grep -m1 -oE '^SUMMARY: libFuzzer: .*' "$log" | sed 's/SUMMARY: libFuzzer: //' || true)"
artifact="$(grep -m1 -oE 'Test unit written to [^ ]+' "$log" | sed 's#.*/##' || true)"
message="$(grep -A1 -m1 'panicked at' "$log" | tail -n +2 || true)"
# The panic site is the shared invariant check, which every bug of a layer fails, so the title
# is the message's shape: its numbers, quoted source, and `Some(..)` wrappers dropped.
shape="$(printf '%s' "$message" \
  | sed -E 's/"[^"]*"//g; s/Some\(([A-Za-z]+)\)/\1/g; s/[0-9]+/N/g; s/  +/ /g; s/ +$//' \
  | cut -c1-120)"
if [ -n "$shape" ]; then
  what="$shape"
elif [ -n "$summary" ]; then
  what="$summary"
else
  what="job failed without a finding"
fi
title="fuzz($TARGET): $what"

excerpt="$(sed -n '/panicked at/,/^evidence:/p' "$log" | head -60 || true)"
if [ -z "$excerpt" ]; then
  excerpt="$(grep -E '^(==[0-9]+== |SUMMARY|ALARM|MS: )' "$log" | head -20 || true)"
fi

body="$(cat <<BODY
The nightly \`$TARGET\` fuzz target found this in [run $GITHUB_RUN_ID]($RUN_URL).

**Artifact:** \`${artifact:-none}\`, in the run's \`fuzz-artifacts-$TARGET\` upload.

\`\`\`text
${message:-$what}
\`\`\`

<details>
<summary>Log excerpt</summary>

\`\`\`text
$excerpt
\`\`\`

</details>

$(if [ -n "$shrunk" ] && [ -s "$shrunk" ]; then
  printf '%s\n' "**Shrinks to** (\`tmin\`; it keeps a crash, not always this one, so the assertion it trips is shown):" "" '```text'
  cat "$shrunk"
  printf '%s\n' '```' ""
fi)

To reproduce and shrink, with the artifact under \`fuzz/artifacts/$TARGET/\`:

\`\`\`sh
cargo fuzz run -s none $TARGET fuzz/artifacts/$TARGET/${artifact:-<artifact>}
cargo fuzz tmin -s none $TARGET fuzz/artifacts/$TARGET/${artifact:-<artifact>}
\`\`\`

Keep the shrunk input as a corpus case under \`tests/corpus/\` with the fix. A later finding
whose message has this shape is a comment below; it may be a different bug, so read each before
closing.
BODY
)"

# A list, not a search, and the oldest match: the index lags an issue another target opened or
# closed moments ago.
if [ -n "${DRY_RUN:-}" ]; then
  printf 'TITLE: %s\n\n%s\n' "$title" "$body"
  exit 0
fi
number="$(gh issue list --state open --label bug --limit 200 --json number,title \
  --jq "[.[] | select(.title == \"$title\") | .number] | min // empty")"
if [ -n "$number" ]; then
  gh issue comment "$number" --body "$body"
  echo "commented on #$number"
else
  gh issue create --title "$title" --label bug --body "$body"
fi
