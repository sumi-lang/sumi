#!/usr/bin/env bash
# Opens or updates the issue for a fuzz finding from the target's log: `TARGET`, `RUN_URL`,
# `GH_TOKEN`, and `GH_REPO` name the target, the run, and where the issue goes.
set -euo pipefail

log="$1"
location="$(grep -oE 'panicked at [^ ]+:[0-9]+' "$log" | head -1 | sed 's/panicked at //' || true)"
summary="$(grep -m1 -oE '^SUMMARY: libFuzzer: .*' "$log" | sed 's/SUMMARY: libFuzzer: //' || true)"
artifact="$(grep -m1 -oE 'Test unit written to [^ ]+' "$log" | sed 's#.*/##' || true)"
if [ -n "$location" ]; then
  what="panic at $location"
elif [ -n "$summary" ]; then
  what="$summary"
else
  what="job failed without a finding"
fi
title="fuzz($TARGET): $what"

message="$(grep -A1 -m1 'panicked at' "$log" | tail -n +2 || true)"
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

To reproduce and shrink, with the artifact under \`fuzz/artifacts/$TARGET/\`:

\`\`\`sh
cargo fuzz run -s none $TARGET fuzz/artifacts/$TARGET/${artifact:-<artifact>}
cargo fuzz tmin -s none $TARGET fuzz/artifacts/$TARGET/${artifact:-<artifact>}
\`\`\`

Keep the shrunk input as a corpus case under \`tests/corpus/\` with the fix.
BODY
)"

# A list, not a search, and the oldest match: the index lags an issue another target opened or
# closed moments ago.
number="$(gh issue list --state open --label bug --limit 200 --json number,title \
  --jq "[.[] | select(.title == \"$title\") | .number] | min // empty")"
if [ -n "$number" ]; then
  gh issue comment "$number" --body "$body"
  echo "commented on #$number"
else
  gh issue create --title "$title" --label bug --body "$body"
fi
