#!/usr/bin/env python3
"""Export saved Criterion means and bootstrap confidence intervals as CSV.

Usage: python3 crates/hir/benches/summarize.py target/criterion run1 run2
Allocation CSVs come directly from `cargo bench --bench allocations` instead.
"""

import csv
import json
import sys
from pathlib import Path


def main():
    if len(sys.argv) < 3:
        raise SystemExit("usage: summarize.py CRITERION_DIRECTORY BASELINE [BASELINE ...]")
    root = Path(sys.argv[1])
    writer = csv.writer(sys.stdout)
    writer.writerow([
        "baseline", "benchmark", "elements", "mean_ns", "ci95_low_ns",
        "ci95_high_ns", "ns_per_element",
    ])
    for baseline in sys.argv[2:]:
        found = False
        for path in sorted(root.glob(f"**/{baseline}/estimates.json")):
            metadata = json.loads(path.with_name("benchmark.json").read_text())
            if not metadata["group_id"].startswith(("solver/", "hir/")):
                continue
            found = True
            mean = json.loads(path.read_text())["mean"]
            interval = mean["confidence_interval"]
            assert interval["confidence_level"] == 0.95
            elements = metadata["throughput"]["Elements"]
            writer.writerow([
                baseline, metadata["full_id"], elements, mean["point_estimate"],
                interval["lower_bound"], interval["upper_bound"],
                mean["point_estimate"] / elements,
            ])
        if not found:
            raise SystemExit(f"no solver/HIR estimates for {baseline!r} in {root}")


if __name__ == "__main__":
    main()
