#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

lake build :blueprint
lake build :blueprintJson

mkdir -p blueprint

find .lake/build/blueprint/module/CommunicationComplexity/Blueprint.artifacts -name '*.tex' -print \
  | sed 's#.*/##; s#\.tex$##' \
  | sort > blueprint/leanarchitect_nodes.txt

: > blueprint/leanarchitect_edges.csv
for f in .lake/build/blueprint/module/CommunicationComplexity/Blueprint.artifacts/*.tex; do
  src="$(basename "$f" .tex)"
  uses="$(sed -n 's/^\\uses{\(.*\)}$/\1/p' "$f")"
  if [[ -n "$uses" ]]; then
    IFS=',' read -ra deps <<< "$uses"
    for dst in "${deps[@]}"; do
      [[ -n "$dst" ]] && printf '%s,%s\n' "$src" "$dst" >> blueprint/leanarchitect_edges.csv
    done
  fi
done
sort -u blueprint/leanarchitect_edges.csv -o blueprint/leanarchitect_edges.csv

python3 - <<'PY'
import csv
from collections import defaultdict
from pathlib import Path

root = Path("blueprint")
nodes = [line.strip() for line in (root / "leanarchitect_nodes.txt").read_text().splitlines() if line.strip()]
edges = []
with (root / "leanarchitect_edges.csv").open() as f:
    for r in csv.reader(f):
        if len(r) == 2 and r[0] and r[1]:
            edges.append((r[0], r[1]))

with (root / "dependency_graph.dot").open("w") as f:
    f.write("digraph Blueprint {\n")
    f.write("  rankdir=LR;\n")
    f.write("  graph [overlap=false, splines=true, bgcolor=\"white\"];\n")
    f.write("  node [shape=box, style=\"rounded,filled\", fillcolor=\"#f7fbff\", color=\"#4a6fa5\", fontname=\"Helvetica\", fontsize=10];\n")
    f.write("  edge [color=\"#6c7a89\", arrowsize=0.6];\n")
    for n in nodes:
        f.write(f"  \"{n}\";\n")
    for s, t in edges:
        f.write(f"  \"{s}\" -> \"{t}\";\n")
    f.write("}\n")

def module_of(name: str) -> str:
    parts = name.split(".")
    if name.startswith("CommunicationComplexity."):
        return ".".join(parts[: min(len(parts), 3)])
    if len(parts) >= 2:
        return ".".join(parts[:2])
    return name

mod_nodes = set(module_of(n) for n in nodes)
mod_edges = defaultdict(int)
for s, t in edges:
    ms, mt = module_of(s), module_of(t)
    if ms != mt:
        mod_edges[(ms, mt)] += 1

with (root / "module_graph.dot").open("w") as f:
    f.write("digraph Modules {\n")
    f.write("  rankdir=LR;\n")
    f.write("  graph [overlap=false, splines=true, bgcolor=\"white\"];\n")
    f.write("  node [shape=box, style=\"rounded,filled\", fillcolor=\"#fff9f0\", color=\"#aa7a39\", fontname=\"Helvetica\", fontsize=12];\n")
    f.write("  edge [color=\"#8a8a8a\", arrowsize=0.7, fontname=\"Helvetica\", fontsize=10];\n")
    for n in sorted(mod_nodes):
        f.write(f"  \"{n}\";\n")
    for (s, t), w in sorted(mod_edges.items(), key=lambda x: (x[0][0], x[0][1])):
        f.write(f"  \"{s}\" -> \"{t}\" [label=\"{w}\"];\n")
    f.write("}\n")
PY

dot -Tsvg blueprint/dependency_graph.dot -o blueprint/dependency_graph.svg
dot -Tsvg blueprint/module_graph.dot -o blueprint/module_graph.svg

echo "Blueprint refreshed:"
wc -l blueprint/leanarchitect_nodes.txt blueprint/leanarchitect_edges.csv
