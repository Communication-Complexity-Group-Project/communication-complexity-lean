#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TEX_DIR="$ROOT/blueprint/src"
LEAN_DECLS="$ROOT/blueprint/lean_decls"
MANIFEST="$ROOT/blueprint/src/manifest.yaml"

if [[ ! -f "$LEAN_DECLS" ]]; then
  echo "missing file: $LEAN_DECLS" >&2
  exit 1
fi

if [[ ! -f "$MANIFEST" ]]; then
  echo "missing file: $MANIFEST" >&2
  exit 1
fi

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

rg --files "$TEX_DIR" -g '*.tex' | sort > "$tmpdir/tex_files"

if [[ ! -s "$tmpdir/tex_files" ]]; then
  echo "no tex files found under $TEX_DIR" >&2
  exit 1
fi

# shellcheck disable=SC2046
rg --no-filename -oN '\\lean\{[^}]+\}' $(cat "$tmpdir/tex_files") \
  | sed -E 's/^\\lean\{([^}]+)\}$/\1/' \
  | sort -u > "$tmpdir/blueprint_decls"

sort -u "$LEAN_DECLS" > "$tmpdir/known_decls"

awk '
  $1 == "-" && $2 == "id:" {decl=""; status=""}
  $1 == "lean_decl:" {decl=$2}
  $1 == "status:" {status=$2; if (decl != "" && status != "formalized") print decl}
' "$MANIFEST" | sort -u > "$tmpdir/non_formalized_decls"

missing=0
while IFS= read -r decl; do
  [[ -z "$decl" ]] && continue
  if grep -Fxq "$decl" "$tmpdir/known_decls"; then
    continue
  fi
  if grep -Fxq "$decl" "$tmpdir/non_formalized_decls"; then
    continue
  fi
  echo "missing declaration in blueprint/lean_decls (or mark non-formalized in manifest): $decl" >&2
  missing=1
done < "$tmpdir/blueprint_decls"

if [[ $missing -ne 0 ]]; then
  exit 1
fi

count="$(wc -l < "$tmpdir/blueprint_decls" | tr -d '[:space:]')"
echo "blueprint refs check passed ($count declarations)."
