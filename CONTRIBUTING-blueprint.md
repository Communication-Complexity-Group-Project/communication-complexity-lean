# Blueprint Contribution Guide

This blueprint is organized by mathematical narrative, not Lean file layout.

## Structure

- Top-level ordering lives in `blueprint/src/content.tex`.
- Section content lives in `blueprint/src/sections/*.tex`.
- Logical mapping lives in `blueprint/src/manifest.yaml`.
- Formalized declaration list lives in `blueprint/lean_decls`.

## Rules for New Content

- Add content to an existing section file or create a new numbered section file.
- Keep stable logical labels (`\label{...}`) once published.
- Add `\lean{...}` tags for Lean declarations whenever available.
- Add or update an entry in `blueprint/src/manifest.yaml` for each new label.
- Use `status: planned` for declarations that are not yet in Lean.
- Move `planned` entries to `formalized` once declaration exists and add it to `blueprint/lean_decls`.

## Validation

Run:

```bash
scripts/check_blueprint_refs.sh
```

The check passes when each `\lean{...}` declaration is either:

- present in `blueprint/lean_decls`, or
- marked non-formalized (`planned`, etc.) in `blueprint/src/manifest.yaml`.
