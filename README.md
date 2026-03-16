# CommunicationComplexity

## LeanArchitect Blueprint

This project now includes a LeanArchitect blueprint overlay at
`CommunicationComplexity/Blueprint.lean` that tags major public definitions
and theorems with `@[blueprint]`.

Run:

```bash
lake build :blueprint
lake build :blueprintJson
```

Generated outputs:

- `.lake/build/blueprint/library/CommunicationComplexity.tex`
- `.lake/build/blueprint/library/CommunicationComplexity.json`
- `.lake/build/blueprint/module/CommunicationComplexity/Blueprint.tex`
- `.lake/build/blueprint/module/CommunicationComplexity/Blueprint.json`

Derived relationship files (from `\uses{...}` in artifact tex files):

- `blueprint/leanarchitect_nodes.txt` (one node per line)
- `blueprint/leanarchitect_edges.csv` (`source,target` dependency edges)

### Updating After `main` Changes

After pulling latest `main`, rerun:

```bash
scripts/update_blueprint.sh
```

This regenerates:

- LeanArchitect `.tex` and `.json` outputs under `.lake/build/blueprint/...`
- `blueprint/leanarchitect_nodes.txt`
- `blueprint/leanarchitect_edges.csv`
- `blueprint/module_graph.svg`
- `blueprint/dependency_graph.svg`

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
