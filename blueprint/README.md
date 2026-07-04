# The LeTrocq blueprint

A Mathlib-style [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)
document for LeTrocq. It restates the design of the library — the graded
parametricity translation (chapter 1) and the demand-driven witness solver
(chapter 2) — as definitions/lemmas/theorems, each tied to the Lean declaration
that realises it (`\lean{…}`), marked formalised (`\leanok`), and linked into a
dependency graph (`\uses{…}`).

It supersedes the prose in `DESIGN.md` and `bidir_solver.md`: the same content,
now checkable against the source and renderable as a PDF + web graph.

## Layout

```
blueprint/src/
  content.tex        the blueprint itself (the two chapters)
  macros/common.tex  notation + theorem-env declarations, shared by both builds
  macros/print.tex   pdf-only macros      macros/web.tex  web-only macros
  print.tex          pdf entry point      web.tex         web entry point
  plastex.cfg        plasTeX configuration for the web build
  latexmkrc          tells latexmk to use xelatex (for unicode-math)
  extra_styles.css   CSS tweaks for the web version
```

## Building

Requires a TeX distribution and the `leanblueprint` CLI (`pip install
leanblueprint`), which pulls in plasTeX and the `blueprint` LaTeX package. A TeX
install is needed for **both** targets: the pdf via xelatex, and the web build
for `\input` resolution (`kpsewhich`) and for rendering graph-node math to SVG
(`dvisvgm`). Run the commands **from the repository root** (leanblueprint reads
`blueprint/src/`):

```sh
leanblueprint pdf         # -> blueprint/print/print.pdf
leanblueprint web         # -> blueprint/web/  (dependency graph + hyperlinked html)
leanblueprint serve       # preview the web version locally
```

CI (`.github/workflows/docs.yml`) uses
[`leanprover-community/docgen-action`](https://github.com/leanprover-community/docgen-action)
with `blueprint: true`, which builds this blueprint alongside the doc-gen4 API
docs and deploys them to GitHub Pages on every push to `main` (other branches and
PRs validate the build only). The blueprint lands at `…/blueprint`, the API docs
at `…/docs`. Enable it once under *Settings → Pages → Source: GitHub Actions*.

### Verifying the `\lean{…}` links

`leanblueprint checkdecls` verifies every `\lean{…}` names a real declaration,
but it needs a `checkdecls` Lake dependency — which LeTrocq deliberately avoids
(the project depends on Lean core only). So it is **not** wired into CI. All 23
`\lean` targets were cross-checked against the source by hand when this was
written; re-check by grep after any refactor that renames a declaration, e.g.

```sh
grep -oP '\\lean\{[^}]*\}' blueprint/src/content.tex \
  | sed -E 's/\\lean\{//; s/\}//' | tr ',' '\n'   # then grep each in LeTrocq/
```

> Note: the scaffold matches the `leanblueprint` 1.9.x template. The web build
> (plasTeX) was verified to compile — both chapters render, every `\Cref`/`\uses`
> label resolves, and the dependency graph is populated. The pdf build wasn't run
> where this was authored (no LaTeX engine there), but the preamble is the stock
> `leanblueprint new` one plus `cleveref`.
