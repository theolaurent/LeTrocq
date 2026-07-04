---
# The landing page. The header buttons (Blueprint web/pdf, Documentation, GitHub) come from the
# layout in _layouts/default.html; this body adds a short description and the dependency-graph link.
layout: default
usemathjax: true
---

**LeTrocq** is a Lean-native, *graded* reformulation of the
[Trocq](https://arxiv.org/abs/2310.14022) parametricity / proof-transfer framework
(Cohen–Crance–Mahboubi), in the no-univalence fragment. Register an equivalence between two types
once, and LeTrocq automatically transports types, terms, and goals across it — generating verified
`Param` witnesses whose transport maps compute.

It is **library-agnostic** (no dependencies beyond Lean core; even `Nat`/`List`/`Quot` are ordinary
`@[trocq]` registrations) and **predictable** (transfer is a single deterministic top-down pass — no
typeclass resolution, no backtracking, no fixpoint).

Useful links:

* [Blueprint]({{ site.url }}/blueprint/) — the design, each result tied to its Lean declaration
* [Blueprint as PDF]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [GitHub repository]({{ site.github.repository_url }})

{% comment %} API docs disabled (api-docs: false in docs.yml); re-enable there to restore:
* [API documentation]({{ site.url }}/docs/) {% endcomment %}
