# CPP 2027 Submission — 0pat Exercise XXIX: Observing the Intersections of the Complex Plane's Four Objects

## Paper

- Exercise_XXIX_Complex_Plane_Intersections.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXIX_Complex_Plane_Intersections.tex`

## Content

Complete intersection table of the Riemann direction's four objects (all machine-checked):
- real axis ∩ critical circle = {0, 2} (C020); imaginary axis ∩ critical circle = {0}
- real axis ∩ prime circle p = {±√p}; imaginary axis ∩ prime circle p = {±i√p}
- prime-2 circle ∩ critical circle = {1±i} (C020); prime-3 circle ∩ critical circle = {3/2±√3/2·i}
- NEW structural theorem: prime circle p ≥ 5 is disjoint from the critical circle
  (a = p/2, b² = p(4−p)/4 < 0) — intersection iff p ∈ {2, 3}
- 5 theorems, 0 errors, 0 sorry

## Artifact

- artifact/formal/proof.lean — the 5-theorem proof (108 lines, imports ComplexAxis C011)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
