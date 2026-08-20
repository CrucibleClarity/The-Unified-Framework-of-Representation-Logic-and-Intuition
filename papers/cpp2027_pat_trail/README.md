# CPP 2027 Submission Package — An Empirical Trail to Formalized Pat Theory

## Paper

- `paper.tex` — ACM format (acmart), anonymous
- `refs.bib` — bibliography
- `pat_trail_paper.pdf` — compiled PDF (15 pages, article-class test build;
  acmart compile requires the ACM template)

Compile: `pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper`

## Content

Complete research trail record (2026-07-29 → 2026-08-16):

1. **Starting observation** — first generalization 2026-07-29 22:39:12 (UTC+8);
   first perfect generalization 2026-08-15 04:01 (all 19 operations OOD → 1.000);
   E12 two-pole pattern (training acc 1.000, OOD 0/32 ↔ 32/32, 45 runs reproduced);
   early first-successes recovered from the session log (07-29/07-30
   prefigurations: cross-class 90%/42.3%, logic-operator leave-one-out 90%,
   parallel-token verification 55% vs 90%, ≤ 47%→79%).
2. **Riemann direction (2026-08-06 → 08-12, C011–C025)** — visualization
   project delivered 08-06 17:55 (request 17:10; zeta landscape, critical
   line, prime positions ≤10⁸, bases 2–36 + complex bases, persisted data
   18:46 with RS fix 9e-4); user's thinking doc around 08-07 (primes have no
   construction / irrationals as projected remainders / basepoint drift on
   the circle around 1); Lean formalization session 08-12 00:00–02:54
   (PrimeDriftPositions → ComplexAxis → C011/C012 at 00:29 → C013–C025);
   published 08-12 (DOI 10.5281/zenodo.21896990 / 21897167 / 21896345).
3. **Homework-exercise series (2026-08-13 → 08-15)** — 25 reports (I–XXII +
   Pat0 + summary), each with Lean 0-sorry; exercise I (P vs NP) started
   08-13 14:19 with three user corrections in 27 minutes (14:24 positioning,
   14:31 no over-enumeration, 14:48 cite living scientists); 10 DOIs
   published 18:26–18:37; double-blind structure from exercise 14 (19:01);
   08-14 12:47 re-qualification as observation reports (no mathematical
   conclusion).
4. **Empirical trail E1–E18** — design reasons, procedures, results (20 scripts,
   15 result files in the referenced self-contained package); every experiment
   carries its first-success timestamp.
5. **Five structural laws** — anchor binding, notation translatability, shift
   invariance, structure-bearing representation, definition-layer invisibility.
6. **Framework mapping** — basepoint = anchor → R136 (paired direction
   declaration), R138 (phase locking), R143 (interlock matrix).
7. **Logical completeness theorem (08-15 09:14–09:47)** — decoupling operator
   D (R1 exclusion + R2 cancellation + R3 layering) ⟹ completeness at any
   order/element/subject-object; orthogonality-as-symmetry conjecture (I7t),
   double-declaration stability 5/5, two-symmetry-groups corollary (I7v,
   Cartan–Dieudonné), methodology paper; **three mapping-judgment theorems
   (08-16 16:16–16:23)** — symbol-norm / presentation-legality /
   intuition-precision (user correction 16:17), formalized in
   MappingJudgmentTheorems.lean (5 theorems, 0 sorry) with experiment-coverage
   matrix.
8. **Lean formalization** — R136–R153 all PROVED no sorry (2026-08-13 13:31);
   150+ Toolkit files, claims R001–R232; R150/R151/R163 continuum chain;
   3631 jobs lake build (mathlib v4.32.2).
9. **Timestamped evidence chain** — session records, 2303-turn task log,
   git history, file timestamps, Lean no-sorry timeline.
10. **Human corrections steering the API execution** — 15 documented corrections
   (08-12 09:44 Riemann referent, 11:08 attribution; 08-13 14:24/14:31/14:48
   exercise I; 08-15 09:14 completeness check + two-pole/token-level/stripping
   disciplines; 08-16 16:17 theorem positioning, 06:17 record format,
   06:18/06:21 attribution, timeline), each with session timestamp, marking
   which statements are the user's claims and which are the model's insistence.
11. **Reproducibility** — self-contained package (training one-command
   reproduction + pinned Lean build) + provenance methodology (SHA-256
   manifests, per-claim dual-repo publication with anonymization).

## Relationship to the self-contained package

The paper summarizes the trail recorded in full in the self-contained package
(`src/llm_research_v5/lab/paper_repro/selfcontained_zh/`): experiments
(`实验/all/scripts/`, 20 scripts), results (`结果/`, 15 files), timeline
(`记录/对话时间线.md`), observations (`观测/`, 25 reports), formalization
(`形式化/`, 150+ Lean files).

## Submission metadata

- **Title**: An Empirical Trail to Formalized Pat Theory: from 0/1 OOD
  Observations to Machine-Checked Theorems
- **Author**: Anonymous (double-blind)
- **Category**: CPP (Certified Programs and Proofs) — formalization / verification
- **Keywords**: Lean, formalization, transformer, OOD, basepoint, reproducibility

## Double-blind note

Paper and artifact contain no author / affiliation / email / DOI / repository
identifiers.
