# Credibility Bootstrap: A Verification-Map Discipline for Independent Formalization Authors

> A short methodological note accompanying *Empirical Foundations of
> Pat* (CPP 2027 submission package). Why a verification map belongs
> on the first page when the author has no academic identity to
> vouch for the work.

## The problem: no academic identity

A Princeton professor submitting *A Proof of the Riemann Hypothesis*
is read in a specific way: the editor knows the author's research
background, and that background is part of the submission's
credibility. An Independent Researcher submitting the same title is
read differently: the editor does not know who the author is. The
difference is not about the rules of submission — anyone can submit.
The difference is **credibility bootstrap**: the manuscript itself
must carry the credibility that an institutional identity would
otherwise supply.

## The mechanism: make the manuscript carry its own proof of trust

For a formalization paper there is a mechanical way to do this. The
first page should carry a **verification map** that lays out, in a
table, exactly what a referee has to check:

| Element | Content |
|---|---|
| Main Theorem | the precise statement, corresponding to the standard conjecture/theorem it claims |
| Assumptions / Axioms | explicitly listed, verified by `#print axioms` (e.g. `propext`, `Classical.choice`, `Quot.sound`) |
| Core new lemma chain | claim id + content + Lean file + theorem name, one row per link |
| Proof dependency graph | node tree, acyclic, no unmarked edges |
| Lean theorem names | file:theorem for every link of the chain |
| Repository / version | archive location + toolchain version + build job count |

The map turns the editorial question from *"should I trust this
author?"* into *"is this proof object worth sending to an expert
checker?"* The referee does not need to trust the author; they only
need to check whether each node of the map is what it claims to be —
open the file, run the build, count the `sorry`s.

## Why this is especially important for independent authors

A verification map is useful for every formalization paper, but for
an independent author it is not optional:

1. **It replaces reputation with mechanism.** The author cannot
   offer a track record, so the paper offers a machine-checked
   artifact instead. The proof object is the reputation.
2. **It makes the honest boundary visible.** Gaps must be marked
   (CONJ for conjectures, unproved links stated in full precision).
   For an unknown author, an *unmarked* gap is fatal; a *marked* gap
   is a sign of discipline.
3. **It is cheap to check.** Every claim of the map is verifiable in
   minutes (run `lake build`, open the file, read the statement).
   The editor's decision cost is low, so the decision can be about
   the work rather than the author.

## The discipline behind it

The verification-map discipline is part of a larger rule set for
anonymous submission:

- **No identity in the artifact.** No author, affiliation, email,
  DOI, repository identifier, or local path in the paper or the
  artifact. (This note itself is written without identity.)
- **No overclaiming.** Claims carry `novelty_status` (KNOWN /
  NOVELTY_UNASSESSED); classical components are marked KNOWN; the
  empirical-to-formalization correspondence is labeled observational,
  not deductive.
- **No unmarked gaps.** Anything not machine-checked is either out of
  scope or stated as a conjecture with its precise shape.

## How this note's companion paper applies it

*Empirical Foundations of Pat* is an independent-researcher
submission. Its first page carries a verification map: twenty-two
Lean theorems (zero `sorry`), the interlock matrix
($\det = \theta \cdot (r + 1/r) \neq 0$) through the four-phase
interlock, the countable pat grid, and the continuum closure
theorems; toolchain pinned (Lean 4.32.2 + mathlib v4.32.2); the
full artifact in the submission package with build commands. The
paper also records an originality boundary: the research was
conducted through an API, the model capability has been distilled,
the conflict scope cannot be confirmed, and originality is evidenced
only by session logs and git backup timestamps. That boundary is
itself part of the credibility mechanism — a referee who knows
exactly what the paper does and does not claim can check the
artifact without needing to trust anyone.

*The verification map does not make a paper important. It makes a
paper checkable — and for an author without a name, checkability is
the only available form of credibility.*
