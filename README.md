# A degree-sensitive comparison of graphs and balanced digraphs

AI-assisted research manuscript (2026-11-26). Human authorship and affiliation pending verification; no claim of independent peer review, certified academic grade, or exhaustive priority.

This manuscript gives a self-contained combinatorial proof of Mehrdad's arXiv:2611.02191v1 Conjecture 1.1, with C=1, and the stronger explicit bound

`G(d)^2 <= D(d) <= 4^n G(d)^2 product_i max(1, min(d_i,n-1-d_i))`.

The right inequality assumes even total degree; the original conjecture assumes a graphical positive degree sequence. D counts loopless simple digraphs with equal in- and out-degrees, permitting antiparallel arcs. The key ingredients are single-tour transition-system counts and a component-local inverse code for the previously known parity repair. The half-factor comparison, BEST construction, and existence of the switching operation are credited as prior mathematics. The stronger polynomial-loss problem is not solved.

- `manuscript.pdf` / `manuscript.tex`: complete analytical proof and entropy/cut consequences.
- `PRIOR_ART.md`: comparison against the closest text and related literature, with access limitations.
- `ADVERSARIAL_AUDIT.md`: proof risks and scope.
- `verify_counts.py`, `replay_counts_dp.py`, `verify_switches.py`, `verify_tours.py`: exact checks; outputs and exit codes included.
- `DegreeCountCore.lean`, `lean_evidence/`: selected parity and algebraic kernels, compile evidence and retained initial draft.
- `REPRODUCE.md`, `ACCEPTANCE.json`, `MANIFEST.sha256`: reproduction and integrity information.

The article itself proves the general theorem. Finite tests and partial Lean compilation are separate supporting checks, not a substitute for the proof.
