# Reproduction of latest revision

Extract into an empty directory. Verify `sha256sum -c MANIFEST.sha256` before running code. Run `python verify_robustness.py` without `-O` (assertions are checks). Uses Python standard library and archived switch script.

Compile `pdflatex -interaction=nonstopmode -halt-on-error manuscript_v2.tex` twice. Original tests/Lean evidence and environment in REPRODUCE.md are preserved; no new Lean compile is claimed. Prior archive at `history/DEGREE_SEQUENCE_COMPARISON_PUBLIC_2026-11-26.zip`.
