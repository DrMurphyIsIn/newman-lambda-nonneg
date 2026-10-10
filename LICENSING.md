# Licensing

- `lean/`, `scripts/`, `.github/`: Apache License 2.0 (`LICENSE`), the licence of the Arda dbn island they are
  copied from. The copies are byte-identical to the Arda commit named in `provenance/ARDA_SOURCE`
  (`scripts/materialize.sh` checks this).
- `paper/`, `README.md`, `docs/`, `NOTICE.md`, `provenance/*.md`: Creative Commons Attribution 4.0 International
  (CC BY 4.0).
- `logs/`: GitHub Actions job transcripts, reproduced as records.
- `lean/statements/RHDefs.lean` is the Arda registry's vocabulary mirror (Apache-2.0); the island depends on
  nicholasbulka/li-criterion-rh-equivalence-lean (Apache-2.0) for one theorem (Hadamard's exp-polynomial
  theorem), fetched by Lake at build time and not vendored here.
- Mathlib is Apache-2.0 and is fetched by Lake; nothing of it is vendored.
