# Verified proofs

`Hard/Pcf.lean` is the verified **12/12** solution to `Problems/Hard/Pcf.lean`.

- Source: run `s7-pcf-final`, lane `a3` (level-free logical relation).
- Size: 2002 lines, 161 declarations.
- SHA-256: `1938e7f827574545cfbc1b7cfdfa4442c613331d27e0d71219eb056528dfb0c5`.
- Check: `OK hard/pcf (12/12 targets)`, `solved=true`, `statement_ok=true`,
  no forbidden constructs, no `sorryAx`.
- Axioms: `propext` and `Quot.sound` on the targets that need them; no other
  axioms.

This is a **reference solution**. A run environment is built from its own
`Proofs/` skeleton and does not copy this directory; an agent must not read it
during a run. It exists so the result is not lost with the transient run
directory.
