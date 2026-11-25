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

## MLTT stage M0b

`Hard/Mltt.lean` is the verified first MLTT stage: the `Eq` `J` eliminator
typechecks with the index-refining `case` rule.

- Source: run `s0-mltt-j6`, agent `a1`, method `S0`.
- Size: 139 lines, one target.
- SHA-256: `dd9a8bb655cdb453186baec90d2cf6df692c6b08dbbb4d97ed9711334a98371b`.
- Check: `OK hard/mltt-j (1/1 targets)`, `solved=true`, `statement_ok=true`.
- Axioms: `propext`, `Quot.sound`.

This is a **stage proof**, not the contextual-equivalence theorem.

## MLTT stage M0c

`Hard/MlttWeaken.lean` proves weakening for the `Eq` family:

```lean
HasType [Eq_sig] Γ t A →
HasType [Eq_sig] (B :: Γ) (shift 1 0 t) (shift 1 0 A)
```

- Source: run `s0-mltt-weaken3`, agent `a1`, method `S0`.
- Size: 845 lines, one target.
- SHA-256: `b2624bccf2ee7466fe0cc49408e88cc307eed426c599445027eafb0de025b9c2`.
- Check: `OK hard/mltt-weaken (1/1 targets)`, `solved=true`, `statement_ok=true`.
- Axioms: `propext`, `Quot.sound`.


