import Problems.Hard.Mltt

/-!
# MLTT stage M0c: weakening

The first held-out stage after the `J` typing proof.  Adding an unused
context binder shifts both the term and its type; this must preserve typing.
-/

namespace Problems.Hard.MlttWeaken

open Problems.Hard.Mltt

def hasType_weaken : Prop :=
  ∀ {env : Env} {Γ : Ctx} {A B : Tm} {t : Tm},
    HasType env Γ t A →
    HasType env (B :: Γ) (Tm.shift 1 0 t) (Tm.shift 1 0 A)

end Problems.Hard.MlttWeaken
