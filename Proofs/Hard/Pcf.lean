import Problems.Hard.Pcf

/- Targets for `hard/pcf`. -/

namespace Problems.Hard.Pcf

/-! ## The empty variable context -/

theorem var_nil {σ : Ty} (v : Var [] σ) : False := by cases v

/-! ## Renaming: lifting lemmas -/

theorem liftRen_congr {Γ Δ : List Ty} {τ : Ty}
    {ρ ρ' : ∀ {σ}, Var Γ σ → Var Δ σ} (h : ∀ {σ} (v : Var Γ σ), ρ v = ρ' v)
    {σ : Ty} (v : Var (τ :: Γ) σ) : liftRen ρ v = liftRen ρ' v := by
  cases v with
  | here => rfl
  | there w => show Var.there (ρ w) = Var.there (ρ' w); rw [h w]

theorem liftRen_id {Γ : List Ty} {τ : Ty} {σ : Ty} (v : Var (τ :: Γ) σ) :
    liftRen (fun {υ} (x : Var Γ υ) => x) v = v := by
  cases v with
  | here => rfl
  | there w => rfl

theorem liftRen_comp {Γ Δ Ε : List Ty} {τ : Ty}
    (ρ : ∀ {σ}, Var Γ σ → Var Δ σ) (ρ' : ∀ {σ}, Var Δ σ → Var Ε σ)
    {σ : Ty} (v : Var (τ :: Γ) σ) :
    liftRen ρ' (liftRen ρ v) = liftRen (fun {υ} (x : Var Γ υ) => ρ' (ρ x)) v := by
  cases v with
  | here => rfl
  | there w => rfl

/-! ## Renaming: congruence, composition, identity -/

theorem rename_congr {Γ Δ : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → (ρ ρ' : ∀ {σ}, Var Γ σ → Var Δ σ) →
    (∀ {σ} (v : Var Γ σ), ρ v = ρ' v) → rename ρ t = rename ρ' t
  | .var v, ρ, ρ', h => by
      show Tm.var (ρ v) = Tm.var (ρ' v)
      rw [h v]
  | .lam b, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr b (liftRen ρ) (liftRen ρ') (liftRen_congr h)]
  | .app f a, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr f ρ ρ' h, rename_congr a ρ ρ' h]
  | .zero, _, _, _ => rfl
  | .succ x, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr x ρ ρ' h]
  | .pred x, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr x ρ ρ' h]
  | .ifz n x e, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr n ρ ρ' h, rename_congr x ρ ρ' h, rename_congr e ρ ρ' h]
  | .tt, _, _, _ => rfl
  | .ff, _, _, _ => rfl
  | .cond c x e, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr c ρ ρ' h, rename_congr x ρ ρ' h, rename_congr e ρ ρ' h]
  | .fix f, ρ, ρ', h => by
      simp only [rename]
      rw [rename_congr f ρ ρ' h]

theorem rename_rename {Γ Δ Ε : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → (ρ : ∀ {σ}, Var Γ σ → Var Δ σ) →
    (ρ' : ∀ {σ}, Var Δ σ → Var Ε σ) →
    rename ρ' (rename ρ t) = rename (fun {σ} (v : Var Γ σ) => ρ' (ρ v)) t
  | .var v, ρ, ρ' => rfl
  | .lam b, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename b (liftRen ρ) (liftRen ρ')]
      exact congrArg Tm.lam (rename_congr b (fun v => liftRen ρ' (liftRen ρ v))
        (liftRen (fun v => ρ' (ρ v))) (fun {σ} v => liftRen_comp ρ ρ' v))
  | .app f a, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename f ρ ρ', rename_rename a ρ ρ']
  | .zero, _, _ => rfl
  | .succ x, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename x ρ ρ']
  | .pred x, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename x ρ ρ']
  | .ifz n x e, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename n ρ ρ', rename_rename x ρ ρ', rename_rename e ρ ρ']
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .cond c x e, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename c ρ ρ', rename_rename x ρ ρ', rename_rename e ρ ρ']
  | .fix f, ρ, ρ' => by
      simp only [rename]
      rw [rename_rename f ρ ρ']

theorem rename_id {Γ : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → rename (fun {σ} (v : Var Γ σ) => v) t = t
  | .var v => rfl
  | .lam b => by
      simp only [rename]
      rw [rename_congr b (liftRen (fun {σ} (v : Var _ σ) => v))
            (fun {σ} (v : Var _ σ) => v) (fun {σ} v => liftRen_id v), rename_id b]
  | .app f a => by
      simp only [rename]
      rw [rename_id f, rename_id a]
  | .zero => rfl
  | .succ x => by
      simp only [rename]
      rw [rename_id x]
  | .pred x => by
      simp only [rename]
      rw [rename_id x]
  | .ifz n x e => by
      simp only [rename]
      rw [rename_id n, rename_id x, rename_id e]
  | .tt => rfl
  | .ff => rfl
  | .cond c x e => by
      simp only [rename]
      rw [rename_id c, rename_id x, rename_id e]
  | .fix f => by
      simp only [rename]
      rw [rename_id f]

/-! ## Substitution: lifting lemmas -/

theorem liftSubst_var {Γ : List Ty} {τ : Ty} {σ : Ty} (v : Var (τ :: Γ) σ) :
    liftSubst (fun {υ} (x : Var Γ υ) => Tm.var x) v = Tm.var v := by
  cases v with
  | here => rfl
  | there w => rfl

theorem liftSubst_congr {Γ Δ : List Ty} {τ : Ty}
    {f f' : ∀ {σ}, Var Γ σ → Tm Δ σ} (h : ∀ {σ} (v : Var Γ σ), f v = f' v)
    {σ : Ty} (v : Var (τ :: Γ) σ) : liftSubst f v = liftSubst f' v := by
  cases v with
  | here => rfl
  | there w =>
      simp only [liftSubst]
      rw [h w]

theorem liftSubst_liftRen {Γ Δ Ε : List Ty} {τ : Ty}
    (ρ : ∀ {σ}, Var Γ σ → Var Δ σ) (f : ∀ {σ}, Var Δ σ → Tm Ε σ)
    {σ : Ty} (v : Var (τ :: Γ) σ) :
    liftSubst f (liftRen ρ v) = liftSubst (fun {υ} (x : Var Γ υ) => f (ρ x)) v := by
  cases v with
  | here => rfl
  | there w => rfl

theorem liftRen_liftSubst {Γ Δ Ε : List Ty} {τ : Ty}
    (f : ∀ {σ}, Var Γ σ → Tm Δ σ) (ρ : ∀ {σ}, Var Δ σ → Var Ε σ)
    {σ : Ty} (v : Var (τ :: Γ) σ) :
    rename (liftRen ρ) (liftSubst f v) =
      liftSubst (fun {υ} (x : Var Γ υ) => rename ρ (f x)) v := by
  cases v with
  | here => rfl
  | there w =>
      simp only [liftSubst]
      rw [rename_rename, rename_rename]
      rfl

/-! ## Substitution: congruence and identity -/

theorem subst_congr {Γ Δ : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → (f f' : ∀ {σ}, Var Γ σ → Tm Δ σ) →
    (∀ {σ} (v : Var Γ σ), f v = f' v) → subst f t = subst f' t
  | .var v, _, _, h => by
      show _ = _
      exact h v
  | .lam b, f, f', h => by
      simp only [subst]
      rw [subst_congr b (liftSubst f) (liftSubst f') (liftSubst_congr h)]
  | .app x y, f, f', h => by
      simp only [subst]
      rw [subst_congr x f f' h, subst_congr y f f' h]
  | .zero, _, _, _ => rfl
  | .succ x, f, f', h => by
      simp only [subst]
      rw [subst_congr x f f' h]
  | .pred x, f, f', h => by
      simp only [subst]
      rw [subst_congr x f f' h]
  | .ifz n x e, f, f', h => by
      simp only [subst]
      rw [subst_congr n f f' h, subst_congr x f f' h, subst_congr e f f' h]
  | .tt, _, _, _ => rfl
  | .ff, _, _, _ => rfl
  | .cond c x e, f, f', h => by
      simp only [subst]
      rw [subst_congr c f f' h, subst_congr x f f' h, subst_congr e f f' h]
  | .fix x, f, f', h => by
      simp only [subst]
      rw [subst_congr x f f' h]

theorem subst_id {Γ : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → subst (fun {σ} (v : Var Γ σ) => Tm.var v) t = t
  | .var v => rfl
  | .lam b => by
      simp only [subst]
      rw [subst_congr b (liftSubst (fun {σ} (v : Var _ σ) => Tm.var v))
            (fun {σ} (v : Var _ σ) => Tm.var v) (fun {σ} v => liftSubst_var v),
        subst_id b]
  | .app x y => by
      simp only [subst]
      rw [subst_id x, subst_id y]
  | .zero => rfl
  | .succ x => by
      simp only [subst]
      rw [subst_id x]
  | .pred x => by
      simp only [subst]
      rw [subst_id x]
  | .ifz n x e => by
      simp only [subst]
      rw [subst_id n, subst_id x, subst_id e]
  | .tt => rfl
  | .ff => rfl
  | .cond c x e => by
      simp only [subst]
      rw [subst_id c, subst_id x, subst_id e]
  | .fix x => by
      simp only [subst]
      rw [subst_id x]

/-! ## Substitution: composition -/

theorem subst_rename {Γ Δ Ε : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → (ρ : ∀ {σ}, Var Γ σ → Var Δ σ) →
    (f : ∀ {σ}, Var Δ σ → Tm Ε σ) →
    subst f (rename ρ t) = subst (fun {σ} (v : Var Γ σ) => f (ρ v)) t
  | .var v, ρ, f => rfl
  | .lam b, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename b (liftRen ρ) (liftSubst f)]
      exact congrArg Tm.lam (subst_congr b (fun v => liftSubst f (liftRen ρ v)) _
        (fun {σ} v => liftSubst_liftRen ρ f v))
  | .app x y, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename x ρ f, subst_rename y ρ f]
  | .zero, _, _ => rfl
  | .succ x, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename x ρ f]
  | .pred x, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename x ρ f]
  | .ifz n x e, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename n ρ f, subst_rename x ρ f, subst_rename e ρ f]
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .cond c x e, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename c ρ f, subst_rename x ρ f, subst_rename e ρ f]
  | .fix x, ρ, f => by
      simp only [rename, subst]
      rw [subst_rename x ρ f]

theorem rename_subst {Γ Δ Ε : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → (f : ∀ {σ}, Var Γ σ → Tm Δ σ) →
    (ρ : ∀ {σ}, Var Δ σ → Var Ε σ) →
    rename ρ (subst f t) = subst (fun {σ} (v : Var Γ σ) => rename ρ (f v)) t
  | .var v, f, ρ => rfl
  | .lam b, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst b (liftSubst f) (liftRen ρ)]
      exact congrArg Tm.lam (subst_congr b (fun v => rename (liftRen ρ) (liftSubst f v)) _
        (fun {σ} v => liftRen_liftSubst f ρ v))
  | .app x y, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst x f ρ, rename_subst y f ρ]
  | .zero, _, _ => rfl
  | .succ x, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst x f ρ]
  | .pred x, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst x f ρ]
  | .ifz n x e, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst n f ρ, rename_subst x f ρ, rename_subst e f ρ]
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .cond c x e, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst c f ρ, rename_subst x f ρ, rename_subst e f ρ]
  | .fix x, f, ρ => by
      simp only [rename, subst]
      rw [rename_subst x f ρ]

theorem liftSubst_liftSubst {Γ Δ Ε : List Ty} {τ : Ty}
    (f : ∀ {σ}, Var Γ σ → Tm Δ σ) (g : ∀ {σ}, Var Δ σ → Tm Ε σ)
    {σ : Ty} (v : Var (τ :: Γ) σ) :
    subst (liftSubst g) (liftSubst f v) =
      liftSubst (fun {υ} (x : Var Γ υ) => subst g (f x)) v := by
  cases v with
  | here => rfl
  | there w =>
      simp only [liftSubst]
      rw [subst_rename, rename_subst]
      rfl

theorem subst_subst {Γ Δ Ε : List Ty} {τ : Ty} :
    (t : Tm Γ τ) → (f : ∀ {σ}, Var Γ σ → Tm Δ σ) →
    (g : ∀ {σ}, Var Δ σ → Tm Ε σ) →
    subst g (subst f t) = subst (fun {σ} (v : Var Γ σ) => subst g (f v)) t
  | .var v, f, g => rfl
  | .lam b, f, g => by
      simp only [subst]
      rw [subst_subst b (liftSubst f) (liftSubst g)]
      exact congrArg Tm.lam (subst_congr b (fun v => subst (liftSubst g) (liftSubst f v)) _
        (fun {σ} v => liftSubst_liftSubst f g v))
  | .app x y, f, g => by
      simp only [subst]
      rw [subst_subst x f g, subst_subst y f g]
  | .zero, _, _ => rfl
  | .succ x, f, g => by
      simp only [subst]
      rw [subst_subst x f g]
  | .pred x, f, g => by
      simp only [subst]
      rw [subst_subst x f g]
  | .ifz n x e, f, g => by
      simp only [subst]
      rw [subst_subst n f g, subst_subst x f g, subst_subst e f g]
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .cond c x e, f, g => by
      simp only [subst]
      rw [subst_subst c f g, subst_subst x f g, subst_subst e f g]
  | .fix x, f, g => by
      simp only [subst]
      rw [subst_subst x f g]

/-! ## Weakening -/

def weaken {Γ : List Ty} {σ : Ty} (t : Tm [] σ) : Tm Γ σ :=
  subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) t

theorem subst_weaken {Γ : List Ty} {σ τ : Ty} (x : Tm [] σ) (y : Tm Γ τ) :
    subst (substHere y) (weaken (Γ := τ :: Γ) x) = weaken (Γ := Γ) x := by
  show subst (substHere y) (subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) x)
      = subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) x
  calc subst (substHere y) (subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) x)
      = subst (fun {υ} (v : Var [] υ) =>
          subst (substHere y) ((fun {ω} (w : Var [] ω) => (var_nil w).elim) v)) x :=
        subst_subst x _ _
    _ = subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) x :=
        subst_congr x _ _ (fun {ω} v => (var_nil v).elim)

theorem weaken_nil {σ : Ty} (x : Tm [] σ) : weaken (Γ := []) x = x := by
  show subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) x = x
  calc subst (fun {ω} (v : Var [] ω) => (var_nil v).elim) x
      = subst (fun {ω} (v : Var [] ω) => Tm.var v) x :=
        subst_congr x _ _ (fun {ω} v => (var_nil v).elim)
    _ = x := subst_id x

/-! ## Context composition -/

/-- Substitution for the hole in a one-hole context, filling it with a term
that may itself have a free variable. -/
def substHereCtx {Γ : List Ty} {σ : Ty} (a : Tm Γ σ) :
    ∀ {τ : Ty}, Var (σ :: []) τ → Tm Γ τ
  | _, .here => a
  | _, .there w => (var_nil w).elim

/-- Compose a one-hole context with a hole-filling term that may have a free
variable of its own. -/
def substCtx {σ τ υ : Ty} (D : Tm [τ] υ) (x : Tm [σ] τ) : Tm [σ] υ :=
  subst (substHereCtx x) D

theorem plug_substCtx {σ τ υ : Ty} (D : Tm [τ] υ) (x : Tm [σ] τ)
    (t : Tm [] σ) :
    plug (substCtx D x) t = plug D (plug x t) := by
  show subst (substHere t) (subst (substHereCtx x) D) =
    subst (substHere (subst (substHere t) x)) D
  rw [subst_subst]
  exact subst_congr D _ _ (fun {ω} v => by
    cases v with
    | here => rfl
    | there w => exact (var_nil w).elim)

/-- The context `(λ.D) □`, whose plugging of `t` is `(λ.D) t`. -/
theorem plug_lam_ctx {σ τ : Ty} (D : Tm [σ] τ) (t : Tm [] σ) :
    plug (Tm.app (weaken (Γ := [σ]) (Tm.lam D)) (Tm.var Var.here)) t =
      Tm.app (Tm.lam D) t := by
  show Tm.app (subst (substHere t) (weaken (Γ := [σ]) (Tm.lam D)))
      (subst (substHere t) (Tm.var Var.here)) = Tm.app (Tm.lam D) t
  rw [subst_weaken, weaken_nil]
  rfl

/-- The context `□ a`, whose plugging of `t` is `t a`. -/
theorem plug_app_ctx {σ τ : Ty} (t : Tm [] (Ty.arr σ τ)) (a : Tm [] σ) :
    plug (Tm.app (Tm.var Var.here) (weaken (Γ := [Ty.arr σ τ]) a)) t =
      Tm.app t a := by
  show Tm.app (subst (substHere t) (Tm.var Var.here))
      (subst (substHere t) (weaken (Γ := [Ty.arr σ τ]) a)) = Tm.app t a
  rw [subst_weaken, weaken_nil]
  rfl

/-! ## Values do not step -/

theorem value_no_step {σ : Ty} {v : Tm [] σ} (hv : Value v) :
    ∀ {w : Tm [] σ}, Step v w → False := by
  induction hv with
  | zero => intro w h; cases h
  | tt => intro w h; cases h
  | ff => intro w h; cases h
  | lam => intro w h; cases h
  | succ hv' ih => intro w h; cases h with
      | succ h' => exact ih h'

/-! ## Single-step determinism -/

theorem step_det {σ : Ty} {t u : Tm [] σ} (h : Step t u) :
    ∀ {v : Tm [] σ}, Step t v → u = v := by
  induction h with
  | succ ht ih =>
      intro v hv
      cases hv with
      | succ hv' => rw [ih hv']
  | pred_zero =>
      intro v hv
      cases hv with
      | pred_zero => rfl
      | pred h' => nomatch h'
  | pred_succ val =>
      intro v hv
      cases hv with
      | pred_succ _ => rfl
      | pred h' =>
          cases h' with
          | succ h'' => exact (value_no_step val h'').elim
  | pred ht ih =>
      intro v hv
      cases hv with
      | pred_zero => nomatch ht
      | pred_succ val =>
          cases ht with
          | succ ht' => exact (value_no_step val ht').elim
      | pred hv' => rw [ih hv']
  | ifz_zero =>
      intro v hv
      cases hv with
      | ifz_zero => rfl
      | ifz h' => nomatch h'
  | ifz_succ val =>
      intro v hv
      cases hv with
      | ifz_succ _ => rfl
      | ifz h' =>
          cases h' with
          | succ h'' => exact (value_no_step val h'').elim
  | ifz ht ih =>
      intro v hv
      cases hv with
      | ifz_zero => nomatch ht
      | ifz_succ val =>
          cases ht with
          | succ ht' => exact (value_no_step val ht').elim
      | ifz hv' => rw [ih hv']
  | cond_tt =>
      intro v hv
      cases hv with
      | cond_tt => rfl
      | cond h' => nomatch h'
  | cond_ff =>
      intro v hv
      cases hv with
      | cond_ff => rfl
      | cond h' => nomatch h'
  | cond ht ih =>
      intro v hv
      cases hv with
      | cond_tt => nomatch ht
      | cond_ff => nomatch ht
      | cond hv' => rw [ih hv']
  | app_lam val =>
      intro v hv
      cases hv with
      | app_lam _ => rfl
      | app_fun h' => exact (value_no_step .lam h').elim
      | app_arg _ h' => exact (value_no_step val h').elim
  | app_fun ht ih =>
      intro v hv
      cases hv with
      | app_lam val => exact (value_no_step .lam ht).elim
      | app_fun hv' => rw [ih hv']
      | app_arg val _ => exact (value_no_step val ht).elim
  | app_arg val ht ih =>
      intro v hv
      cases hv with
      | app_lam va => exact (value_no_step va ht).elim
      | app_fun h' => exact (value_no_step val h').elim
      | app_arg _ hv' => rw [ih hv']
  | fix =>
      intro v hv
      cases hv with
      | fix => rfl

/-! ## Reduction sequences -/

theorem steps_app_fun {σ τ : Ty} {f f' : Tm [] (Ty.arr σ τ)} (a : Tm [] σ)
    (h : Steps f f') : Steps (Tm.app f a) (Tm.app f' a) := by
  induction h with
  | refl => exact .refl _
  | step h1 h2 ih => exact .step ih (.app_fun h2)

theorem steps_app_arg {σ τ : Ty} {f : Tm [] (Ty.arr σ τ)} (hf : Value f)
    {a a' : Tm [] σ} (h : Steps a a') : Steps (Tm.app f a) (Tm.app f a') := by
  induction h with
  | refl => exact .refl _
  | step h1 h2 ih => exact .step ih (.app_arg hf h2)

theorem steps_head {σ : Ty} {t v : Tm [] σ} (h : Steps t v) :
    t = v ∨ ∃ u, Step t u ∧ Steps u v := by
  induction h with
  | refl => exact Or.inl rfl
  | step h1' hstep ih =>
      rcases ih with heq | ⟨u, htu, hus⟩
      · subst heq
        exact Or.inr ⟨_, hstep, .refl _⟩
      · exact Or.inr ⟨u, htu, .step hus hstep⟩

theorem steps_value_self {σ : Ty} {t : Tm [] σ} (hv : Value t) :
    ∀ {w : Tm [] σ}, Steps t w → w = t := by
  intro w h
  induction h with
  | refl => rfl
  | step h' hstep ih =>
      rw [ih] at hstep
      exact (value_no_step hv hstep).elim

theorem steps_prefix {σ : Ty} {t v : Tm [] σ} (h1 : Steps t v)
    {w : Tm [] σ} (h2 : Steps t w) : Steps v w ∨ Steps w v := by
  induction h1 with
  | refl => exact Or.inl h2
  | step h1' hstep ih =>
      rcases ih with h | h
      · rcases steps_head h with rfl | ⟨y, hmy, hys⟩
        · exact Or.inr (Steps.step (Steps.refl _) hstep)
        · have hvy : _ = y := step_det hstep hmy
          rw [hvy] at *
          exact Or.inl hys
      · exact Or.inr (Steps.step h hstep)

theorem steps_det_value {σ : Ty} {t v : Tm [] σ} (h1 : Steps t v) (hv : Value v)
    {w : Tm [] σ} (h2 : Steps t w) (hw : Value w) : v = w := by
  rcases steps_prefix h1 h2 with h | h
  · exact (steps_value_self hv h).symm
  · exact steps_value_self hw h

theorem steps_trans_aux {σ : Ty} {t u v : Tm [] σ} (h1 : Steps t u) (h2 : Steps u v) :
    Steps t v := by
  induction h2 with
  | refl => exact h1
  | step _ hstep ih => exact .step ih hstep

/-! ## Targets -/

theorem step_deterministic_proof : step_deterministic := by
  intro σ t u v h1 h2
  exact step_det h1 h2

theorem steps_trans_proof : steps_trans := by
  intro σ t u v h1 h2
  exact steps_trans_aux h1 h2

theorem contextual_le_plug_proof : contextual_le_plug := by
  intro σ τ C t u h υ D hTerm
  have key : Terminates (plug (substCtx D C) u) :=
    h (substCtx D C) (by rwa [← plug_substCtx] at hTerm)
  rwa [plug_substCtx] at key

theorem contextual_le_value_proof : contextual_le_value := by
  intro σ t u v v' h hv hsteps hv' hsteps' τ D hTerm
  obtain ⟨w, hw, hws⟩ := hTerm
  have key : Steps (plug (Tm.app (weaken (Γ := [σ]) (Tm.lam D)) (Tm.var Var.here))
      t) w := by
    rw [plug_lam_ctx]
    exact steps_trans_aux (steps_app_arg .lam hsteps)
      (steps_trans_aux (Steps.step (Steps.refl _) (Step.app_lam hv)) hws)
  obtain ⟨w', hw', hws'⟩ :=
    h (Tm.app (weaken (Γ := [σ]) (Tm.lam D)) (Tm.var Var.here)) ⟨w, hw, key⟩
  refine ⟨w', hw', ?_⟩
  rw [plug_lam_ctx] at hws'
  have h2 : Steps (Tm.app (Tm.lam D) u) (plug D v') :=
    steps_trans_aux (steps_app_arg .lam hsteps')
      (Steps.step (Steps.refl _) (Step.app_lam hv'))
  rcases steps_prefix h2 hws' with hh | hh
  · exact hh
  · rw [steps_value_self hw' hh]
    exact .refl _

theorem contextual_le_app_proof : contextual_le_app := by
  intro σ τ t u a h υ D hTerm
  have hT : Terminates (plug (substCtx D (Tm.app (Tm.var Var.here)
      (weaken (Γ := [Ty.arr σ τ]) a))) t) := by
    rw [← plug_app_ctx, ← plug_substCtx] at hTerm
    exact hTerm
  have key : Terminates (plug (substCtx D (Tm.app (Tm.var Var.here)
      (weaken (Γ := [Ty.arr σ τ]) a))) u) :=
    h (substCtx D (Tm.app (Tm.var Var.here)
      (weaken (Γ := [Ty.arr σ τ]) a))) hT
  have key' : Terminates (plug D (plug (Tm.app (Tm.var Var.here)
      (weaken (Γ := [Ty.arr σ τ]) a)) u)) := by
    rw [← plug_substCtx]
    exact key
  rwa [plug_app_ctx] at key'

theorem sim_refl_proof : sim_refl := by
  intro σ t
  refine ⟨fun {υ} (x y : Tm [] υ) => x = y, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b h v hv hs
    exact ⟨v, hv, h ▸ hs, rfl⟩
  · intro a b h v hv hs
    exact ⟨v, hv, h ▸ hs, rfl⟩
  · intro σ' τ' f g h
    refine ⟨?_, ?_⟩
    · intro v hv hs
      exact ⟨v, hv, h ▸ hs, rfl⟩
    · intro a
      rw [h]

theorem is_simulation_simulates :
    IsSimulation (fun {σ : Ty} (t u : Tm [] σ) => Simulates t u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t u h v hv hs
    obtain ⟨R, hR, htu⟩ := h
    exact hR.1 t u htu v hv hs
  · intro t u h v hv hs
    obtain ⟨R, hR, htu⟩ := h
    exact hR.2.1 t u htu v hv hs
  · intro σ τ t u h
    obtain ⟨R, hR, htu⟩ := h
    obtain ⟨hval, happ⟩ := hR.2.2 t u htu
    refine ⟨?_, ?_⟩
    · intro v hv hs
      obtain ⟨v', hv', hs', hRvv'⟩ := hval v hv hs
      exact ⟨v', hv', hs', ⟨R, hR, hRvv'⟩⟩
    · intro a
      exact ⟨R, hR, happ a⟩

theorem sim_app_proof : sim_app := by
  intro σ τ t u a h
  exact (is_simulation_simulates.2.2 t u h).2 a

/-! ## Closure properties of similarity

These are the properties of `Simulates` that a proof of the simulation-to-
preorder direction gets for free: reflexivity (already proved), transitivity,
closure under reduction on either side, and transfer of termination.  What
they do **not** give is substitution of related arguments in a β-redex; that
is isolated in `beta_arg_congruence_of_subst` below. -/

/-- Similarity is transitive: the composition of two simulations is a
simulation.  (The composition keeps the applicative clause because both
factors do.) -/
theorem simulates_trans {σ : Ty} {t u v : Tm [] σ}
    (h1 : Simulates t u) (h2 : Simulates u v) : Simulates t v := by
  obtain ⟨R, hR, htu⟩ := h1
  obtain ⟨S, hS, huv⟩ := h2
  refine ⟨fun {υ} (x y : Tm [] υ) => ∃ z, R x z ∧ S z y, ?_, ⟨u, htu, huv⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b hob w hw hs
    obtain ⟨z, hRz, hSz⟩ := hob
    obtain ⟨w1, hw1, hs1, heq1⟩ := hR.1 a z hRz w hw hs
    obtain ⟨w2, hw2, hs2, heq2⟩ := hS.1 z b hSz w1 hw1 hs1
    exact ⟨w2, hw2, hs2, heq1.trans heq2⟩
  · intro a b hob w hw hs
    obtain ⟨z, hRz, hSz⟩ := hob
    obtain ⟨w1, hw1, hs1, heq1⟩ := hR.2.1 a z hRz w hw hs
    obtain ⟨w2, hw2, hs2, heq2⟩ := hS.2.1 z b hSz w1 hw1 hs1
    exact ⟨w2, hw2, hs2, heq1.trans heq2⟩
  · intro σ' τ' a b hob
    obtain ⟨z, hRz, hSz⟩ := hob
    obtain ⟨hRv, hRa⟩ := hR.2.2 a z hRz
    obtain ⟨hSv, hSa⟩ := hS.2.2 z b hSz
    refine ⟨?_, ?_⟩
    · intro w hw hs
      obtain ⟨w1, hw1, hs1, hR1⟩ := hRv w hw hs
      obtain ⟨w2, hw2, hs2, hS2⟩ := hSv w1 hw1 hs1
      exact ⟨w2, hw2, hs2, w1, hR1, hS2⟩
    · intro a0
      exact ⟨Tm.app z a0, hRa a0, hSa a0⟩

/-- If a reduction path contains a value, the value is reached from every
intermediate term of the path. -/
theorem steps_to_value {σ : Ty} {p q v : Tm [] σ} (hp : Steps p q)
    (hq : Steps p v) (hv : Value v) : Steps q v := by
  rcases steps_prefix hp hq with h | h
  · exact h
  · rw [steps_value_self hv h]
    exact .refl v

/-- Similarity is preserved by reducing *both* sides to related terms: if `x`
reduces to `z`, `y` to `z'`, and `z` simulates `z'`, then `x` simulates
`y`. -/
theorem simulates_join {σ : Ty} {x y z z' : Tm [] σ} (h : Simulates z z')
    (hx : Steps x z) (hy : Steps y z') : Simulates x y := by
  refine ⟨fun {υ} (p q : Tm [] υ) =>
      ∃ za zb, Simulates za zb ∧ Steps p za ∧ Steps q zb, ?_,
    ⟨z, z', h, hx, hy⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p q hob w hw hs
    obtain ⟨za, zb, hab, hp, hq⟩ := hob
    obtain ⟨R, hR, habR⟩ := hab
    obtain ⟨w', hw', hs', heq⟩ := hR.1 za zb habR w hw (steps_to_value hp hs hw)
    exact ⟨w', hw', steps_trans_aux hq hs', heq⟩
  · intro p q hob w hw hs
    obtain ⟨za, zb, hab, hp, hq⟩ := hob
    obtain ⟨R, hR, habR⟩ := hab
    obtain ⟨w', hw', hs', heq⟩ := hR.2.1 za zb habR w hw (steps_to_value hp hs hw)
    exact ⟨w', hw', steps_trans_aux hq hs', heq⟩
  · intro σ' τ' p q hob
    obtain ⟨za, zb, hab, hp, hq⟩ := hob
    obtain ⟨R, hR, habR⟩ := hab
    obtain ⟨hRv, hRa⟩ := hR.2.2 za zb habR
    refine ⟨?_, ?_⟩
    · intro w hw hs
      obtain ⟨w', hw', hs', hR'⟩ := hRv w hw (steps_to_value hp hs hw)
      exact ⟨w', hw', steps_trans_aux hq hs',
        ⟨w, w', ⟨R, hR, hR'⟩, .refl w, .refl w'⟩⟩
    · intro a0
      exact ⟨Tm.app za a0, Tm.app zb a0, ⟨R, hR, hRa a0⟩,
        steps_app_fun a0 hp, steps_app_fun a0 hq⟩

/-- Similarity is preserved when both sides reduce further. -/
theorem simulates_steps {σ : Ty} {t t' u u' : Tm [] σ} (h : Simulates t u)
    (h1 : Steps t t') (h2 : Steps u u') : Simulates t' u' := by
  refine ⟨fun {υ} (p q : Tm [] υ) =>
      ∃ za zb, Simulates za zb ∧ Steps za p ∧ Steps zb q, ?_,
    ⟨t, u, h, h1, h2⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p q hob w hw hs
    obtain ⟨za, zb, hab, hp, hq⟩ := hob
    obtain ⟨R, hR, habR⟩ := hab
    obtain ⟨w', hw', hs', heq⟩ := hR.1 za zb habR w hw (steps_trans_aux hp hs)
    exact ⟨w', hw', steps_to_value hq hs' hw', heq⟩
  · intro p q hob w hw hs
    obtain ⟨za, zb, hab, hp, hq⟩ := hob
    obtain ⟨R, hR, habR⟩ := hab
    obtain ⟨w', hw', hs', heq⟩ := hR.2.1 za zb habR w hw (steps_trans_aux hp hs)
    exact ⟨w', hw', steps_to_value hq hs' hw', heq⟩
  · intro σ' τ' p q hob
    obtain ⟨za, zb, hab, hp, hq⟩ := hob
    obtain ⟨R, hR, habR⟩ := hab
    obtain ⟨hRv, hRa⟩ := hR.2.2 za zb habR
    refine ⟨?_, ?_⟩
    · intro w hw hs
      obtain ⟨w', hw', hs', hR'⟩ := hRv w hw (steps_trans_aux hp hs)
      exact ⟨w', hw', steps_to_value hq hs' hw',
        ⟨w, w', ⟨R, hR, hR'⟩, .refl w, .refl w'⟩⟩
    · intro a0
      exact ⟨Tm.app za a0, Tm.app zb a0, ⟨R, hR, hRa a0⟩,
        steps_app_fun a0 hp, steps_app_fun a0 hq⟩

theorem simulates_term_nat {t u : Tm [] Ty.nat} (h : Simulates t u) :
    Terminates t → Terminates u := by
  rintro ⟨w, hw, hs⟩
  obtain ⟨R, hR, htu⟩ := h
  obtain ⟨w', hw', hs', _⟩ := hR.1 t u htu w hw hs
  exact ⟨w', hw', hs'⟩

theorem simulates_term_bool {t u : Tm [] Ty.bool} (h : Simulates t u) :
    Terminates t → Terminates u := by
  rintro ⟨w, hw, hs⟩
  obtain ⟨R, hR, htu⟩ := h
  obtain ⟨w', hw', hs', _⟩ := hR.2.1 t u htu w hw hs
  exact ⟨w', hw', hs'⟩

theorem simulates_term_arr {σ τ : Ty} {t u : Tm [] (Ty.arr σ τ)}
    (h : Simulates t u) : Terminates t → Terminates u := by
  rintro ⟨w, hw, hs⟩
  obtain ⟨R, hR, htu⟩ := h
  obtain ⟨w', hw', hs', _⟩ := (hR.2.2 t u htu).1 w hw hs
  exact ⟨w', hw', hs'⟩

/-- Similarity transfers termination: this is the target at the empty
context. -/
theorem simulates_term {σ : Ty} {t u : Tm [] σ} (h : Simulates t u) :
    Terminates t → Terminates u := by
  intro ht
  cases σ with
  | nat => exact simulates_term_nat h ht
  | bool => exact simulates_term_bool h ht
  | arr σ' τ' => exact simulates_term_arr h ht

/-- The target at the empty context. -/
theorem sim_implies_contextual_le_id {σ : Ty} (t u : Tm [] σ)
    (h : Simulates t u) : Terminates t → Terminates u := simulates_term h

/-- The target at applicative contexts of one argument. -/
theorem sim_implies_contextual_le_app {σ τ : Ty}
    (t u : Tm [] (Ty.arr σ τ)) (a : Tm [] σ) (h : Simulates t u) :
    Terminates (Tm.app t a) → Terminates (Tm.app u a) :=
  simulates_term (sim_app_proof t u a h)

/-! ## The exact remaining gap

A non-Howe route through a context lemma needs the following instance of
argument congruence at a β-redex: substituting *related values* into one fixed
body preserves similarity.  The free closure properties above reduce the
target to it; nothing smaller is known to suffice. -/

/-- Related values substituted into one fixed body give related β-reducts.
This is the β-instance of "argument congruence". -/
theorem beta_arg_congruence_of_subst {σ τ : Ty}
    (hsub : ∀ (b : Tm (σ :: []) τ) (v v' : Tm [] σ),
      Value v → Value v' → Simulates v v' → Simulates (subst0 b v) (subst0 b v'))
    (b : Tm (σ :: []) τ) (v v' : Tm [] σ)
    (hv : Value v) (hv' : Value v') (hvv : Simulates v v') :
    Simulates (Tm.app (Tm.lam b) v) (Tm.app (Tm.lam b) v') :=
  simulates_join (hsub b v v' hv hv' hvv)
    (Steps.step (Steps.refl _) (Step.app_lam hv))
    (Steps.step (Steps.refl _) (Step.app_lam hv'))

/-- With the closure properties above, the target is *exactly* the congruence
statement for similarity: any proof of `sim_congruent` (whatever its method)
yields `sim_implies_contextual_le` by one application of termination
transfer. -/
theorem sim_implies_contextual_le_of_congruent (hc : sim_congruent) :
    sim_implies_contextual_le := by
  intro σ t u h τ C hT
  exact simulates_term (hc C t u h) hT

/-! ## Contextual may-preorder implies similarity -/

/-- A closed term that never reaches a value. -/
def looping : Tm [] Ty.nat := .fix (.lam (.var .here))

theorem looping_no_value : ¬ Value looping := by
  intro h
  cases h

/-- `(λx.x) ·` applied `n` times to `looping`. -/
def loopingIter : Nat → Tm [] Ty.nat
  | 0 => looping
  | n + 1 => .app (.lam (.var .here)) (loopingIter n)

theorem loopingIter_step : ∀ n, Step (loopingIter n) (loopingIter (n + 1))
  | 0 => Step.fix
  | n + 1 => Step.app_arg .lam (loopingIter_step n)

theorem loopingIter_no_value : ∀ n, ¬ Value (loopingIter n)
  | 0 => looping_no_value
  | n + 1 => by
      intro h
      cases h

theorem looping_diverge : ¬ Terminates looping := by
  rintro ⟨v, hv, hs⟩
  have key : ∀ (n : Nat) {w : Tm [] Ty.nat}, Steps (loopingIter n) w →
      ∃ m, n ≤ m ∧ w = loopingIter m := by
    intro n w h
    induction h with
    | refl => exact ⟨n, Nat.le_refl n, rfl⟩
    | step h1 hstep ih =>
        obtain ⟨m, hmn, rfl⟩ := ih
        exact ⟨m + 1, Nat.le_succ_of_le hmn, step_det hstep (loopingIter_step m)⟩
  obtain ⟨m, _, rfl⟩ := key 0 hs
  exact loopingIter_no_value m hv

/-- The numerals. -/
def numeral : Nat → Tm [] Ty.nat
  | 0 => .zero
  | n + 1 => .succ (numeral n)

theorem value_numeral : ∀ n, Value (numeral n)
  | 0 => .zero
  | n + 1 => .succ (value_numeral n)

theorem value_nat_numeral : ∀ {v : Tm [] Ty.nat}, Value v → ∃ n, v = numeral n
  | _, .zero => ⟨0, rfl⟩
  | _, .succ hv => by
      obtain ⟨n, rfl⟩ := value_nat_numeral hv
      exact ⟨n + 1, rfl⟩

theorem numeral_inj (k : Nat) : ∀ {m : Nat}, numeral k = numeral m → k = m := by
  induction k with
  | zero =>
      intro m h
      cases m with
      | zero => rfl
      | succ m => cases h
  | succ k ih =>
      intro m h
      cases m with
      | zero => cases h
      | succ m =>
          have h' : numeral k = numeral m := by injection h
          exact congrArg Nat.succ (ih h')

/-- `n`-fold predecessor. -/
def predN {Γ : List Ty} : Nat → Tm Γ Ty.nat → Tm Γ Ty.nat
  | 0, t => t
  | n + 1, t => .pred (predN n t)

theorem subst_predN {Γ Δ : List Ty} (f : ∀ {σ}, Var Γ σ → Tm Δ σ)
    (t : Tm Γ Ty.nat) (n : Nat) :
    subst f (predN n t) = predN n (subst f t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show Tm.pred (subst f (predN n t)) = Tm.pred (predN n (subst f t))
      rw [ih]

theorem plug_predN (n : Nat) (v : Tm [] Ty.nat) :
    plug (predN n (.var (Var.here : Var [Ty.nat] Ty.nat))) v = predN n v := by
  show subst (substHere v) (predN n (.var Var.here)) = predN n v
  rw [subst_predN]
  rfl

theorem steps_pred {t t' : Tm [] Ty.nat} (h : Steps t t') :
    Steps (Tm.pred t) (Tm.pred t') := by
  induction h with
  | refl => exact .refl _
  | step h1 h2 ih => exact .step ih (.pred h2)

theorem pred_numeral (m : Nat) : Steps (Tm.pred (numeral m)) (numeral (m - 1)) := by
  cases m with
  | zero => exact .step (.refl _) .pred_zero
  | succ k => exact .step (.refl _) (.pred_succ (value_numeral k))

theorem predN_steps_numeral (n m : Nat) :
    Steps (predN n (numeral m)) (numeral (m - n)) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
      have h1 : Steps (predN (n + 1) (numeral m)) (Tm.pred (numeral (m - n))) :=
        steps_pred ih
      have h2 : Steps (Tm.pred (numeral (m - n))) (numeral (m - n - 1)) :=
        pred_numeral (m - n)
      have h3 : m - n - 1 = m - (n + 1) := by omega
      rw [h3] at h2
      exact steps_trans_aux h1 h2

theorem steps_ifz {σ : Ty} (a b : Tm [] σ) {t t' : Tm [] Ty.nat} (h : Steps t t') :
    Steps (Tm.ifz t a b) (Tm.ifz t' a b) := by
  induction h with
  | refl => exact .refl _
  | step h1 h2 ih => exact .step ih (.ifz h2)

/-- `ifz (pred^n □) 0 ω`: terminates exactly on numerals `≤ n`. -/
def testLe (n : Nat) : Tm [Ty.nat] Ty.nat :=
  .ifz (predN n (.var .here)) .zero (weaken (Γ := [Ty.nat]) looping)

/-- `ifz (pred^n □) ω 0`: terminates exactly on numerals `> n`. -/
def testGt (n : Nat) : Tm [Ty.nat] Ty.nat :=
  .ifz (predN n (.var .here)) (weaken (Γ := [Ty.nat]) looping) .zero

theorem plug_testLe (n : Nat) (v : Tm [] Ty.nat) :
    plug (testLe n) v = Tm.ifz (predN n v) Tm.zero (weaken (Γ := []) looping) := by
  show Tm.ifz (subst (substHere v) (predN n (.var Var.here)))
      (subst (substHere v) Tm.zero)
      (subst (substHere v) (weaken (Γ := [Ty.nat]) looping))
      = Tm.ifz (predN n v) Tm.zero (weaken (Γ := []) looping)
  rw [subst_predN, subst_weaken]
  rfl

theorem plug_testGt (n : Nat) (v : Tm [] Ty.nat) :
    plug (testGt n) v = Tm.ifz (predN n v) (weaken (Γ := []) looping) Tm.zero := by
  show Tm.ifz (subst (substHere v) (predN n (.var Var.here)))
      (subst (substHere v) (weaken (Γ := [Ty.nat]) looping))
      (subst (substHere v) Tm.zero)
      = Tm.ifz (predN n v) (weaken (Γ := []) looping) Tm.zero
  rw [subst_predN, subst_weaken]
  rfl

theorem terminates_testLe {n m : Nat} (h : m ≤ n) :
    Terminates (plug (testLe n) (numeral m)) := by
  refine ⟨Tm.zero, .zero, ?_⟩
  rw [plug_testLe]
  have h1 : Steps (Tm.ifz (predN n (numeral m)) Tm.zero (weaken (Γ := []) looping))
      (Tm.ifz (numeral (m - n)) Tm.zero (weaken (Γ := []) looping)) :=
    steps_ifz _ _ (predN_steps_numeral n m)
  have h2 : m - n = 0 := Nat.sub_eq_zero_of_le h
  rw [h2] at h1
  exact .step h1 .ifz_zero

theorem diverges_testLe {n m : Nat} (h : m > n) :
    ¬ Terminates (plug (testLe n) (numeral m)) := by
  intro ht
  rw [plug_testLe] at ht
  obtain ⟨w, hw, hws⟩ := ht
  have h1 : Steps (Tm.ifz (predN n (numeral m)) Tm.zero (weaken (Γ := []) looping))
      (Tm.ifz (numeral (m - n)) Tm.zero (weaken (Γ := []) looping)) :=
    steps_ifz _ _ (predN_steps_numeral n m)
  obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
  rw [hk] at h1
  have h2 : Steps (Tm.ifz (numeral (k + 1)) Tm.zero (weaken (Γ := []) looping))
      (weaken (Γ := []) looping) := .step (.refl _) (.ifz_succ (value_numeral k))
  have h3 : Steps (Tm.ifz (predN n (numeral m)) Tm.zero (weaken (Γ := []) looping))
      (weaken (Γ := []) looping) := steps_trans_aux h1 h2
  have h4 : Steps (weaken (Γ := []) looping) w := steps_to_value h3 hws hw
  rw [weaken_nil] at h4
  exact looping_diverge ⟨w, hw, h4⟩

theorem terminates_testGt {n m : Nat} (h : m > n) :
    Terminates (plug (testGt n) (numeral m)) := by
  refine ⟨Tm.zero, .zero, ?_⟩
  rw [plug_testGt]
  have h1 : Steps (Tm.ifz (predN n (numeral m)) (weaken (Γ := []) looping) Tm.zero)
      (Tm.ifz (numeral (m - n)) (weaken (Γ := []) looping) Tm.zero) :=
    steps_ifz _ _ (predN_steps_numeral n m)
  obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
  rw [hk] at h1
  exact .step h1 (.ifz_succ (value_numeral k))

theorem diverges_testGt {n m : Nat} (h : m ≤ n) :
    ¬ Terminates (plug (testGt n) (numeral m)) := by
  intro ht
  rw [plug_testGt] at ht
  obtain ⟨w, hw, hws⟩ := ht
  have h1 : Steps (Tm.ifz (predN n (numeral m)) (weaken (Γ := []) looping) Tm.zero)
      (Tm.ifz (numeral (m - n)) (weaken (Γ := []) looping) Tm.zero) :=
    steps_ifz _ _ (predN_steps_numeral n m)
  have h2 : m - n = 0 := Nat.sub_eq_zero_of_le h
  rw [h2] at h1
  have h3 : Steps (Tm.ifz (numeral 0) (weaken (Γ := []) looping) Tm.zero)
      (weaken (Γ := []) looping) := .step (.refl _) .ifz_zero
  have h4 : Steps (Tm.ifz (predN n (numeral m)) (weaken (Γ := []) looping) Tm.zero)
      (weaken (Γ := []) looping) := steps_trans_aux h1 h3
  have h5 : Steps (weaken (Γ := []) looping) w := steps_to_value h4 hws hw
  rw [weaken_nil] at h5
  exact looping_diverge ⟨w, hw, h5⟩

/-- `numeral k` may-terminates in `numeral m` only if `m ≤ k`. -/
theorem le_of_contextual_le_numeral {k m : Nat}
    (h : ContextualLe (numeral k) (numeral m)) : m ≤ k := by
  by_cases hkm : k < m
  · exact absurd (h (testLe k) (terminates_testLe (Nat.le_refl k))) (diverges_testLe hkm)
  · omega

/-- `numeral k` may-terminates in `numeral m` only if `k ≤ m`. -/
theorem ge_of_contextual_le_numeral {k m : Nat}
    (h : ContextualLe (numeral k) (numeral m)) : k ≤ m := by
  by_cases hkm : k ≤ m
  · exact hkm
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hmj : m ≤ j := by omega
    exact absurd (h (testGt j) (terminates_testGt (n := j) (m := j + 1) (by omega)))
      (diverges_testGt hmj)

/-- Contextually related values at `nat` are equal: `testLe`/`testGt` pin the
numeral on both sides. -/
theorem values_eq_of_contextual_le_nat {v v' : Tm [] Ty.nat}
    (h : ContextualLe v v') (hv : Value v) (hv' : Value v') : v = v' := by
  obtain ⟨k, rfl⟩ := value_nat_numeral hv
  obtain ⟨m, rfl⟩ := value_nat_numeral hv'
  have h1 : m ≤ k := le_of_contextual_le_numeral h
  have h2 : k ≤ m := ge_of_contextual_le_numeral h
  have hkm : m = k := by omega
  rw [hkm]

theorem value_bool_cases {v : Tm [] Ty.bool} (h : Value v) :
    v = Tm.tt ∨ v = Tm.ff := by
  cases h with
  | tt => exact Or.inl rfl
  | ff => exact Or.inr rfl

/-- `cond □ 0 ω`: terminates exactly on `tt`. -/
def testT : Tm [Ty.bool] Ty.nat :=
  .cond (.var .here) .zero (weaken (Γ := [Ty.bool]) looping)

/-- `cond □ ω 0`: terminates exactly on `ff`. -/
def testF : Tm [Ty.bool] Ty.nat :=
  .cond (.var .here) (weaken (Γ := [Ty.bool]) looping) .zero

theorem plug_testT (v : Tm [] Ty.bool) :
    plug testT v = Tm.cond v Tm.zero (weaken (Γ := []) looping) := by
  show Tm.cond (subst (substHere v) (.var Var.here))
      (subst (substHere v) Tm.zero)
      (subst (substHere v) (weaken (Γ := [Ty.bool]) looping))
      = Tm.cond v Tm.zero (weaken (Γ := []) looping)
  rw [subst_weaken]
  rfl

theorem plug_testF (v : Tm [] Ty.bool) :
    plug testF v = Tm.cond v (weaken (Γ := []) looping) Tm.zero := by
  show Tm.cond (subst (substHere v) (.var Var.here))
      (subst (substHere v) (weaken (Γ := [Ty.bool]) looping))
      (subst (substHere v) Tm.zero)
      = Tm.cond v (weaken (Γ := []) looping) Tm.zero
  rw [subst_weaken]
  rfl

theorem terminates_testT : Terminates (plug testT Tm.tt) := by
  refine ⟨Tm.zero, .zero, ?_⟩
  rw [plug_testT]
  exact .step (.refl _) .cond_tt

theorem diverges_testT : ¬ Terminates (plug testT Tm.ff) := by
  intro ht
  rw [plug_testT] at ht
  obtain ⟨w, hw, hws⟩ := ht
  have h1 : Steps (Tm.cond Tm.ff Tm.zero (weaken (Γ := []) looping))
      (weaken (Γ := []) looping) := .step (.refl _) .cond_ff
  have h2 : Steps (weaken (Γ := []) looping) w := steps_to_value h1 hws hw
  rw [weaken_nil] at h2
  exact looping_diverge ⟨w, hw, h2⟩

theorem terminates_testF : Terminates (plug testF Tm.ff) := by
  refine ⟨Tm.zero, .zero, ?_⟩
  rw [plug_testF]
  exact .step (.refl _) .cond_ff

theorem diverges_testF : ¬ Terminates (plug testF Tm.tt) := by
  intro ht
  rw [plug_testF] at ht
  obtain ⟨w, hw, hws⟩ := ht
  have h1 : Steps (Tm.cond Tm.tt (weaken (Γ := []) looping) Tm.zero)
      (weaken (Γ := []) looping) := .step (.refl _) .cond_tt
  have h2 : Steps (weaken (Γ := []) looping) w := steps_to_value h1 hws hw
  rw [weaken_nil] at h2
  exact looping_diverge ⟨w, hw, h2⟩

theorem values_eq_of_contextual_le_bool {v v' : Tm [] Ty.bool}
    (h : ContextualLe v v') (hv : Value v) (hv' : Value v') : v = v' := by
  rcases value_bool_cases hv with rfl | rfl <;> rcases value_bool_cases hv' with rfl | rfl
  · rfl
  · exact absurd (h testT terminates_testT) diverges_testT
  · exact absurd (h testF terminates_testF) diverges_testF
  · rfl

theorem is_simulation_contextual_le :
    IsSimulation (fun {σ : Ty} (t u : Tm [] σ) => ContextualLe t u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t u h v hv hs
    obtain ⟨v', hv', hs'⟩ := h (Tm.var Var.here) ⟨v, hv, hs⟩
    exact ⟨v', hv', hs',
      values_eq_of_contextual_le_nat (contextual_le_value_proof t u v v' h hv hs hv' hs')
        hv hv'⟩
  · intro t u h v hv hs
    obtain ⟨v', hv', hs'⟩ := h (Tm.var Var.here) ⟨v, hv, hs⟩
    exact ⟨v', hv', hs',
      values_eq_of_contextual_le_bool (contextual_le_value_proof t u v v' h hv hs hv' hs')
        hv hv'⟩
  · intro σ τ t u h
    refine ⟨?_, ?_⟩
    · intro v hv hs
      obtain ⟨v', hv', hs'⟩ := h (Tm.var Var.here) ⟨v, hv, hs⟩
      exact ⟨v', hv', hs', contextual_le_value_proof t u v v' h hv hs hv' hs'⟩
    · intro a
      exact contextual_le_app_proof t u a h

theorem contextual_le_implies_sim_proof : contextual_le_implies_sim := by
  intro σ t u h
  exact ⟨fun {υ} (x y : Tm [] υ) => ContextualLe x y, is_simulation_contextual_le, h⟩

/-! ## The target is interderivable with the congruence statement

With the contextual preorder closed under plugging (target 3) and with
`ContextualLe ⊆ Simulates` (target 8) both available, the simulation-to-
preorder direction and the precongruence statement imply each other.  So a
proof of the target *is* a proof that similarity is a precongruence: the
non-Howe routes and Howe's method are not merely two choices, they are the
same obligation in this development. -/

/-- Target 10 yields the precongruence statement. -/
theorem sim_congruent_of_sim_implies_contextual_le
    (h : sim_implies_contextual_le) : sim_congruent := by
  intro σ τ C t u htu
  exact contextual_le_implies_sim_proof (plug C t) (plug C u)
    (contextual_le_plug_proof C (h t u htu))

/-- The target and the precongruence statement are equivalent. -/
theorem sim_implies_contextual_le_iff_sim_congruent :
    sim_implies_contextual_le ↔ sim_congruent :=
  ⟨sim_congruent_of_sim_implies_contextual_le, sim_implies_contextual_le_of_congruent⟩

/-- Target 11, from the target. -/
theorem contextual_le_iff_sim_of_sim_implies_contextual_le
    (h : sim_implies_contextual_le) : contextual_le_iff_sim := by
  intro σ t u
  exact ⟨fun hc => contextual_le_implies_sim_proof t u hc, h t u⟩

/-- Target 12, from target 11. -/
theorem contextual_eq_iff_sim_both_of_iff (h : contextual_le_iff_sim) :
    contextual_eq_iff_sim_both := by
  intro σ t u
  exact ⟨fun hc => ⟨(h t u).1 hc.1, (h u t).1 hc.2⟩,
    fun hs => ⟨(h t u).2 hs.1, (h u t).2 hs.2⟩⟩

/-- Conversely, argument congruence at a λ-abstraction gives substitution of
related values into that body (reduce both sides to the β-reduct). -/
theorem subst_of_beta_arg_congruence {σ τ : Ty}
    (hac : ∀ (b : Tm (σ :: []) τ) (v v' : Tm [] σ),
      Value v → Value v' → Simulates v v' →
        Simulates (Tm.app (Tm.lam b) v) (Tm.app (Tm.lam b) v'))
    (b : Tm (σ :: []) τ) (v v' : Tm [] σ)
    (hv : Value v) (hv' : Value v') (h : Simulates v v') :
    Simulates (subst0 b v) (subst0 b v') :=
  simulates_steps (hac b v v' hv hv' h)
    (Steps.step (Steps.refl (Tm.app (Tm.lam b) v)) (Step.app_lam hv))
    (Steps.step (Steps.refl (Tm.app (Tm.lam b) v')) (Step.app_lam hv'))

/-- The missing ingredient, in its two equivalent forms: substitution of
related values into one fixed body, and argument congruence at a
λ-abstraction.  Neither is derivable from the simulation clauses by
structural induction: the body of a λ-value is only *behaviourally* related
to the syntax, which is exactly the gap that Howe's transitively closed
compatible relation fills. -/
theorem subst_value_iff_beta_arg_congruence {σ τ : Ty} :
    (∀ (b : Tm (σ :: []) τ) (v v' : Tm [] σ),
      Value v → Value v' → Simulates v v' → Simulates (subst0 b v) (subst0 b v'))
    ↔ (∀ (b : Tm (σ :: []) τ) (v v' : Tm [] σ),
      Value v → Value v' → Simulates v v' →
        Simulates (Tm.app (Tm.lam b) v) (Tm.app (Tm.lam b) v')) :=
  ⟨beta_arg_congruence_of_subst, subst_of_beta_arg_congruence⟩

/-- Similar terms that are already `nat` values are equal (the base clause of
`IsSimulation` is equality). -/
theorem simulates_eq_of_nat_values {v v' : Tm [] Ty.nat} (h : Simulates v v')
    (hv : Value v) (hv' : Value v') : v = v' := by
  obtain ⟨R, hR, hvR⟩ := h
  obtain ⟨w, hw, hs, heq⟩ := hR.1 v v' hvR v hv (.refl v)
  exact heq.trans (steps_value_self hv' hs)

/-- Similar terms that are already `bool` values are equal. -/
theorem simulates_eq_of_bool_values {v v' : Tm [] Ty.bool} (h : Simulates v v')
    (hv : Value v) (hv' : Value v') : v = v' := by
  obtain ⟨R, hR, hvR⟩ := h
  obtain ⟨w, hw, hs, heq⟩ := hR.2.1 v v' hvR v hv (.refl v)
  exact heq.trans (steps_value_self hv' hs)

/-- Changing a `nat`-typed value argument of a fixed function is free: the two
values are literally equal.  So argument congruence fails only for
function-typed arguments, whose λ-bodies are merely behaviourally related. -/
theorem simulates_app_nat_arg {τ : Ty} (f : Tm [] (Ty.arr Ty.nat τ))
    {v v' : Tm [] Ty.nat} (h : Simulates v v') (hv : Value v) (hv' : Value v') :
    Simulates (Tm.app f v) (Tm.app f v') := by
  rw [simulates_eq_of_nat_values h hv hv']
  exact sim_refl_proof _

/-- Changing a `bool`-typed value argument of a fixed function is free. -/
theorem simulates_app_bool_arg {τ : Ty} (f : Tm [] (Ty.arr Ty.bool τ))
    {v v' : Tm [] Ty.bool} (h : Simulates v v') (hv : Value v) (hv' : Value v') :
    Simulates (Tm.app f v) (Tm.app f v') := by
  rw [simulates_eq_of_bool_values h hv hv']
  exact sim_refl_proof _

/-- Substituting related `nat` values into a body is trivial: similar base
values are literally equal, so both sides are the same term. -/
theorem subst0_nat_value {τ : Ty} (b : Tm (Ty.nat :: []) τ) {v v' : Tm [] Ty.nat}
    (hv : Value v) (hv' : Value v') (h : Simulates v v') :
    Simulates (subst0 b v) (subst0 b v') := by
  rw [simulates_eq_of_nat_values h hv hv']
  exact sim_refl_proof _

/-- Substituting related `bool` values into a body is trivial. -/
theorem subst0_bool_value {τ : Ty} (b : Tm (Ty.bool :: []) τ) {v v' : Tm [] Ty.bool}
    (hv : Value v) (hv' : Value v') (h : Simulates v v') :
    Simulates (subst0 b v) (subst0 b v') := by
  rw [simulates_eq_of_bool_values h hv hv']
  exact sim_refl_proof _

/-- The *different-body* substitution case is derivable from the *same-body*
case together with the applicative clause of the simulation: relate
`b[v]` to `b[v']` by the same-body lemma, and `b[v']` to `b'[v']` by the
applicative clause at argument `v'`.  So the single remaining obligation is
the same-body lemma, i.e. substitution into *one* body. -/
theorem simulates_subst_related_bodies_of_same {σ τ : Ty}
    (hsub : ∀ (b : Tm (σ :: []) τ) (v v' : Tm [] σ),
      Value v → Value v' → Simulates v v' → Simulates (subst0 b v) (subst0 b v'))
    {b b' : Tm (σ :: []) τ} {v v' : Tm [] σ}
    (hv : Value v) (hv' : Value v') (hvv : Simulates v v')
    (hlam : Simulates (Tm.lam b) (Tm.lam b')) :
    Simulates (subst0 b v) (subst0 b' v') := by
  have h1 : Simulates (subst0 b v) (subst0 b v') := hsub b v v' hv hv' hvv
  have happ : Simulates (Tm.app (Tm.lam b) v') (Tm.app (Tm.lam b') v') :=
    (is_simulation_simulates.2.2 (Tm.lam b) (Tm.lam b') hlam).2 v'
  have h2 : Simulates (subst0 b v') (subst0 b' v') :=
    simulates_steps happ
      (Steps.step (Steps.refl _) (Step.app_lam hv'))
      (Steps.step (Steps.refl _) (Step.app_lam hv'))
  exact simulates_trans h1 h2

/-! ## Bounded-step calculus

`StepsN n t u` means "exactly `n` steps".  Counting the steps of the
left-hand computation is what makes the evaluation-order decompositions below
possible: an application's evaluation is split into the function's steps, the
argument's steps, one β-step, and the body's steps, with the counts summing to
the total.  The bounded decompositions drive the compatibility lemmas of the
level-free relation, and `StepsN` is also where the termination argument for
`fix` gets its well-founded measure. -/

/-- `t` reduces to `u` in exactly `n` steps. -/
inductive StepsN {σ : Ty} : Nat → Tm [] σ → Tm [] σ → Prop where
  | zero (t : Tm [] σ) : StepsN 0 t t
  | succ {n : Nat} {t u v : Tm [] σ} : Step t u → StepsN n u v → StepsN (n + 1) t v

theorem stepsN_steps {σ : Ty} {n : Nat} {t u : Tm [] σ} (h : StepsN n t u) :
    Steps t u := by
  induction h with
  | zero t => exact Steps.refl t
  | succ hstep hrest ih =>
      exact steps_trans_aux (Steps.step (Steps.refl _) hstep) ih

theorem stepsN_step {σ : Ty} {n : Nat} {t u : Tm [] σ} (h : StepsN n t u) :
    ∀ {v : Tm [] σ}, Step u v → StepsN (n + 1) t v := by
  induction h with
  | zero t =>
      intro v hv
      have hidx : 0 + 1 = 1 := by omega
      rw [hidx]
      exact StepsN.succ hv (StepsN.zero v)
  | succ hstep hrest ih =>
      intro v hv
      exact StepsN.succ hstep (ih hv)

theorem steps_stepsN {σ : Ty} {t u : Tm [] σ} (h : Steps t u) :
    ∃ n, StepsN n t u := by
  induction h with
  | refl => exact ⟨0, StepsN.zero _⟩
  | step h1 h2 ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, stepsN_step hn h2⟩

/-- Evaluation-order decomposition for an application: an `n`-step evaluation
of `f a` evaluates `f` to a λ, then `a` to a value, then makes one β-step and
continues in the body. -/
theorem stepsN_app_inv {σ τ : Ty} :
    ∀ (k : Nat) {f : Tm [] (Ty.arr σ τ)} {a : Tm [] σ} {v : Tm [] τ},
      StepsN k (Tm.app f a) v → Value v →
      ∃ (j1 : Nat) (h : Tm (σ :: []) τ) (j2 : Nat) (av : Tm [] σ) (j3 : Nat),
        StepsN j1 f (Tm.lam h) ∧ StepsN j2 a av ∧ Value av ∧
          StepsN j3 (subst0 h av) v ∧ j1 + 1 + j2 + j3 = k := by
  intro k
  induction k with
  | zero =>
      intro f a v h hv
      cases h
      cases hv
  | succ j ih =>
      intro f a v h hv
      cases h with
      | succ hstep hrest =>
          cases hstep with
          | app_fun hf =>
              obtain ⟨j1, h, j2, av, j3, h1, h2, h3, h4, h5⟩ := ih hrest hv
              exact ⟨j1 + 1, h, j2, av, j3, StepsN.succ hf h1, h2, h3, h4, by omega⟩
          | app_arg val ha =>
              obtain ⟨j1, h, j2, av, j3, h1, h2, h3, h4, h5⟩ := ih hrest hv
              exact ⟨j1, h, j2 + 1, av, j3, h1, StepsN.succ ha h2, h3, h4, by omega⟩
          | app_lam val =>
              exact ⟨0, _, 0, a, j, StepsN.zero _, StepsN.zero _, val, hrest, by omega⟩


/-- A value that reaches a term by a bounded reduction is that term already. -/
theorem stepsN_value {n : Nat} {σ : Ty} {v w : Tm [] σ} (h : StepsN n v w)
    (hv : Value v) : n = 0 ∧ w = v := by
  cases h with
  | zero t => exact ⟨rfl, rfl⟩
  | succ hstep _ => exact (value_no_step hv hstep).elim



/-! ## Level-free logical relation

A step index that bounds the left computation loses a level on every
application, so the "change the argument" step cannot be composed with the
same-argument step.  Dropping the index removes the bookkeeping entirely:
`EL` is the plain predicate "every value that `t` reaches is matched by a
value that `t'` reaches, and the two are related", with the only recursive
ingredients being the type recursion in `VEL` and the termination argument
for `fix`.  Since `EL` is *not* indexed by the number of steps, no level has
to be split between the two computations. -/

/-- A closing substitution environment. -/
def Env (Γ : List Ty) := ∀ {υ : Ty}, Var Γ υ → Tm [] υ

/-- Extend a closed environment with one more closed value. -/
def EnvCons {Γ : List Ty} {σ : Ty} (a : Tm [] σ) (γ : Env Γ) : Env (σ :: Γ) :=
  fun {υ} (v : Var (σ :: Γ) υ) =>
    match v with
    | .here => a
    | .there w => γ w

/-! ### Substitution under a binder -/

theorem subst_there_closed {σ τ : Ty} (a : Tm [] σ) (x : Tm [] τ) :
    subst (substHere a) (rename (fun {υ} (v : Var [] υ) => Var.there v) x)
      = x := by
  rw [subst_rename]
  rw [show subst (fun {υ : Ty} (v : Var [] υ) => substHere a (Var.there v)) x
        = subst (fun {υ : Ty} (v : Var [] υ) => Tm.var v) x from
      subst_congr x _ _ (fun {υ} v => rfl)]
  exact subst_id x

/-- Substituting a closed value for the innermost variable equals extending
the environment with that value. -/
theorem subst_envCons {Γ : List Ty} {σ τ : Ty} (b : Tm (σ :: Γ) τ)
    (γ : Env Γ) (a : Tm [] σ) :
    subst (EnvCons a γ) b = subst0 (subst (liftSubst γ) b) a := by
  show subst (EnvCons a γ) b = subst (substHere a) (subst (liftSubst γ) b)
  rw [subst_subst]
  refine subst_congr b _ _ (fun {υ} v => ?_)
  cases v with
  | here => rfl
  | there w =>
      show γ w = subst (substHere a) (liftSubst γ (Var.there w))
      exact (subst_there_closed a (γ w)).symm

/-! ### Terms that are never values -/

theorem not_value_app {σ τ : Ty} (f : Tm [] (Ty.arr σ τ)) (a : Tm [] σ) :
    ¬ Value (Tm.app f a) := by intro h; cases h

theorem not_value_pred (t : Tm [] Ty.nat) : ¬ Value (Tm.pred t) := by
  intro h; cases h

theorem not_value_ifz {σ : Ty} (n : Tm [] Ty.nat) (a b : Tm [] σ) :
    ¬ Value (Tm.ifz n a b) := by intro h; cases h

theorem not_value_cond {σ : Ty} (c : Tm [] Ty.bool) (a b : Tm [] σ) :
    ¬ Value (Tm.cond c a b) := by intro h; cases h

theorem not_value_fix {σ : Ty} (f : Tm [] (Ty.arr σ σ)) :
    ¬ Value (Tm.fix f) := by intro h; cases h

theorem value_nat_cases {v : Tm [] Ty.nat} (h : Value v) :
    v = Tm.zero ∨ ∃ w, v = Tm.succ w ∧ Value w := by
  cases h with
  | zero => exact Or.inl rfl
  | succ hw => exact Or.inr ⟨_, rfl, hw⟩

theorem value_arr_cases {σ τ : Ty} {v : Tm [] (Ty.arr σ τ)} (h : Value v) :
    ∃ b, v = Tm.lam b := by cases h with | lam => exact ⟨_, rfl⟩

theorem value_pred_cases {v : Tm [] Ty.nat} (h : Value v) :
    v = Tm.zero ∨ ∃ w, v = Tm.succ w := by
  rcases value_nat_cases h with hz | ⟨w, hw, _⟩
  · exact Or.inl hz
  · exact Or.inr ⟨w, hw⟩

/-! ### Step inversions with step counts -/

theorem stepsN_succ_inv (k : Nat) :
    ∀ {t u : Tm [] Ty.nat},
      StepsN k (Tm.succ t) u → ∃ v, u = Tm.succ v ∧ StepsN k t v := by
  induction k with
  | zero =>
      intro t u h
      cases h
      exact ⟨t, rfl, StepsN.zero t⟩
  | succ n ih =>
      intro t u h
      cases h with
      | succ hstep hrest =>
          cases hstep with
          | succ h' =>
              obtain ⟨v, heq, hsteps⟩ := ih hrest
              exact ⟨v, heq, StepsN.succ h' hsteps⟩

theorem stepsN_pred_inv (k : Nat) :
    ∀ {t u : Tm [] Ty.nat}, StepsN k (Tm.pred t) u → Value u →
      ∃ (j : Nat) (v : Tm [] Ty.nat),
        StepsN j t v ∧ Value v ∧ k = j + 1 ∧ Step (Tm.pred v) u := by
  induction k with
  | zero =>
      intro t u h hu
      cases h
      exact absurd hu (not_value_pred t)
  | succ n ih =>
      intro t u h hu
      cases h with
      | succ hstep hrest =>
          cases hstep with
          | pred_zero =>
              obtain ⟨rfl, rfl⟩ := stepsN_value hrest Value.zero
              exact ⟨0, Tm.zero, StepsN.zero _, Value.zero, rfl, Step.pred_zero⟩
          | pred_succ val =>
              obtain ⟨rfl, rfl⟩ := stepsN_value hrest val
              exact ⟨0, Tm.succ _, StepsN.zero _, Value.succ val, rfl,
                Step.pred_succ val⟩
          | pred h' =>
              obtain ⟨j, v, hsteps, hv, heq, hstep⟩ := ih hrest hu
              exact ⟨j + 1, v, StepsN.succ h' hsteps, hv, by omega, hstep⟩

theorem stepsN_ifz_inv (k : Nat) :
    ∀ {σ : Ty} {t : Tm [] Ty.nat} {a b u : Tm [] σ},
      StepsN k (Tm.ifz t a b) u → Value u →
      ∃ (j : Nat) (v : Tm [] Ty.nat) (i : Nat),
        StepsN j t v ∧ Value v ∧ k = j + 1 + i ∧
        ((v = Tm.zero ∧ StepsN i a u) ∨
          (∃ w : Tm [] Ty.nat, v = Tm.succ w ∧ StepsN i b u)) := by
  induction k with
  | zero =>
      intro σ t a b u h hu
      cases h
      exact absurd hu (not_value_ifz t a b)
  | succ n ih =>
      intro σ t a b u h hu
      cases h with
      | succ hstep hrest =>
          cases hstep with
          | ifz_zero =>
              exact ⟨0, Tm.zero, n, StepsN.zero _, Value.zero, by omega,
                Or.inl ⟨rfl, hrest⟩⟩
          | ifz_succ val =>
              exact ⟨0, Tm.succ _, n, StepsN.zero _, Value.succ val, by omega,
                Or.inr ⟨_, rfl, hrest⟩⟩
          | ifz h' =>
              obtain ⟨j, v, i, hsteps, hv, heq, hbr⟩ := ih hrest hu
              exact ⟨j + 1, v, i, StepsN.succ h' hsteps, hv, by omega, hbr⟩

theorem stepsN_cond_inv (k : Nat) :
    ∀ {σ : Ty} {c : Tm [] Ty.bool} {a b u : Tm [] σ},
      StepsN k (Tm.cond c a b) u → Value u →
      ∃ (j : Nat) (cv : Tm [] Ty.bool) (i : Nat),
        StepsN j c cv ∧ Value cv ∧ k = j + 1 + i ∧
        ((cv = Tm.tt ∧ StepsN i a u) ∨ (cv = Tm.ff ∧ StepsN i b u)) := by
  induction k with
  | zero =>
      intro σ c a b u h hu
      cases h
      exact absurd hu (not_value_cond c a b)
  | succ n ih =>
      intro σ c a b u h hu
      cases h with
      | succ hstep hrest =>
          cases hstep with
          | cond_tt =>
              exact ⟨0, Tm.tt, n, StepsN.zero _, Value.tt, by omega,
                Or.inl ⟨rfl, hrest⟩⟩
          | cond_ff =>
              exact ⟨0, Tm.ff, n, StepsN.zero _, Value.ff, by omega,
                Or.inr ⟨rfl, hrest⟩⟩
          | cond h' =>
              obtain ⟨j, cv, i, hsteps, hcv, heq, hbr⟩ := ih hrest hu
              exact ⟨j + 1, cv, i, StepsN.succ h' hsteps, hcv, by omega, hbr⟩

theorem stepsN_fix_inv (k : Nat) :
    ∀ {σ : Ty} {f : Tm [] (Ty.arr σ σ)} {u : Tm [] σ},
      StepsN k (Tm.fix f) u → Value u →
      ∃ j : Nat, k = j + 1 ∧ StepsN j (Tm.app f (Tm.fix f)) u := by
  induction k with
  | zero =>
      intro σ f u h hu
      cases h
      exact absurd hu (not_value_fix f)
  | succ n ih =>
      intro σ f u h hu
      cases h with
      | succ hstep hrest =>
          cases hstep with
          | fix => exact ⟨n, rfl, hrest⟩

/-! ### Reduction lemmas -/

theorem steps_succ {t t' : Tm [] Ty.nat} (h : Steps t t') :
    Steps (Tm.succ t) (Tm.succ t') := by
  induction h with
  | refl => exact .refl _
  | step _ hstep ih => exact .step ih (.succ hstep)

theorem steps_cond {σ : Ty} (a b : Tm [] σ) {c c' : Tm [] Ty.bool}
    (h : Steps c c') : Steps (Tm.cond c a b) (Tm.cond c' a b) := by
  induction h with
  | refl => exact .refl _
  | step _ hstep ih => exact .step ih (.cond hstep)

/-- The β-reduct of a value application reaches whatever the application
reaches. -/
theorem steps_app_lam_value {σ τ : Ty} {b : Tm (σ :: []) τ} {a : Tm [] σ}
    {v : Tm [] τ} (ha : Value a) (hv : Value v)
    (h : Steps (Tm.app (Tm.lam b) a) v) : Steps (subst0 b a) v := by
  obtain ⟨k, hk⟩ := steps_stepsN h
  obtain ⟨j1, c, j2, av, j3, hfstep, hast, hav, hbody, heq⟩ :=
    stepsN_app_inv k hk hv
  obtain ⟨hj1, hc⟩ := stepsN_value hfstep Value.lam
  subst hj1
  have hcb : c = b := by injection hc
  subst hcb
  obtain ⟨hj2, hav'⟩ := stepsN_value hast ha
  subst hj2
  subst hav'
  exact stepsN_steps hbody

/-! ### The relation -/

/-- The value relation and the term relation of a type.  Mutual recursion on
the type only. -/
def VEL (τ : Ty) :
    (Tm [] τ → Tm [] τ → Prop) × (Tm [] τ → Tm [] τ → Prop) :=
  match τ with
  | .nat =>
      let V : Tm [] Ty.nat → Tm [] Ty.nat → Prop := fun v v' => v = v'
      let E : Tm [] Ty.nat → Tm [] Ty.nat → Prop :=
        fun t t' => ∀ v, Value v → Steps t v →
          ∃ v', Value v' ∧ Steps t' v' ∧ V v v'
      (V, E)
  | .bool =>
      let V : Tm [] Ty.bool → Tm [] Ty.bool → Prop := fun v v' => v = v'
      let E : Tm [] Ty.bool → Tm [] Ty.bool → Prop :=
        fun t t' => ∀ v, Value v → Steps t v →
          ∃ v', Value v' ∧ Steps t' v' ∧ V v v'
      (V, E)
  | .arr σ ρ =>
      let p := VEL σ
      let q := VEL ρ
      let V : Tm [] (Ty.arr σ ρ) → Tm [] (Ty.arr σ ρ) → Prop :=
        fun v v' => ∀ (a a' : Tm [] σ), Value a → Value a' →
          p.1 a a' → q.2 (Tm.app v a) (Tm.app v' a')
      let E : Tm [] (Ty.arr σ ρ) → Tm [] (Ty.arr σ ρ) → Prop :=
        fun t t' => ∀ v, Value v → Steps t v →
          ∃ v', Value v' ∧ Steps t' v' ∧ V v v'
      (V, E)

/-- Value relatedness at a type. -/
def VL (τ : Ty) (v v' : Tm [] τ) : Prop := (VEL τ).1 v v'

/-- Term relatedness at a type. -/
def EL (τ : Ty) (t t' : Tm [] τ) : Prop := (VEL τ).2 t t'

theorem VL_nat (v v' : Tm [] Ty.nat) : VL Ty.nat v v' ↔ v = v' := Iff.rfl

theorem VL_bool (v v' : Tm [] Ty.bool) : VL Ty.bool v v' ↔ v = v' := Iff.rfl

theorem VL_arr {σ τ : Ty} (v v' : Tm [] (Ty.arr σ τ)) :
    VL (Ty.arr σ τ) v v' ↔
      ∀ (a a' : Tm [] σ), Value a → Value a' → VL σ a a' →
        EL τ (Tm.app v a) (Tm.app v' a') := Iff.rfl

theorem EL_def (τ : Ty) (t t' : Tm [] τ) :
    EL τ t t' ↔ ∀ v, Value v → Steps t v →
      ∃ v', Value v' ∧ Steps t' v' ∧ VL τ v v' := by
  cases τ with
  | nat => exact Iff.rfl
  | bool => exact Iff.rfl
  | arr σ ρ => exact Iff.rfl

theorem VL_to_EL {τ : Ty} {v v' : Tm [] τ} (hv : Value v) (hv' : Value v')
    (h : VL τ v v') : EL τ v v' := by
  rw [EL_def]
  intro w hw hs
  have hwv : w = v := steps_value_self hv hs
  subst hwv
  exact ⟨v', hv', Steps.refl v', h⟩

theorem EL_zero : EL Ty.nat Tm.zero Tm.zero := by
  rw [EL_def]
  intro v hv hs
  have h : v = Tm.zero := steps_value_self Value.zero hs
  subst h
  exact ⟨Tm.zero, Value.zero, Steps.refl _, rfl⟩

theorem EL_tt : EL Ty.bool Tm.tt Tm.tt := by
  rw [EL_def]
  intro v hv hs
  have h : v = Tm.tt := steps_value_self Value.tt hs
  subst h
  exact ⟨Tm.tt, Value.tt, Steps.refl _, rfl⟩

theorem EL_ff : EL Ty.bool Tm.ff Tm.ff := by
  rw [EL_def]
  intro v hv hs
  have h : v = Tm.ff := steps_value_self Value.ff hs
  subst h
  exact ⟨Tm.ff, Value.ff, Steps.refl _, rfl⟩

/-! ### Closure under application -/

theorem EL_app {σ τ : Ty} {f f' : Tm [] (Ty.arr σ τ)} {a a' : Tm [] σ}
    (hf : EL (Ty.arr σ τ) f f') (ha : EL σ a a') :
    EL τ (Tm.app f a) (Tm.app f' a') := by
  rw [EL_def] at hf ha ⊢
  intro v hv hsteps
  obtain ⟨k, hk⟩ := steps_stepsN hsteps
  obtain ⟨j1, b, j2, av, j3, hfstep, hast, hav, hbody, heq⟩ :=
    stepsN_app_inv k hk hv
  obtain ⟨v', hv', hf'step, hVf⟩ := hf (Tm.lam b) Value.lam (stepsN_steps hfstep)
  obtain ⟨b', rfl⟩ : ∃ b', v' = Tm.lam b' := by cases hv' with | lam => exact ⟨_, rfl⟩
  obtain ⟨av', hav', ha'step, hVa⟩ := ha av hav (stepsN_steps hast)
  rw [VL_arr] at hVf
  have hApp : EL τ (Tm.app (Tm.lam b) av) (Tm.app (Tm.lam b') av') :=
    hVf av av' hav hav' hVa
  rw [EL_def] at hApp
  obtain ⟨w, hw, hwsteps, hVw⟩ :=
    hApp v hv (stepsN_steps (StepsN.succ (Step.app_lam hav) hbody))
  refine ⟨w, hw, ?_, hVw⟩
  exact steps_trans_aux (steps_app_fun a' hf'step)
    (steps_trans_aux (steps_app_arg (f := Tm.lam b') Value.lam ha'step) hwsteps)

/-! ### Compatibility of the term relation -/

theorem EL_succ {t t' : Tm [] Ty.nat} (h : EL Ty.nat t t') :
    EL Ty.nat (Tm.succ t) (Tm.succ t') := by
  rw [EL_def] at h ⊢
  intro v hv hs
  obtain ⟨k, hk⟩ := steps_stepsN hs
  obtain ⟨w, rfl, hwk⟩ := stepsN_succ_inv k hk
  have hw : Value w := by cases hv with | succ hw => exact hw
  obtain ⟨w', hw', hw'steps, hV⟩ := h w hw (stepsN_steps hwk)
  rw [VL_nat] at hV
  exact ⟨Tm.succ w', Value.succ hw', steps_succ hw'steps, by rw [VL_nat, hV]⟩

theorem EL_pred {t t' : Tm [] Ty.nat} (h : EL Ty.nat t t') :
    EL Ty.nat (Tm.pred t) (Tm.pred t') := by
  rw [EL_def] at h ⊢
  intro v hv hs
  obtain ⟨k, hk⟩ := steps_stepsN hs
  obtain ⟨j, v0, hsteps, hv0, heq, hstep⟩ := stepsN_pred_inv k hk hv
  obtain ⟨v0', hv0', hsteps', hV⟩ := h v0 hv0 (stepsN_steps hsteps)
  rw [VL_nat] at hV
  rw [← hV] at hsteps'
  exact ⟨v, hv, steps_trans_aux (steps_pred hsteps') (Steps.step (Steps.refl _) hstep), rfl⟩

theorem EL_ifz {σ : Ty} {t t' : Tm [] Ty.nat} {a a' b b' : Tm [] σ}
    (ht : EL Ty.nat t t') (ha : EL σ a a') (hb : EL σ b b') :
    EL σ (Tm.ifz t a b) (Tm.ifz t' a' b') := by
  rw [EL_def] at ht ha hb ⊢
  intro v hv hs
  obtain ⟨k, hk⟩ := steps_stepsN hs
  obtain ⟨j, v0, i, hsteps, hv0, heq, hbr⟩ := stepsN_ifz_inv k hk hv
  obtain ⟨v0', hv0', hsteps', hV⟩ := ht v0 hv0 (stepsN_steps hsteps)
  rw [VL_nat] at hV
  rw [hV] at hv0 hbr
  rcases hbr with ⟨rfl, hsteps''⟩ | ⟨w, rfl, hsteps''⟩
  · obtain ⟨w', hw', hw'steps, hV'⟩ := ha v hv (stepsN_steps hsteps'')
    refine ⟨w', hw', ?_, hV'⟩
    exact steps_trans_aux (steps_ifz a' b' hsteps')
      (steps_trans_aux (Steps.step (Steps.refl _) Step.ifz_zero) hw'steps)
  · cases hv0 with
    | succ hw0 =>
        obtain ⟨w', hw', hw'steps, hV'⟩ := hb v hv (stepsN_steps hsteps'')
        exact ⟨w', hw', steps_trans_aux (steps_ifz a' b' hsteps')
          (steps_trans_aux (Steps.step (Steps.refl _) (Step.ifz_succ hw0)) hw'steps), hV'⟩

theorem EL_cond {σ : Ty} {c c' : Tm [] Ty.bool} {a a' b b' : Tm [] σ}
    (hc : EL Ty.bool c c') (ha : EL σ a a') (hb : EL σ b b') :
    EL σ (Tm.cond c a b) (Tm.cond c' a' b') := by
  rw [EL_def] at hc ha hb ⊢
  intro v hv hs
  obtain ⟨k, hk⟩ := steps_stepsN hs
  obtain ⟨j, cv, i, hsteps, hcv, heq, hbr⟩ := stepsN_cond_inv k hk hv
  obtain ⟨cv', hcv', hsteps', hV⟩ := hc cv hcv (stepsN_steps hsteps)
  rw [VL_bool] at hV
  rw [hV] at hcv hbr
  rcases hbr with ⟨rfl, hsteps''⟩ | ⟨rfl, hsteps''⟩
  · obtain ⟨w', hw', hw'steps, hV'⟩ := ha v hv (stepsN_steps hsteps'')
    refine ⟨w', hw', ?_, hV'⟩
    exact steps_trans_aux (steps_cond a' b' hsteps')
      (steps_trans_aux (Steps.step (Steps.refl _) Step.cond_tt) hw'steps)
  · obtain ⟨w', hw', hw'steps, hV'⟩ := hb v hv (stepsN_steps hsteps'')
    refine ⟨w', hw', ?_, hV'⟩
    exact steps_trans_aux (steps_cond a' b' hsteps')
      (steps_trans_aux (Steps.step (Steps.refl _) Step.cond_ff) hw'steps)

theorem EL_beta {σ τ : Ty} {b b' : Tm (σ :: []) τ} {a a' : Tm [] σ}
    (ha : Value a) (ha' : Value a')
    (h : EL τ (subst0 b a) (subst0 b' a')) :
    EL τ (Tm.app (Tm.lam b) a) (Tm.app (Tm.lam b') a') := by
  rw [EL_def] at h ⊢
  intro v hv hs
  have h' : Steps (subst0 b a) v := steps_app_lam_value ha hv hs
  obtain ⟨v', hv', hv'steps, hV⟩ := h v hv h'
  exact ⟨v', hv', steps_trans_aux (Steps.step (Steps.refl _) (Step.app_lam ha')) hv'steps, hV⟩

theorem EL_fix {σ : Ty} {F F' : Tm [] (Ty.arr σ σ)} (hF : EL (Ty.arr σ σ) F F') :
    EL σ (Tm.fix F) (Tm.fix F') := by
  rw [EL_def] at hF ⊢
  intro v hv hs
  obtain ⟨k, hk⟩ := steps_stepsN hs
  have key : ∀ n j, j ≤ n → ∀ v, Value v → StepsN j (Tm.fix F) v →
      ∃ v', Value v' ∧ Steps (Tm.fix F') v' ∧ VL σ v v' := by
    intro n
    induction n with
    | zero =>
        intro j hj v hv hk
        have hj0 : j = 0 := by omega
        subst hj0
        cases hk
        exact absurd hv (not_value_fix F)
    | succ n ih =>
        intro j hj v hv hk
        cases j with
        | zero => cases hk; exact absurd hv (not_value_fix F)
        | succ m =>
            cases hk with
            | succ hstep hrest =>
                cases hstep with
                | fix =>
                    obtain ⟨j1, b, j2, av, j3, hFstep, hfixstep, hav, hbody, heq⟩ :=
                      stepsN_app_inv m hrest hv
                    obtain ⟨v', hv', hF'step, hVf⟩ :=
                      hF (Tm.lam b) Value.lam (stepsN_steps hFstep)
                    obtain ⟨b', rfl⟩ : ∃ b', v' = Tm.lam b' := by
                      cases hv' with | lam => exact ⟨_, rfl⟩
                    obtain ⟨av', hav', hfix'step, hVav⟩ := ih j2 (by omega) av hav hfixstep
                    rw [VL_arr] at hVf
                    have hApp : EL σ (Tm.app (Tm.lam b) av) (Tm.app (Tm.lam b') av') :=
                      hVf av av' hav hav' hVav
                    rw [EL_def] at hApp
                    obtain ⟨w, hw, hwsteps, hVw⟩ :=
                      hApp v hv (stepsN_steps (StepsN.succ (Step.app_lam hav) hbody))
                    exact ⟨w, hw, steps_trans_aux (Steps.step (Steps.refl _) Step.fix)
                      (steps_trans_aux (steps_app_fun (Tm.fix F') hF'step)
                        (steps_trans_aux (steps_app_arg (f := Tm.lam b') Value.lam
                          hfix'step) hwsteps)), hVw⟩
  exact key k k (by omega) v hv hk

/-! ### The fundamental theorem -/

theorem EL_fundamental {Γ : List Ty} {τ : Ty} (s : Tm Γ τ)
    (γ γ' : Env Γ)
    (hpt : ∀ {υ : Ty} (v : Var Γ υ), EL υ (γ v) (γ' v)) :
    EL τ (subst γ s) (subst γ' s) := by
  induction s with
  | var v => exact hpt v
  | zero => exact EL_zero
  | tt => exact EL_tt
  | ff => exact EL_ff
  | succ t ih => exact EL_succ (ih γ γ' hpt)
  | pred t ih => exact EL_pred (ih γ γ' hpt)
  | ifz n a b ih_n ih_a ih_b =>
      exact EL_ifz (ih_n γ γ' hpt) (ih_a γ γ' hpt) (ih_b γ γ' hpt)
  | cond c a b ih_c ih_a ih_b =>
      exact EL_cond (ih_c γ γ' hpt) (ih_a γ γ' hpt) (ih_b γ γ' hpt)
  | app f a ih_f ih_a => exact EL_app (ih_f γ γ' hpt) (ih_a γ γ' hpt)
  | fix f ih => exact EL_fix (ih γ γ' hpt)
  | lam b ih =>
      have hV : VL (Ty.arr _ _) (Tm.lam (subst (liftSubst γ) b))
          (Tm.lam (subst (liftSubst γ') b)) := by
        rw [VL_arr]
        intro a a' ha ha' hVa
        apply EL_beta ha ha'
        rw [← subst_envCons b γ a, ← subst_envCons b γ' a']
        apply ih (EnvCons a γ) (EnvCons a' γ')
        intro υ v
        cases v with
        | here => exact VL_to_EL ha ha' hVa
        | there w => exact hpt w
      exact VL_to_EL Value.lam Value.lam hV

/-! ### Post-composition with similarity -/

theorem EL_post_sim (τ : Ty) :
    ∀ {t u s : Tm [] τ}, EL τ t u → Simulates u s → EL τ t s := by
  induction τ with
  | nat =>
      intro t u s h hs
      rw [EL_def] at h ⊢
      intro v hv hsteps
      obtain ⟨v1, hv1, hs1, hV⟩ := h v hv hsteps
      rw [VL_nat] at hV
      subst hV
      obtain ⟨R, hR, hus⟩ := hs
      obtain ⟨v2, hv2, hs2, heq⟩ := hR.1 u s hus v hv1 hs1
      exact ⟨v2, hv2, hs2, by rw [VL_nat]; exact heq⟩
  | bool =>
      intro t u s h hs
      rw [EL_def] at h ⊢
      intro v hv hsteps
      obtain ⟨v1, hv1, hs1, hV⟩ := h v hv hsteps
      rw [VL_bool] at hV
      subst hV
      obtain ⟨R, hR, hus⟩ := hs
      obtain ⟨v2, hv2, hs2, heq⟩ := hR.2.1 u s hus v hv1 hs1
      exact ⟨v2, hv2, hs2, by rw [VL_bool]; exact heq⟩
  | arr σ τ ih_σ ih_τ =>
      intro t u s h hs
      rw [EL_def] at h ⊢
      intro v hv hsteps
      obtain ⟨v1, hv1, hs1, hV⟩ := h v hv hsteps
      obtain ⟨R, hR, hus⟩ := hs
      obtain ⟨v2, hv2, hs2, hRval⟩ := (hR.2.2 u s hus).1 v1 hv1 hs1
      refine ⟨v2, hv2, hs2, ?_⟩
      have hsim : Simulates v1 v2 := ⟨R, hR, hRval⟩
      rw [VL_arr] at hV ⊢
      intro a a' ha ha' hVa
      have h1 : EL τ (Tm.app v a) (Tm.app v1 a') := hV a a' ha ha' hVa
      have hsame : Simulates (Tm.app v1 a') (Tm.app v2 a') :=
        (is_simulation_simulates.2.2 v1 v2 hsim).2 a'
      exact ih_τ h1 hsame

/-! ### Similarity is contained in the relation -/

theorem simulates_to_EL {τ : Ty} {t u : Tm [] τ} (h : Simulates t u) :
    EL τ t u := by
  cases τ with
  | nat =>
      rw [EL_def]
      intro v hv hs
      obtain ⟨R, hR, htu⟩ := h
      obtain ⟨v', hv', hs', heq⟩ := hR.1 t u htu v hv hs
      exact ⟨v', hv', hs', by rw [VL_nat]; exact heq⟩
  | bool =>
      rw [EL_def]
      intro v hv hs
      obtain ⟨R, hR, htu⟩ := h
      obtain ⟨v', hv', hs', heq⟩ := hR.2.1 t u htu v hv hs
      exact ⟨v', hv', hs', by rw [VL_bool]; exact heq⟩
  | arr σ τ =>
      rw [EL_def]
      intro v hv hs
      obtain ⟨R, hR, htu⟩ := h
      obtain ⟨v', hv', hs', hRval⟩ := (hR.2.2 t u htu).1 v hv hs
      refine ⟨v', hv', hs', ?_⟩
      have hsim : Simulates v v' := ⟨R, hR, hRval⟩
      obtain ⟨b, rfl⟩ := value_arr_cases hv
      obtain ⟨b', rfl⟩ : ∃ b', v' = Tm.lam b' := by
        cases hv' with | lam => exact ⟨_, rfl⟩
      rw [VL_arr]
      intro a a' ha ha' hVa
      apply EL_beta ha ha'
      have h1 : EL τ (subst0 b a) (subst0 b a') := by
        apply EL_fundamental b (substHere a) (substHere a')
        intro υ w
        cases w with
        | here => exact VL_to_EL ha ha' hVa
        | there x => exact (var_nil x).elim
      have hsame : Simulates (Tm.app (Tm.lam b) a') (Tm.app (Tm.lam b') a') :=
        (is_simulation_simulates.2.2 _ _ hsim).2 a'
      have h2 : Simulates (subst0 b a') (subst0 b' a') :=
        simulates_steps hsame
          (Steps.step (Steps.refl _) (Step.app_lam ha'))
          (Steps.step (Steps.refl _) (Step.app_lam ha'))
      exact EL_post_sim τ h1 h2

/-! ### The relation is a simulation -/

theorem EL_refl (τ : Ty) (t : Tm [] τ) : EL τ t t := by
  cases τ with
  | nat =>
      rw [EL_def]
      intro v hv hs
      exact ⟨v, hv, hs, rfl⟩
  | bool =>
      rw [EL_def]
      intro v hv hs
      exact ⟨v, hv, hs, rfl⟩
  | arr σ τ =>
      rw [EL_def]
      intro v hv hs
      refine ⟨v, hv, hs, ?_⟩
      obtain ⟨b, rfl⟩ := value_arr_cases hv
      rw [VL_arr]
      intro a a' ha ha' hVa
      apply EL_beta ha ha'
      apply EL_fundamental b (substHere a) (substHere a')
      intro υ w
      cases w with
      | here => exact VL_to_EL ha ha' hVa
      | there x => exact (var_nil x).elim

theorem is_simulation_EL :
    IsSimulation (fun {σ : Ty} (t u : Tm [] σ) => EL σ t u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t u h v hv hs
    rw [EL_def] at h
    obtain ⟨v', hv', hs', hV⟩ := h v hv hs
    rw [VL_nat] at hV
    exact ⟨v', hv', hs', hV⟩
  · intro t u h v hv hs
    rw [EL_def] at h
    obtain ⟨v', hv', hs', hV⟩ := h v hv hs
    rw [VL_bool] at hV
    exact ⟨v', hv', hs', hV⟩
  · intro σ τ t u h
    refine ⟨?_, ?_⟩
    · intro v hv hs
      rw [EL_def] at h
      obtain ⟨v', hv', hs', hV⟩ := h v hv hs
      exact ⟨v', hv', hs', VL_to_EL hv hv' hV⟩
    · intro a
      exact EL_app h (EL_refl σ a)

theorem EL_sub_simulates {τ : Ty} {t u : Tm [] τ} (h : EL τ t u) :
    Simulates t u :=
  ⟨fun {σ} (x y : Tm [] σ) => EL σ x y, is_simulation_EL, h⟩

/-! ### Targets 9-12 -/

theorem sim_congruent_proof : sim_congruent := by
  intro σ τ C t u htu
  have hE : EL σ t u := simulates_to_EL htu
  have hpt : ∀ {υ : Ty} (w : Var [σ] υ), EL υ (substHere t w) (substHere u w) := by
    intro υ w
    cases w with
    | here => exact hE
    | there x => exact (var_nil x).elim
  have hC : EL τ (subst (substHere t) C) (subst (substHere u) C) :=
    EL_fundamental C (substHere t) (substHere u) hpt
  exact EL_sub_simulates hC

theorem sim_implies_contextual_le_proof : sim_implies_contextual_le :=
  sim_implies_contextual_le_of_congruent sim_congruent_proof

theorem contextual_le_iff_sim_proof : contextual_le_iff_sim :=
  contextual_le_iff_sim_of_sim_implies_contextual_le sim_implies_contextual_le_proof

theorem contextual_eq_iff_sim_both_proof : contextual_eq_iff_sim_both :=
  contextual_eq_iff_sim_both_of_iff contextual_le_iff_sim_proof

end Problems.Hard.Pcf
