module

namespace DY.Bytes.NormalizationMetaTheory

structure Term {α: Type} (arity: α → Nat) where
  f: α
  args: Fin (arity f) → Term arity

inductive WithVariable (α: Type) where
  | Constructor (f: α)
  | Variable (i: Nat)

def WithVariable.arity (arity: α → Nat) (f: WithVariable α): Nat :=
  match f with
  | .Constructor f => arity f
  | .Variable _ => 0

abbrev GroundTerm {α: Type} (arity: α → Nat) := Term arity
abbrev VarTerm {α: Type} (arity: α → Nat) := Term (WithVariable.arity arity)
abbrev Substitution {α: Type} (arity: α → Nat) := Nat → GroundTerm arity
abbrev Equations {α: Type} (arity: α → Nat) := List (VarTerm arity × VarTerm arity)
abbrev NormConstructor {α: Type} (arity: α → Nat) := (f: α) → (args: Fin (arity f) → GroundTerm arity) → GroundTerm arity

variable {α: Type} {arity: α → Nat}

def Term.applySubst (t: VarTerm arity) (σ: Substitution arity): GroundTerm arity :=
  match t with
  | { f := .Constructor f, args } => {
    f := f
    args i := (args i).applySubst σ
  }
  | { f := .Variable i, args := _ } => σ i

def Term.injVar (t: GroundTerm arity): VarTerm arity :=
  let { f, args } := t
  {
    f := .Constructor f
    args i := (args i).injVar
  }

-- sanity check
theorem Term.applySubst_injVar
  (t: GroundTerm arity) (σ: Substitution arity)
  : t.injVar.applySubst σ = t
:= by
  induction t
  simp_all [applySubst, injVar]

inductive EquationalEq (E: Equations arity): GroundTerm arity → GroundTerm arity → Prop where
  | Refl (t: GroundTerm arity): EquationalEq E t t
  | Trans (t1 t2 t3: GroundTerm arity) (h12: EquationalEq E t1 t2) (h23: EquationalEq E t2 t3): EquationalEq E t1 t3
  | Congr
    (f: α) (args1 args2: Fin (arity f) → GroundTerm arity)
    (h: ∀ i, EquationalEq E (args1 i) (args2 i))
    : EquationalEq E {f, args := args1} {f, args := args2}
  | Equation
    (lhs rhs: VarTerm arity)
    (h_lhs_rhs: (lhs, rhs) ∈ E ∨ (rhs, lhs) ∈ E)
    (σ: Substitution arity)
    : EquationalEq E (lhs.applySubst σ) (rhs.applySubst σ)

local notation lhs:50 " ≈" "(" E ") " rhs:50 => EquationalEq E lhs rhs

theorem EquationalEq.refl
  (E: Equations arity) (t: GroundTerm arity)
  : t ≈(E) t
:= .Refl t

theorem EquationalEq.symm
  (E: Equations arity) (t1 t2: GroundTerm arity)
  (h: t1 ≈(E) t2)
  : t2 ≈(E) t1
:= by
  induction h
  case Refl t => exact .Refl t
  case Trans t1 t2 t3 h12 h23 h21 h32 => exact .Trans t3 t2 t1 h32 h21
  case Congr f args1 args2 h ih => exact .Congr f args2 args1 ih
  case Equation lhs rhs h σ => exact .Equation rhs lhs (by grind) σ

theorem EquationalEq.trans
  (E: Equations arity) (t1 t2 t3: GroundTerm arity)
  (h12: t1 ≈(E) t2)
  (h23: t2 ≈(E) t3)
  : t1 ≈(E) t3
:= .Trans t1 t2 t3 h12 h23

theorem EquationalEq.congr
  (E: Equations arity)
  (f: α) (args1 args2: Fin (arity f) → GroundTerm arity)
  (h: ∀ i, (args1 i) ≈(E) (args2 i))
  : {f, args := args1} ≈(E) {f, args := args2}
:= .Congr f args1 args2 h

-- for `calc` proofs
instance (E: Equations arity): Trans (EquationalEq E) (EquationalEq E) (EquationalEq E) where
  trans := EquationalEq.trans E _ _ _

structure IsNormalizingFor (E: Equations arity) (N: GroundTerm arity → GroundTerm arity) where
  eq_implies: ∀ lhs rhs σ, ((lhs, rhs) ∈ E) → N (lhs.applySubst σ) = N (rhs.applySubst σ)
  implies_eq: ∀ t, t ≈(E) (N t)
  congr: ∀ f args, N { f, args } = N { f, args i := N (args i) }

theorem theorem1.direct
  (E: Equations arity) (N: GroundTerm arity → GroundTerm arity) (h_N: IsNormalizingFor E N)
  (t1 t2: GroundTerm arity)
  : N t1 = N t2 →
    t1 ≈(E) t2
:= by
  have h1 := h_N.implies_eq t1
  have h2 := h_N.implies_eq t2
  grind [EquationalEq.trans, EquationalEq.symm]

theorem theorem1.indirect
  (E: Equations arity) (N: GroundTerm arity → GroundTerm arity) (h_N: IsNormalizingFor E N)
  (t1 t2: GroundTerm arity)
  : t1 ≈(E) t2 →
    N t1 = N t2
:= by
  intro h
  induction h
  case Refl t => grind
  case Trans t1 t2 t3 h12 h23 h21 h32 => grind
  case Congr f args1 args2 h ih =>
    have := h_N.congr f args1
    have := h_N.congr f args2
    grind
  case Equation lhs rhs h σ =>
    have := h_N.eq_implies lhs rhs σ
    have := h_N.eq_implies rhs lhs σ
    grind

theorem theorem1
  (E: Equations arity) (N: GroundTerm arity → GroundTerm arity) (h_N: IsNormalizingFor E N)
  (t1 t2: GroundTerm arity)
  : t1 ≈(E) t2 ↔
    N t1 = N t2
:= by
  grind [theorem1.direct, theorem1.indirect]

def myN (normMk: NormConstructor arity) (t: Term arity) :=
  let {f, args} := t
  normMk f (fun i => myN normMk (args i))

def IsNormalized (N: Term arity → Term arity) (t: Term arity): Prop :=
  N t = t

structure NormConstructorGood (E: Equations arity) (normMk: NormConstructor arity) where
  eq_implies: ∀ lhs rhs σ, (lhs, rhs) ∈ E → myN normMk (lhs.applySubst σ) = myN normMk (rhs.applySubst σ)
  implies_eq: ∀ f args, { f, args } ≈(E) (normMk f args)
  congr: ∀ (f: α) (args: Fin (arity f) → GroundTerm arity), (∀ i, IsNormalized (myN normMk) (args i)) → IsNormalized (myN normMk) (normMk f args)

theorem myN_idempotent
  (E: Equations arity) (normMk: NormConstructor arity)
  (h_normMk: NormConstructorGood E normMk)
  : ∀ t, myN normMk (myN normMk t) = myN normMk t
:= by
  intro t
  induction t
  rename_i f args ih
  calc myN normMk (myN normMk { f, args })
    _ = myN normMk (normMk f (fun i => myN normMk (args i))) := by simp only [myN]
    _ = normMk f (fun i => myN normMk (args i)) := by
      have := h_normMk.congr f (fun i => myN normMk (args i)) (fun i => ih i)
      simp_all [IsNormalized]
    _ = myN normMk { f, args } := by simp only [myN]

theorem theorem2
  (E: Equations arity) (normMk: NormConstructor arity) (h_normMk: NormConstructorGood E normMk)
  : IsNormalizingFor E (myN normMk)
where
  eq_implies := by
    intro lhs rhs σ h_lhs_rhs
    exact h_normMk.eq_implies lhs rhs σ h_lhs_rhs
  implies_eq t := by
    induction t
    rename_i f args ih
    calc
      _ ≈(E) { f := f, args := fun i => myN normMk (args i) } := EquationalEq.congr _ _ _ _ ih
      _ ≈(E) (normMk f fun i => myN normMk (args i)) := h_normMk.implies_eq f (fun i => myN normMk (args i))
  congr := by
    intro f args
    calc myN normMk { f := f, args := args }
      _ = normMk f (fun i => myN normMk (args i)) := by dsimp only [myN]
      _ = normMk f (fun i => myN normMk (myN normMk (args i))) := by simp only [myN_idempotent E normMk h_normMk]
      _ = myN normMk { f := f, args := fun i => myN normMk (args i) } := by dsimp only [myN]

theorem final_theorem
  (E: Equations arity) (normMk: NormConstructor arity) (h_normMk: NormConstructorGood E normMk)
  : ∀ t1 t2,
    t1 ≈(E) t2 ↔ myN normMk t1 = myN normMk t2
:= theorem1 _ _ (theorem2 E normMk h_normMk)

end DY.Bytes.NormalizationMetaTheory
