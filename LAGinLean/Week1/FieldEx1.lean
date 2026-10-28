import Mathlib.Tactic

variable (p : ℕ) [hp : Fact p.Prime]

@[ext]
structure F where
  val : ℕ
  cond : val < p
  deriving DecidableEq

variable {p}

namespace F

-- ignore this proof
instance : Finite (F p) := .intro ⟨fun x ↦ ⟨x.1, x.2⟩, fun x ↦ ⟨x.1, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Zero (F p) where
  zero := ⟨0, hp.out.pos⟩

instance : One (F p) where
  one := ⟨1, hp.out.one_lt⟩

instance : Add (F p) where
  add x y := ⟨(x.val + y.val) % p, Nat.mod_lt _ hp.out.pos⟩

instance : Mul (F p) where
  mul x y := ⟨(x.val * y.val) % p, Nat.mod_lt _ hp.out.pos⟩

instance : Neg (F p) where
  neg x := ⟨(p - x.val) % p, Nat.mod_lt _ hp.out.pos⟩

/-- Additive axioms -/

lemma add_comm (a b : F p) : a + b = b + a := by
  ext
  calc  (a + b).val
    _ = (a.val + b.val) % p := rfl
    _ = (b.val + a.val) % p := by rw?
    _ = (b + a).val         := rfl

lemma zero_add (a : F p) : 0 + a = a := by
  have : a.val < p := a.cond
  ext
  calc  (0 + a).val
    _ = (0 + a.val) % p := rfl
    _ = a.val % p       := by rw?
    _ = a.val           := by rw?

lemma add_zero (a : F p) : a + 0 = a := by
  rw [add_comm, zero_add]

lemma add_assoc (a b c : F p) : (a + b) + c = a + (b + c) := by
  ext
  calc (a + b + c).val
    _ = ((a.val + b.val) % p + c.val) % p := rfl
    _ = (a.val + b.val + c.val) % p := by rw [Nat.mod_add_mod]
    _ = (a.val + (b.val + c.val)) % p := by rw [Nat.add_assoc]
    _ = (a.val + (b.val + c.val) % p) % p := by rw [Nat.add_mod_mod]
    _ = (a + (b + c)).val := rfl

lemma add_left_neg (a : F p) : -a + a = 0 := by
  have := a.cond.le
  ext
  calc (-a + a).val
    _ = ((p - a.val) % p + a.val) % p := rfl
    _ = (p - a.val + a.val) % p := by rw [Nat.mod_add_mod]
    _ = p % p := by rw [Nat.sub_add_cancel this]
    _ = 0 := by rw [Nat.mod_self]


/-- Multiplicative axioms -/

lemma mul_comm (a b : F p) : a * b = b * a := by
  ext
  calc (a * b).val
    _ = (a.val * b.val) % p := rfl
    _ = (b.val * a.val) % p := by rw [Nat.mul_comm]


lemma zero_mul (a : F p) : 0 * a = 0 := by
  ext
  calc (0 * a).val
    _ = (0 * a.val) % p := rfl
    _ = 0 := by rw [Nat.zero_mul, Nat.zero_mod]


lemma mul_zero (a : F p) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

lemma one_mul (a : F p) : 1 * a = a := by
  have : a.val < p := a.cond
  ext
  calc (1 * a).val
    _ = (1 * a.val) % p := rfl
    _ = a.val % p := by rw [Nat.one_mul]
    _ = a.val := by rw [Nat.mod_eq_of_lt this]


lemma mul_one (a : F p) : a * 1 = a := by
  rw [mul_comm, one_mul]

lemma mul_assoc (a b c : F p) : (a * b) * c = a * (b * c) := by
  ext
  calc (a * b * c).val
    _ = ((a.val * b.val) % p * c.val) % p := rfl
    _ = (a.val * b.val * c.val) % p := by rw [Nat.mod_mul_mod]
    _ = (a.val * (b.val * c.val)) % p := by rw [Nat.mul_assoc]
    _ = (a.val * (b.val * c.val % p)) % p := by rw [← Nat.mul_mod_mod]


/-- Distributivity axioms -/

lemma left_distrib (a b c : F p) : a * (b + c) = a * b + a * c := by
  ext
  calc (a * (b + c)).val
    _ = (a.val * ((b.val + c.val) % p)) % p := rfl
    _ = (a.val * (b.val + c.val)) % p := by rw [Nat.mul_mod_mod]
    _ = (a.val * b.val + a.val * c.val) % p := by rw [Nat.mul_add]
    _ = ((a.val * b.val) % p + (a.val * c.val) % p) % p := by rw [Nat.add_mod]

lemma right_distrib (a b c : F p) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm b, mul_comm]

/-
This is the hard part, both mathematically and lean-wise.

Here I have listed some lemmas that you may or may not need.
-/

#check Nat.dvd_of_mod_eq_zero
#check Nat.Prime.dvd_mul
#check Nat.eq_zero_of_dvd_of_lt
#check Finite.injective_iff_surjective

lemma invertibility (a : F p) (ha : a ≠ 0) : ∃ b : F p, a * b = 1 := by
  have hp : p.Prime := hp.out
  have hint₁ : ∀ x, a * x = 0 → x = 0 := by
    intro x hx
    rw [F.ext_iff] at hx
    change a.val * x.val % p = 0 at hx
    apply Nat.dvd_of_mod_eq_zero at hx
    rw [Nat.Prime.dvd_mul hp] at hx
    cases hx with
    | inl hpa =>
      apply False.elim
      apply ha
      ext
      exact Nat.eq_zero_of_dvd_of_lt hpa a.cond
    | inr hpx =>
      ext
      exact Nat.eq_zero_of_dvd_of_lt hpx x.cond

  have hint₂ : Function.Injective (a * ·) := by
    intro x y (e : a * x = a * y)
    apply congrArg (· + a * (-y)) at e
    rw [← left_distrib, ← left_distrib, add_comm y, add_left_neg, mul_zero] at e
    apply hint₁ at e
    apply congrArg (· + y) at e
    rw [add_assoc, add_left_neg, add_zero, zero_add] at e
    exact e

  have hint₃ : Function.Surjective (a * ·) := by
    exact Finite.injective_iff_surjective.mp hint₂

  have hint₄ : ∀ b, ∃ c, a * c = b := hint₃
  
  exact hint₄ 1

/-- Put it all together -/

noncomputable
instance : Field (F p) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zsmul := zsmulRec
  add_left_neg := add_left_neg
  mul_comm := mul_comm
  inv a := if h : a = 0 then 0 else (invertibility a h).choose
  exists_pair_ne := ⟨0, 1, fun e ↦ by cases congr($e.1)⟩
  mul_inv_cancel a h := show a * dite _ _ _ = 1 from dif_neg h ▸ (invertibility a h).choose_spec
  inv_zero := dif_pos rfl
  qsmul := qsmulRec _

end F
