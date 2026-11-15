import Mathlib

/- Adapted from OpenAI math, UnitDistances/Radicals.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0. -/

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

def SquareIndependent {K : Type u} [CommMonoid K] (ds : List K) : Prop :=
  ∀ s : List K, s.Sublist ds → s ≠ [] → ∀ c : K, s.prod ≠ c ^ 2

section Quadratic

variable {K : Type u} [Field K] [CharZero K] (a b : K)

theorem square_in_quadratic_iff :
    (∃ z : QuadraticAlgebra K a 0, z ^ 2 = algebraMap K _ b) ↔
      (∃ x : K, x ^ 2 = b) ∨ (∃ y : K, a * y ^ 2 = b) := by
  constructor
  · rintro ⟨z, hz⟩
    have hr := congrArg QuadraticAlgebra.re hz
    have hi := congrArg QuadraticAlgebra.im hz
    simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re] at hr
    simp only [pow_two, QuadraticAlgebra.im_mul, zero_mul, add_zero,
      QuadraticAlgebra.algebraMap_im, mul_comm z.im z.re] at hi
    have hi' : z.re * z.im = 0 := by linear_combination hi / 2
    rcases mul_eq_zero.mp hi' with hx | hy
    · right; exact ⟨z.im, by simpa [hx, pow_two, mul_assoc] using hr⟩
    · left; exact ⟨z.re, by simpa [hy, pow_two] using hr⟩
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · refine ⟨⟨x, 0⟩, ?_⟩
      ext <;> simp [pow_two, ← hx]
    · refine ⟨⟨0, y⟩, ?_⟩
      ext <;> simp [pow_two, ← hy, mul_assoc]

def quadraticFlip : QuadraticAlgebra K a 0 ≃+* QuadraticAlgebra K a 0 where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp; ring
  map_add' z w := by ext <;> simp; ring

omit [CharZero K] in
@[simp] theorem quadraticFlip_cast (x : K) :
    quadraticFlip a (algebraMap K _ x) = algebraMap K _ x := by
  ext <;> simp [quadraticFlip]

omit [CharZero K] in
@[simp] theorem quadraticFlip_omega :
    quadraticFlip a (QuadraticAlgebra.omega : QuadraticAlgebra K a 0) =
      -QuadraticAlgebra.omega := by
  ext <;> simp [quadraticFlip, QuadraticAlgebra.omega]

def quadraticLift (σ : K ≃+* K) (ha : σ a = a) :
    QuadraticAlgebra K a 0 ≃+* QuadraticAlgebra K a 0 where
  toFun z := ⟨σ z.re, σ z.im⟩
  invFun z := ⟨σ.symm z.re, σ.symm z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp [ha]
  map_add' z w := by ext <;> simp

@[simp] theorem quadraticLift_cast (σ : K ≃+* K) (ha : σ a = a) (x : K) :
    quadraticLift a σ ha (algebraMap K _ x) = algebraMap K _ (σ x) := by
  ext <;> simp [quadraticLift]

@[simp] theorem quadraticLift_omega (σ : K ≃+* K) (ha : σ a = a) :
    quadraticLift a σ ha (QuadraticAlgebra.omega : QuadraticAlgebra K a 0) =
      QuadraticAlgebra.omega := by
  ext <;> simp [quadraticLift, QuadraticAlgebra.omega]

def quadraticEval {L : Type u} [Field L] (f : K →+* L)
    (r : L) (hr : r ^ 2 = f a) : QuadraticAlgebra K a 0 →+* L where
  toFun z := f z.re + f z.im * r
  map_zero' := by simp
  map_one' := by change f 1 + f 0 * r = 1; simp
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      map_add, map_mul, zero_mul, add_zero]
    rw [← hr]
    ring

omit [CharZero K] in
@[simp] theorem quadraticEval_cast {L : Type u} [Field L] (f : K →+* L)
    (r : L) (hr : r ^ 2 = f a) (x : K) :
    quadraticEval a f r hr (algebraMap K _ x) = f x := by
  simp [quadraticEval]

omit [CharZero K] in
@[simp] theorem quadraticEval_omega {L : Type u} [Field L] (f : K →+* L)
    (r : L) (hr : r ^ 2 = f a) :
    quadraticEval a f r hr QuadraticAlgebra.omega = r := by
  simp [quadraticEval, QuadraticAlgebra.omega]

end Quadratic

structure RadicalModel {K : Type u} [Field K] (ds : List K) where
  Carrier : Type u
  field : Field Carrier
  charZero : CharZero Carrier
  incl : K →+* Carrier
  roots : Fin ds.length → Carrier
  roots_sq : ∀ i, roots i ^ 2 = incl (ds.get i)
  flips : Fin ds.length → (Carrier ≃+* Carrier)
  flips_base : ∀ i x, flips i (incl x) = incl x
  flips_roots : ∀ i j, flips i (roots j) = if i = j then -roots j else roots j
  square_descends : ∀ b : K, (∃ z : Carrier, z ^ 2 = incl b) ↔
    ∃ s : List K, s.Sublist ds ∧ ∃ c : K, b = c ^ 2 * s.prod
  evaluate : ∀ (L : Type u) [Field L] (f : K →+* L) (r : Fin ds.length → L),
    (∀ i, r i ^ 2 = f (ds.get i)) →
    ∃ φ : Carrier →+* L, (∀ x, φ (incl x) = f x) ∧ ∀ i, φ (roots i) = r i

attribute [instance] RadicalModel.field RadicalModel.charZero

section Construction

variable {K : Type u} [Field K] [CharZero K]

private def emptyModel : RadicalModel ([] : List K) where
  Carrier := K
  field := inferInstance
  charZero := inferInstance
  incl := RingHom.id K
  roots := Fin.elim0
  roots_sq := fun i => Fin.elim0 i
  flips := Fin.elim0
  flips_base := fun i => Fin.elim0 i
  flips_roots := fun i => Fin.elim0 i
  square_descends b := by
    simp only [RingHom.id_apply, List.sublist_nil]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨[], rfl, c, by simpa using hc.symm⟩
    · rintro ⟨s, rfl, c, hc⟩
      exact ⟨c, by simpa using hc.symm⟩
  evaluate L _ f r _ := ⟨f, fun _ => rfl, fun i => Fin.elim0 i⟩

omit [CharZero K] in
private theorem tail_independent {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) : SquareIndependent ds := by
  intro s hs hn c
  exact h s (hs.cons a) hn c

omit [CharZero K] in
private theorem head_not_square {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) (m : RadicalModel ds) :
    ∀ z : m.Carrier, z ^ 2 ≠ m.incl a := by
  intro z hz
  obtain ⟨s, hs, c, hc⟩ := (m.square_descends a).mp ⟨z, hz⟩
  apply h (a :: s) (hs.cons_cons a) (List.cons_ne_nil _ _) (c * s.prod)
  simp only [List.prod_cons, hc]
  ring

omit [CharZero K] in
private theorem head_ne_zero {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) : a ≠ 0 := by
  intro ha
  apply h [a] (List.nil_sublist ds |>.cons_cons a) (List.cons_ne_nil _ _) 0
  simp [ha]

omit [CharZero K] in
private theorem extend_square_descends {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) (m : RadicalModel ds) (b : K) :
    (∃ z : QuadraticAlgebra m.Carrier (m.incl a) 0,
      z ^ 2 = algebraMap m.Carrier _ (m.incl b)) ↔
    ∃ s : List K, s.Sublist (a :: ds) ∧ ∃ c : K, b = c ^ 2 * s.prod := by
  rw [square_in_quadratic_iff]
  have ha := head_ne_zero h
  have hma : m.incl a ≠ 0 := (map_ne_zero m.incl).mpr ha
  constructor
  · rintro (hb | ⟨y, hy⟩)
    · obtain ⟨s, hs, c, hc⟩ := (m.square_descends b).mp hb
      exact ⟨s, hs.cons a, c, hc⟩
    · have hy' : y ^ 2 = m.incl (b / a) := by
        rw [map_div₀, eq_div_iff hma, mul_comm]
        exact hy
      obtain ⟨s, hs, c, hc⟩ := (m.square_descends (b / a)).mp ⟨y, hy'⟩
      refine ⟨a :: s, hs.cons_cons a, c, ?_⟩
      calc
        b = (b / a) * a := (div_mul_cancel₀ b ha).symm
        _ = c ^ 2 * (a :: s).prod := by rw [hc, List.prod_cons]; ring
  · rintro ⟨s, hs, c, hc⟩
    rcases List.sublist_cons_iff.mp hs with hs | ⟨r, rfl, hr⟩
    · exact Or.inl ((m.square_descends b).mpr ⟨s, hs, c, hc⟩)
    · obtain ⟨y, hy⟩ := (m.square_descends (c ^ 2 * r.prod)).mpr ⟨r, hr, c, rfl⟩
      refine Or.inr ⟨y, ?_⟩
      rw [hy, ← map_mul]
      congr 1
      rw [hc, List.prod_cons]
      ring

private def extendModel {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) (m : RadicalModel ds) :
    RadicalModel (a :: ds) := by
  letI : Fact (∀ z : m.Carrier, z ^ 2 ≠ m.incl a + 0 * z) :=
    ⟨by simpa using head_not_square h m⟩
  let E := QuadraticAlgebra m.Carrier (m.incl a) 0
  let cast : m.Carrier →+* E := algebraMap m.Carrier E
  refine
    { Carrier := E
      field := inferInstance
      charZero := inferInstance
      incl := cast.comp m.incl
      roots := Fin.cases QuadraticAlgebra.omega (fun i => cast (m.roots i))
      roots_sq := ?_
      flips := Fin.cases (quadraticFlip (m.incl a))
        (fun i => quadraticLift (m.incl a) (m.flips i) (m.flips_base i a))
      flips_base := ?_
      flips_roots := ?_
      square_descends := extend_square_descends h m
      evaluate := ?_ }
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [cast, E, pow_two, QuadraticAlgebra.omega_mul_omega_eq_add, Algebra.smul_def]
    · change cast (m.roots i) ^ 2 = cast (m.incl (ds.get i))
      simpa only [map_pow] using congrArg cast (m.roots_sq i)
  · intro i x
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [cast, E]
    · simp [cast, E, m.flips_base]
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [cast, E, Fin.succ_ne_zero, eq_comm]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [cast, E, Fin.succ_ne_zero]
      · by_cases hij : i = j <;> simp [cast, E, m.flips_roots, hij]
  · intro L _ f r hr
    obtain ⟨φ, hφbase, hφroot⟩ := m.evaluate L f (fun i => r i.succ)
      (fun i => hr i.succ)
    have hr0 : r 0 ^ 2 = φ (m.incl a) := by
      rw [hφbase]
      exact hr 0
    refine ⟨quadraticEval (m.incl a) φ (r 0) hr0, ?_, ?_⟩
    · intro x
      simpa [cast, E] using hφbase x
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [E]
      · simpa [cast, E] using hφroot i

theorem exists_radicalModel (ds : List K) (h : SquareIndependent ds) :
    Nonempty (RadicalModel ds) := by
  induction ds with
  | nil => exact ⟨emptyModel⟩
  | cons a ds ih =>
    obtain ⟨m⟩ := ih (tail_independent h)
    exact ⟨extendModel h m⟩

end Construction

section Consequences

variable {K : Type u} [Field K] [CharZero K] {ds : List K}

omit [CharZero K] in

theorem SquareIndependent.get_ne_zero (h : SquareIndependent ds) (i : Fin ds.length) :
    ds.get i ≠ 0 := by
  intro hi
  apply h [ds.get i] (List.singleton_sublist.mpr (ds.get_mem i))
    (List.cons_ne_nil _ _) 0
  rw [List.prod_cons, List.prod_nil, mul_one, hi]
  norm_num

omit [CharZero K] in
theorem RadicalModel.root_ne_zero (m : RadicalModel ds) (h : SquareIndependent ds)
    (i : Fin ds.length) : m.roots i ≠ 0 := by
  intro hi
  have hs := m.roots_sq i
  rw [hi, zero_pow (by decide : 2 ≠ 0)] at hs
  exact h.get_ne_zero i (m.incl.injective (by simpa using hs.symm))

omit [CharZero K] in

theorem RadicalModel.linear_relation (m : RadicalModel ds) (h : SquareIndependent ds)
    (c : Fin ds.length → K)
    (hc : ∑ i, m.incl (c i) * m.roots i = 0) : ∀ i, c i = 0 := by
  intro i
  have hdiff :
      (∑ j, (m.incl (c j) * m.roots j -
        m.flips i (m.incl (c j) * m.roots j))) =
      2 * (m.incl (c i) * m.roots i) := by
    calc
      _ = ∑ j : Fin ds.length,
          if i = j then 2 * (m.incl (c i) * m.roots i) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j
          simp [m.flips_base, m.flips_roots]
          ring
        · simp [map_mul, m.flips_base, m.flips_roots, hij]
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, ← map_sum, hc, map_zero, sub_self] at hdiff
  have hz : m.incl (c i) * m.roots i = 0 :=
    (mul_eq_zero.mp hdiff.symm).resolve_left (by norm_num)
  have hz' : m.incl (c i) = 0 := (mul_eq_zero.mp hz).resolve_right (m.root_ne_zero h i)
  exact m.incl.injective (by simpa using hz')


end Consequences

section LinearSystem

variable {E L : Type u} [Field E] [Field L]
variable {n : Type v} [Fintype n] [DecidableEq n]

theorem solution_lift_fixed (f : E →+* L) (M : Matrix n n E) (b : n → E)
    (hdet : M.det ≠ 0) (σ : E ≃+* E)
    (hM : ∀ i j, σ (M i j) = M i j) (hb : ∀ i, σ (b i) = b i)
    (x : n → L) (hx : (M.map f).mulVec x = fun i => f (b i)) :
    ∃ y : n → E, (∀ i, f (y i) = x i) ∧ (∀ i, σ (y i) = y i) := by
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, hy⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) b
  have hunit' : IsUnit (M.map f) := by
    apply (Matrix.isUnit_iff_isUnit_det (M.map f)).mpr
    change IsUnit (f.mapMatrix M).det
    rw [← f.map_det]
    exact (isUnit_iff_ne_zero.mpr hdet).map f
  have hymap : (M.map f).mulVec (fun i => f (y i)) = fun i => f (b i) := by
    ext i
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
      using congrArg f (congrFun hy i)
  have hyx : (fun i => f (y i)) = x :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit') (hymap.trans hx.symm)
  have hyσ : M.mulVec (fun i => σ (y i)) = b := by
    ext i
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, hM, hb]
      using congrArg σ (congrFun hy i)
  have hfix : (fun i => σ (y i)) = y :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hyσ.trans hy.symm)
  exact ⟨y, fun i => congrFun hyx i, fun i => congrFun hfix i⟩

theorem unused_sign_equation [CharZero E] (σ : E ≃+* E)
    {B A c t r : E} (hr : r ≠ 0) (hB : σ B = B) (hA : σ A = A)
    (hc : σ c = c) (ht : σ t = t) (hflip : σ r = -r)
    (heq : B - r * A = c - r * t) : A = t := by
  have heq' := congrArg σ heq
  simp only [map_sub, map_mul, hB, hA, hc, ht, hflip] at heq'
  have hz : r * (A - t) = 0 := by linear_combination (heq' - heq) / 2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hr)

end LinearSystem

section PlanarSystem

variable {K L : Type u} [Field K] [CharZero K] [Field L]

theorem planar_radical_forces_scalar (f : K →+* L)
    (d a b c t : Fin 4 → K)
    (hind : SquareIndependent [d 0, d 1, d 2, d 3])
    (r : Fin 4 → L) (hr : ∀ i, r i ^ 2 = f (d i))
    (hrank : a 0 * b 1 - b 0 * a 1 ≠ 0 ∨
      a 0 * b 2 - b 0 * a 2 ≠ 0 ∨ a 1 * b 2 - b 1 * a 2 ≠ 0)
    (x y A : L)
    (heq : ∀ i, f (a i) * x + f (b i) * y - r i * A =
      f (c i) - r i * f (t i)) : A = f (t 3) := by
  obtain ⟨m⟩ := exists_radicalModel _ hind
  obtain ⟨φ, hφbase, hφroot⟩ := m.evaluate L f r (by
    intro i; fin_cases i <;> simpa using hr _)
  let M : Matrix (Fin 3) (Fin 3) m.Carrier :=
    !![m.incl (a 0), m.incl (b 0), -m.roots 0;
       m.incl (a 1), m.incl (b 1), -m.roots 1;
       m.incl (a 2), m.incl (b 2), -m.roots 2]
  let rhs : Fin 3 → m.Carrier :=
    ![m.incl (c 0) - m.roots 0 * m.incl (t 0),
      m.incl (c 1) - m.roots 1 * m.incl (t 1),
      m.incl (c 2) - m.roots 2 * m.incl (t 2)]
  have hdet : M.det ≠ 0 := by
    intro hz
    let coeff : Fin 4 → K :=
      ![a 2 * b 1 - a 1 * b 2, a 0 * b 2 - a 2 * b 0,
        a 1 * b 0 - a 0 * b 1, 0]
    have hrel : ∑ i, m.incl (coeff i) * m.roots i = 0 := by
      have hexp := (Matrix.det_fin_three M).symm.trans hz
      simp [M] at hexp
      simp [Fin.sum_univ_succ, coeff]
      linear_combination hexp
    have hc := m.linear_relation hind coeff hrel
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    simp [coeff] at h0 h1 h2
    rcases hrank with hh | hh | hh
    · apply hh; linear_combination -h2
    · apply hh; linear_combination h1
    · apply hh; linear_combination -h0
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  have hMf : ∀ i j, m.flips 3 (M i j) = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, m.flips_base, m.flips_roots, h30, h31, h32]
  have hbf : ∀ i, m.flips 3 (rhs i) = rhs i := by
    intro i; fin_cases i <;> simp [rhs, m.flips_base, m.flips_roots, h30, h31, h32]
  have hsol : (M.map φ).mulVec ![x, y, A] = fun i => φ (rhs i) := by
    ext i
    fin_cases i <;>
      simp [M, rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hφbase, hφroot] <;>
      first | linear_combination heq 0 | linear_combination heq 1 | linear_combination heq 2
  obtain ⟨v, hv, hfix⟩ := solution_lift_fixed φ M rhs hdet (m.flips 3) hMf hbf
    ![x, y, A] hsol
  have hlast : m.incl (a 3) * v 0 + m.incl (b 3) * v 1 - m.roots 3 * v 2 =
      m.incl (c 3) - m.roots 3 * m.incl (t 3) := by
    apply φ.injective
    simpa [hφbase, hφroot, hv] using heq 3
  have hv2 : v 2 = m.incl (t 3) := unused_sign_equation (m.flips 3)
    (m.root_ne_zero hind 3)
    (by simp [hfix, m.flips_base]) (hfix 2) (m.flips_base 3 (c 3))
    (m.flips_base 3 (t 3)) (by simp [m.flips_roots]) hlast
  have hh := congrArg φ hv2
  simpa [hv, hφbase] using hh

theorem line_radical_forces_scalar (f : K →+* L)
    (d a c t : Fin 3 → K)
    (hind : SquareIndependent [d 0, d 1, d 2])
    (r : Fin 3 → L) (hr : ∀ i, r i ^ 2 = f (d i))
    (ha : a 0 ≠ 0) (h A : L)
    (heq : ∀ i, f (a i) * h - r i * A = f (c i) - r i * f (t i)) :
    A = f (t 2) := by
  obtain ⟨m⟩ := exists_radicalModel _ hind
  obtain ⟨φ, hφbase, hφroot⟩ := m.evaluate L f r (by
    intro i; fin_cases i <;> simpa using hr _)
  let M : Matrix (Fin 2) (Fin 2) m.Carrier :=
    !![m.incl (a 0), -m.roots 0; m.incl (a 1), -m.roots 1]
  let rhs : Fin 2 → m.Carrier :=
    ![m.incl (c 0) - m.roots 0 * m.incl (t 0),
      m.incl (c 1) - m.roots 1 * m.incl (t 1)]
  have hdet : M.det ≠ 0 := by
    intro hz
    let coeff : Fin 3 → K := ![a 1, -a 0, 0]
    have hrel : ∑ i, m.incl (coeff i) * m.roots i = 0 := by
      have hexp := (Matrix.det_fin_two M).symm.trans hz
      simp [M] at hexp
      simp [Fin.sum_univ_succ, coeff]
      linear_combination hexp
    have hc := m.linear_relation hind coeff hrel 1
    apply ha
    simpa [coeff] using hc
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hMf : ∀ i j, m.flips 2 (M i j) = M i j := by
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [M, m.flips_base, m.flips_roots, h20, h21]
  have hbf : ∀ i, m.flips 2 (rhs i) = rhs i := by
    intro i; fin_cases i <;> simp [rhs, m.flips_base, m.flips_roots, h20, h21]
  have hsol : (M.map φ).mulVec ![h, A] = fun i => φ (rhs i) := by
    ext i
    fin_cases i <;>
      simp [M, rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hφbase, hφroot] <;>
      first | linear_combination heq 0 | linear_combination heq 1
  obtain ⟨v, hv, hfix⟩ := solution_lift_fixed φ M rhs hdet (m.flips 2) hMf hbf
    ![h, A] hsol
  have hlast : m.incl (a 2) * v 0 - m.roots 2 * v 1 =
      m.incl (c 2) - m.roots 2 * m.incl (t 2) := by
    apply φ.injective
    simpa [hφbase, hφroot, hv] using heq 2
  have hv1 : v 1 = m.incl (t 2) := unused_sign_equation (m.flips 2)
    (m.root_ne_zero hind 2)
    (by simp [hfix, m.flips_base]) (hfix 1) (m.flips_base 2 (c 2))
    (m.flips_base 2 (t 2)) (by simp [m.flips_roots]) hlast
  have hh := congrArg φ hv1
  simpa [hv, hφbase] using hh

end PlanarSystem

end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
universe u
variable {K L : Type u} [Field K] [CharZero K] [Field L]

theorem radical_system_impossible (f : K →+* L)
    (d a b c t : Fin 4 → K)
    (hind : SquareIndependent [d 0,d 1,d 2,d 3])
    (r : Fin 4 → L) (hr : ∀ i, r i ^ 2 = f (d i))
    (ha : a 0 ≠ 0) (x y A : L)
    (heq : ∀ i, f (a i)*x+f (b i)*y-r i*A = f (c i)-r i*f (t i))
    (hne : ∀ i, A ≠ f (t i)) : False := by
  classical
  by_cases h : a 0*b 1-b 0*a 1 ≠ 0 ∨ a 0*b 2-b 0*a 2 ≠ 0 ∨ a 1*b 2-b 1*a 2 ≠ 0
  · exact hne 3 (planar_radical_forces_scalar f d a b c t hind r hr h x y A heq)
  · push Not at h
    let ι : Fin 3 → Fin 4 := fun i => i.castSucc
    have hsub : SquareIndependent [d (ι 0),d (ι 1),d (ι 2)] := by
      intro s hs hs0 u
      apply hind s (hs.trans ?_) hs0 u
      exact List.sublist_append_left [d 0,d 1,d 2] [d 3]
    have hprop (i : Fin 3) : a (ι i)*b 0=a 0*b (ι i) := by
      fin_cases i
      · rfl
      · dsimp [ι]; linear_combination -h.1
      · dsimp [ι]; linear_combination -h.2.1
    have hfa : f (a 0) ≠ 0 := by simpa only [map_zero] using f.injective.ne ha
    have hcoef (i : Fin 3) : f (a (ι i))*(f (b 0)/f (a 0))=f (b (ι i)) := by
      rw [← mul_div_assoc, div_eq_iff hfa]
      have hh := congrArg f (hprop i)
      simpa only [map_mul, mul_comm (f (a 0))] using hh
    have heq' (i : Fin 3) : f (a (ι i))*(x+(f (b 0)/f (a 0))*y)-r (ι i)*A =
        f (c (ι i))-r (ι i)*f (t (ι i)) := by
      rw [mul_add, ← mul_assoc, hcoef]
      exact heq (ι i)
    have hh := line_radical_forces_scalar f (d ∘ ι) (a ∘ ι) (c ∘ ι) (t ∘ ι)
      hsub (r ∘ ι) (fun i => hr (ι i)) ha (x+(f (b 0)/f (a 0))*y) A heq'
    exact hne 2 hh
end PlanarUnitDistances.Radicals

namespace UnitDistances.DifferentialSystem

variable {k F : Type*} [Field k] [Field F] [Algebra k F]


end UnitDistances.DifferentialSystem

namespace UnitDistances.DifferentialSystem
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

end UnitDistances.DifferentialSystem

namespace PlanarUnitDistances.Radicals
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L] [Algebra k L]

end PlanarUnitDistances.Radicals

end OAI
