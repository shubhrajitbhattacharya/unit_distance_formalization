import PlanarUnitDistances.SelectedCriticalLocus
import PlanarUnitDistances.Heights
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import PlanarUnitDistances.StationaryComponent
import PlanarUnitDistances.TorusCritical
import PlanarUnitDistances.LogHeight
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Base change of the torus multiplier equations and the stationary-coordinate
height property used in the elimination argument. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open MvPolynomial CriticalLocus Real

variable {K L I J : Type*} [Field K] [Field L] [Fintype I] [Fintype J]

def mapUnits (φ : K →+* L) (a : I → Option J → Kˣ) (i : I) (j : Option J) : Lˣ :=
  Units.map φ.toMonoidHom (a i j)


variable [NumberField K] [Algebra K L]


def StationaryRatioWithCap (K L I J : Type*) [Field K] [NumberField K] [Field L]
    [Algebra K L] [Fintype I] [Fintype J] (r : ℕ)
    (cap : ℝ → ℝ) : Prop :=
  ∀ (a : I → Option J → Kˣ) (i : I) (j : Option J),
    (∀ t, a i t = 1) → (∀ k, a k none = 1) →
    2 ≤ Fintype.card I → Fintype.card I ≤ 3 * Fintype.card (Option J) - 3 →
    2 ≤ Fintype.card (Option J) → Fintype.card (Option J) ≤ 4 → r ≤ 47 →
    ∀ (pick : Fin r → Equation I J) (c : K)
      (P : Ideal (MvPolynomial (Variables (Coord I J) (Fin r)) L)),
      P ∈ (incidenceIdeal (ratio (mapUnits (algebraMap K L) a) i j)
        (equation (mapUnits (algebraMap K L) a)) pick).minimalPrimes →
      outputVariable - C (algebraMap K L c) ∈ P →
      Fintype.card (Variables (Coord I J) (Fin r)) ≤ 98 →
      weilHeight c ≤ cap (∑ z : I×Option J, weilHeight (a z.1 z.2 : K))


omit [Algebra K L] in
theorem sum_normalized_coefficients (a : I → Option J → Kˣ) (b : I)
    (hrow : ∀ j, a b j = 1) (hcol : ∀ i, a i none = 1) {u : ℝ}
    (hu : ∀ i j, weilHeight (a i (some j) : K) ≤ u) :
    (∑ z : I × Option J, weilHeight (a z.1 z.2 : K)) ≤
      (((Fintype.card I-1)*Fintype.card J : ℕ):ℝ)*u := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_option]
  simp only [hcol,Units.val_one,weilHeight_one,zero_add]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
  simp only [hrow,Units.val_one,weilHeight_one,Finset.sum_const_zero,add_zero]
  calc
    _ ≤ ∑ _i ∈ (Finset.univ : Finset I).erase b, ∑ _j : J, u :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hu i j
    _ = _ := by simp [Finset.card_erase_of_mem,mul_assoc]


/-- A stationary coordinate of the original torus has small height on the
actual small grid from its normalized stationary-coordinate estimate.
The quotient hypotheses are evaluated in K. Geometric stationarity is tested
over its algebraic closure, which can also contain the lifted multipliers. -/
theorem stationary_original_ratio_with_cap [Nontrivial I] [CharZero L] [IsAlgClosed L]
    (cap : ℝ → ℝ) (hcap : Monotone cap)
    (source : ∀ (S : Finset I) (r : ℕ), StationaryRatioWithCap K L S J r cap)
    (a : I → Option J → Kˣ) (ha : ∀ i, a i none = 1) (p : I → L × L) (s : Option J → L × L)
    (i₀ : I) (sol : Fibre.TorusSolution i₀ none p s (mapUnits (algebraMap K L) a))
    (hl : Fintype.card (Option J) ≤ 4) (i : I) (j j₁ j₂ : Option J) (hj : s j₁ ≠ s j₂)
    (c : K) (hc : chordRatio p s (mapUnits (algebraMap K L) a) i₀ sol i j = algebraMap K L c)
    {u : ℝ} (hu : 0 ≤ u) (hrect : ∀ k b t, weilHeight (↑(a k (some t) / a b (some t)) : K) ≤ u)
    (hs : ∀ v : Coord I J → L,
      (∀ e, jacobianRow (coordinates p s (mapUnits (algebraMap K L) a) i₀ sol)
        (equation (mapUnits (algebraMap K L) a) e) v = 0) →
      jacobianRow (coordinates p s (mapUnits (algebraMap K L) a) i₀ sol)
        (ratio (mapUnits (algebraMap K L) a) i j) v = 0) :
    weilHeight c ≤ cap (24*u) := by
  classical
  let α := mapUnits (algebraMap K L) a
  have hα (k : I) : α k none = 1 := by simp [α,mapUnits,ha]
  obtain ⟨S,hi,h₂,hmax,hn,hcomp⟩ :=
    sparse_stationary_component p s α i₀ sol hα hl i j j₁ j₂ hj hs
  let b : S := ⟨i,hi⟩
  let β := restrictedCoefficient a S b
  have hmap : restrictedCoefficient α S b = mapUnits (algebraMap K L) β := by
    funext k t
    simp [mapUnits,restrictedCoefficient,β,α]
  obtain ⟨r,pick,_t,hr,hq,P,hP,_hlift,hcoord,_hdeg⟩ := hcomp b
  rw [hmap] at hP
  rw [hc] at hcoord
  have hh := source S r β b j (fun t ↦ by simp [β,b,restrictedCoefficient])
    (fun k ↦ by simp [β,restrictedCoefficient,ha]) (by simpa using h₂) (by simpa using hmax)
    (Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨j₁,j₂,fun h ↦ hj (congrArg s h)⟩⟩) hl hr pick c P hP hcoord hq
  have hsum := sum_normalized_coefficients β b (fun t ↦ by simp [β,restrictedCoefficient])
    (fun k ↦ by simp [β,restrictedCoefficient,ha]) (fun k t ↦ hrect k b t)
  have hcount : (Fintype.card S-1)*Fintype.card J ≤ 24 := by simpa using hn
  have hcount' : (((Fintype.card S-1)*Fintype.card J : ℕ):ℝ) ≤ 24 := by exact_mod_cast hcount
  exact hh.trans (hcap (hsum.trans (mul_le_mul_of_nonneg_right hcount' hu)))


/-- Under the large individual-height and small rectangle-height hypotheses
one velocity in the original Jacobian kernel moves every edge simultaneously.
This includes grids with repeated positions and two distinct column positions. -/
theorem jacobian_motion_with_cap [Nontrivial I] [CharZero L] [IsAlgClosed L]
    (cap : ℝ → ℝ) (hcap : Monotone cap)
    (source : ∀ (S : Finset I) (r : ℕ), StationaryRatioWithCap K L S J r cap)
    (a : I → Option J → Kˣ) (ha : ∀ i, a i none = 1) (p : I → L × L) (s : Option J → L × L)
    (i₀ : I) (sol : Fibre.TorusSolution i₀ none p s (mapUnits (algebraMap K L) a))
    (hl : Fintype.card (Option J) ≤ 4) (j₁ j₂ : Option J) (hj : s j₁ ≠ s j₂)
    (c : I → Option J → K)
    (hc : ∀ i j, chordRatio p s (mapUnits (algebraMap K L) a) i₀ sol i j = algebraMap K L (c i j))
    (J₀ : ℝ) (hJ : 12*(2:ℝ)^111 ≤ J₀) (impossible : ∀ h : ℝ, J₀/3 ≤ h → h ≤ cap (24*(J₀/(324*2^111))) → False)
    (hlarge : ∀ i j, J₀/3 ≤ weilHeight (c i j))
    (hrect : ∀ k b t, weilHeight (↑(a k (some t) / a b (some t)) : K) ≤ J₀/(324*2^111)) :
    let α := mapUnits (algebraMap K L) a
    let x := coordinates p s α i₀ sol
    ∃ v : Coord I J → L, (∀ e, jacobianRow x (equation α e) v = 0) ∧
      ∀ i j, jacobianRow x (ratio α i j) v ≠ 0 := by
  let α := mapUnits (algebraMap K L) a
  let x := coordinates p s α i₀ sol
  let T := ⨅ e, (jacobianRow x (equation α e)).ker
  have hT (v : Coord I J → L) : v ∈ T ↔ ∀ e, jacobianRow x (equation α e) v = 0 := by
    simp only [T,Submodule.mem_iInf,LinearMap.mem_ker]
  cases simultaneous_motion_or_stationarity T (fun e : I × Option J ↦ jacobianRow x (ratio α e.1 e.2)) with
  | inl H =>
    obtain ⟨v,hv,he⟩ := H
    exact ⟨v,(hT _).mp hv,fun i j ↦ he (i,j)⟩
  | inr H =>
    obtain ⟨⟨i,j⟩,hij⟩ := H
    have hjpos : 0 ≤ J₀/(324*2^111) := by
      have hj₀ : 0 ≤ J₀ := (by positivity : (0:ℝ) ≤ 12*2^111).trans hJ
      positivity
    have hh := stationary_original_ratio_with_cap cap hcap source a ha p s i₀ sol hl i j j₁ j₂ hj
      (c i j) (hc i j) hjpos hrect (fun v hv ↦ hij v ((hT _).mpr hv))
    exact (impossible _ (hlarge i j) hh).elim


end PlanarUnitDistances.TorusCritical
