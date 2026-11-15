import PlanarUnitDistances.PrivateValuations
import PlanarUnitDistances.AnchorFallback

namespace PlanarUnitDistances.AnchorGenericPlane
open MvPolynomial OAI.PlanarUnitDistances.Radicals
noncomputable section

variable {k : Type*} [Field k] [CharZero k]
abbrev Pol (k : Type*) [Field k] := MvPolynomial (Fin 2) k
abbrev Frac2 (k : Type*) [Field k] := RatFunc (RatFunc k)

def base : k →+* Frac2 k := RatFunc.C.comp RatFunc.C
def z : Frac2 k := RatFunc.C RatFunc.X
def w : Frac2 k := RatFunc.X
def splitMap : Pol k →+* Frac2 k := eval₂Hom base ![z,w]

omit [CharZero k] in
/-- No polynomial equation between the two generic null coordinates. -/
theorem splitMap_injective : Function.Injective (splitMap (k:=k)) := by
  let F := FractionRing (Pol k)
  let f : Pol k →ₐ[k] F := IsScalarTower.toAlgHom k (Pol k) F
  have inj : Function.Injective f := IsFractionRing.injective (Pol k) F
  have independent := (MvPolynomial.algebraicIndependent_X (Fin 2) k).map' inj
  obtain ⟨ψ,hw,hz,hc⟩ := OAI.PlanarUnitDistances.GenericPlane.exists_plane_embedding _ independent
  have id : ψ.comp splitMap = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro b; change ψ (splitMap (C b))=f (C b)
      rw [splitMap,eval₂Hom_C]
      exact (hc b).trans (f.commutes b).symm
    · intro i
      simp only [RingHom.comp_apply,splitMap,eval₂Hom_X']
      fin_cases i
      · exact hz
      · exact hw
  intro p q h
  apply inj
  exact (DFunLike.congr_fun id p).symm.trans ((congrArg ψ h).trans (DFunLike.congr_fun id q))

/-- Substituting Cartesian coordinates in terms of null coordinates.
Division is by the two nonzero constants 2 and 2i only. -/
def toNull (I : k) : Pol k →+* Pol k :=
  eval₂Hom C ![C (2:k)⁻¹*(X 0+X 1),C (2*I)⁻¹*(X 0-X 1)]

def toCartesian (I : k) : Pol k →+* Pol k :=
  eval₂Hom C ![X 0+C I*X 1,X 0-C I*X 1]

theorem toNull_injective {I : k} (hI : I^2= -1) : Function.Injective (toNull I) := by
  have hn : I≠0 := by rintro rfl; simp at hI
  have hinv (a : k) (ha : a≠0) : (C a:Pol k)*C a⁻¹=1 := by rw [←map_mul,mul_inv_cancel₀ ha,map_one]
  have comp : (toCartesian I).comp (toNull I)=RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro b; simp [toCartesian,toNull]
    · intro i; fin_cases i
      · change toCartesian I (toNull I (X 0))=X 0
        simp [toCartesian,toNull]
        have h := hinv 2 two_ne_zero
        rw [map_ofNat] at h
        linear_combination (X 0)*h
      · change toCartesian I (toNull I (X 1))=X 1
        simp [toCartesian,toNull]
        have h := hinv (2*I) (mul_ne_zero two_ne_zero hn)
        simp only [mul_inv_rev,map_mul,map_ofNat] at h
        linear_combination (X 1)*h
  intro p q h
  exact (DFunLike.congr_fun comp p).symm.trans ((congrArg (toCartesian I) h).trans (DFunLike.congr_fun comp q))

def Dx (I : k) := (splitMap (k:=k)).comp (toNull I)

def distanceSq (r s : k) : Pol k := (X 0-C r)^2+(X 1-C s)^2
def radicand (r s : k) : Pol k := distanceSq r s*(distanceSq r s-4)

/-- Pullback of the actual Cartesian distance to the split generic field, with
the same anchor parameters on both sides. -/
theorem distance_generic {I : k} (hi : I^2= -1) (r s : k) :
    Dx I (distanceSq r s) =
      (z-base (r+I*s)) * (w-base (r-I*s)) := by
  have hn : I≠0 := by rintro rfl; simp at hi
  have nn : base I≠0 := by simpa using (base.injective.ne hn)
  have zi : (C I : Pol k)^2 = -1 := by rw [←map_pow,hi,map_neg,map_one]
  have fac : distanceSq r s = ((X 0+C I*X 1)-C (r+I*s))*((X 0-C I*X 1)-C (r-I*s)) := by
    simp only [distanceSq,map_add,map_sub,map_mul]
    linear_combination (X 1-C s)^2*zi
  have phC (c : k) : Dx I (C c) = base c := by simp [Dx,splitMap,toNull]
  have x : Dx I (X 0) = (2:Frac2 k)⁻¹*(z+w) := by
    simp [Dx,splitMap,toNull,map_ofNat]
  have y : Dx I (X 1) = (2*base I)⁻¹*(z-w) := by
    simp [Dx,splitMap,toNull,map_ofNat]
  rw [fac,map_mul,map_sub,map_sub,map_add,map_sub,map_mul,x,y,phC,phC,phC]
  field_simp [nn]
  ring
/-- Generic field containing the correct independent four Cartesian radicands.
The underlying polynomial map is injective, so coefficient descent is valid. -/
theorem plane_model {I : k} (hI : I^2= -1) (r s : Fin 4 → k)
    (distinct : Function.Injective (fun i => (r i,s i))) :
    Function.Injective (Dx I) ∧
    SquareIndependent [Dx I (radicand (r 0) (s 0)),Dx I (radicand (r 1) (s 1)),
      Dx I (radicand (r 2) (s 2)),Dx I (radicand (r 3) (s 3))] := by
  refine ⟨splitMap_injective.comp (toNull_injective hI),?_⟩
  let a (j : Fin 4) := r j+I*s j
  let b (j : Fin 4) := r j-I*s j
  have hn : I≠0 := by rintro rfl; simp at hI
  have hab : Function.Injective (fun j => (a j,b j)) := by
    intro j l he
    have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    change r j+I*s j = r l+I*s l at h1
    change r j-I*s j = r l-I*s l at h2
    apply distinct
    apply Prod.ext
    · linear_combination (h1+h2)/2
    · apply mul_left_cancel₀ hn
      linear_combination (h1-h2)/2
  have hind := plane_radicands_squareIndependent (List.ofFn (fun j => (a j,b j))) (List.nodup_ofFn.mpr hab)
  have form : SquareIndependent (List.ofFn (fun j : Fin 4 =>
      (z-base (a j))*(w-base (b j))*((z-base (a j))*(w-base (b j))-4))) := by
    simpa only [List.map_ofFn,planeRadicandPoly,planeDistancePoly,map_mul,map_sub,map_ofNat,
      RatFunc.algebraMap_C,RatFunc.algebraMap_X,Function.comp_def,base,z,w,RingHom.comp_apply] using hind
  simp only [radicand,map_mul,map_sub,map_ofNat,distance_generic hI]
  let v (j : Fin 4) := (z-base (a j))*(w-base (b j))*((z-base (a j))*(w-base (b j))-4)
  have ls (F : Fin 4 → Frac2 k) : List.ofFn F = [F 0, F 1, F 2, F 3] := by
    simp [List.ofFn_succ]
  change SquareIndependent (List.ofFn v) at form
  rw [ls] at form
  simpa only [v,a,b,map_sub,map_mul] using form

end
end PlanarUnitDistances.AnchorGenericPlane

namespace PlanarUnitDistances.AnchorGenericPlane
open MvPolynomial Matrix AnchorFallback OAI.PlanarUnitDistances.Radicals
noncomputable section

universe v
variable {k : Type v} [Field k] [CharZero k]

omit [CharZero k] in
theorem radicand_degree (r s : k) : (radicand r s).totalDegree ≤ 4 := by
  have linear (i : Fin 2) (a : k) : (X i-C a : Pol k).totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    rw [totalDegree_X,totalDegree_C]; decide
  have d : (distanceSq r s).totalDegree ≤ 2 := by
    unfold distanceSq
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_pow _ _).trans (by have := linear 0 r; omega)
    · exact (totalDegree_pow _ _).trans (by have := linear 1 s; omega)
  have four : (4:Pol k).totalDegree=0 := by
    rw [show (4:Pol k)=C (4:k) from (map_ofNat C 4).symm,totalDegree_C]
  unfold radicand
  apply (totalDegree_mul _ _).trans
  have t := totalDegree_sub (distanceSq r s) (4:Pol k)
  omega

def positionRhs (r s U T : Fin 4 → k) (j : Fin 4) : Pol k :=
  pos 0 (r j)*C (U j)+pos 1 (s j)*C (T j)

abbrev GenericRoots (I : k) (r s : Fin 4 → k) :=
  Model (fun j => Dx I (radicand (r j) (s j)))

def genericAug (I : k) (r s U T a : Fin 4 → k) (m : GenericRoots I r s) :
    Matrix (Fin 4) (Fin 4) m.Carrier :=
  let f := m.incl.comp (Dx I)
  aug (fun j => f (pos 0 (r j))) (fun j => f (pos 1 (s j)))
    (f ∘ positionRhs r s U T) (fun j => f (C (a j))) m.roots

theorem exists_generic_roots {I : k} (hI : I^2= -1) (r s : Fin 4 → k)
    (hd : Function.Injective (fun i => (r i,s i))) : Nonempty (GenericRoots I r s) :=
  exists_radicalModel _ (plane_model hI r s hd).2

omit [CharZero k] in
/-- Any choice of generic roots with zero determinant forces the corresponding
canonical model determinant to vanish, by its evaluation embedding. -/
theorem genericAug_zero_from_chosen_roots {I : k} (r s U T a : Fin 4 → k)
    (m : GenericRoots I r s) {E : Type v} [Field E] (φ : Frac2 k →+* E)
    (u : Fin 4 → E) (sq : ∀ j,u j^2=φ (Dx I (radicand (r j) (s j))))
    (zero : (aug ((φ.comp (Dx I)) ∘ (fun j => pos 0 (r j)))
      ((φ.comp (Dx I)) ∘ (fun j => pos 1 (s j))) ((φ.comp (Dx I)) ∘ positionRhs r s U T)
      (fun j => φ (Dx I (C (a j)))) u).det=0) : (genericAug I r s U T a m).det=0 := by
  obtain ⟨e,coeff,root⟩ := m.evaluate E φ u (by intro j; fin_cases j <;> exact sq _)
  apply e.injective
  rw [e.map_det,map_zero]
  apply Eq.trans _ zero
  apply congrArg Matrix.det
  ext i j
  fin_cases j <;> simp [genericAug,aug,coeff,root]
/-- The concrete exceptional branch of the four-anchor theorem. In Cartesian
coordinates the eliminant has total degree at most twelve and tests every
solution over every extension of k. -/
theorem cartesian_fallback {I : k} (hI : I^2= -1) (r s U T a : Fin 4 → k)
    (hd : Function.Injective (fun i => (r i,s i))) (m : GenericRoots I r s)
    (zero : (genericAug I r s U T a m).det=0) :
    ∃ F : Pol k,F≠0 ∧ F.totalDegree ≤ 12 ∧
      ∀ (L : Type*) [Field L] (f : k →+* L) (p q h k' A : L) (u : Fin 4 → L),
        (∀ j,let n := (p-f (r j))^2+(q-f (s j))^2; u j^2=n*(n-4)) →
        (∀ j,2*((p-f (r j))*(h-f (U j))+(q-f (s j))*(k'-f (T j)))=u j*(A-f (a j))) →
        A≠f (a 3) → eval₂Hom f ![p,q] F=0 := by
  have ⟨inj,indep⟩ := plane_model hI r s hd
  have proof := degree_twelve_branch r s (hd.ne (by decide : (0:Fin 4)≠1))
    (positionRhs r s U T) (fun j => C (a j)) (fun j => radicand (r j) (s j))
    (fun j => radicand_degree _ _) (Dx I) inj m indep zero
  refine ⟨_,proof.1,proof.2.1,?_⟩
  intro L _ f p q h k' A u hs eqs hn
  apply proof.2.2 L (eval₂Hom f ![p,q]) u h k' A
  · intro j
    simpa [radicand,distanceSq,map_ofNat] using hs j
  · intro j
    simp [pos,positionRhs]
    linear_combination eqs j
  · simpa using hn

end
end PlanarUnitDistances.AnchorGenericPlane
