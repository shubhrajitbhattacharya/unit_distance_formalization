import PlanarUnitDistances.RadicalNorm

/-! Degree control for adjoining several formal square roots of polynomials
of degree at most four. Negative filtration levels control the zero polynomial. -/
namespace PlanarUnitDistances.RadicalNorm
open MvPolynomial
noncomputable section
universe u
structure Bounds (R : Type u) [CommRing R] where
  fits : ℤ → R → Prop
  mono : ∀ {m n x}, m ≤ n → fits m x → fits n x
  zero : ∀ n, fits n 0
  one : fits 0 1
  add : ∀ {n x y}, fits n x → fits n y → fits n (x+y)
  neg : ∀ {n x}, fits n x → fits n (-x)
  mul : ∀ {m n x y}, fits m x → fits n y → fits (m+n) (x*y)

variable {R : Type u} [CommRing R]

def polynomialBounds (σ : Type*) (k : Type u) [Field k] : Bounds (MvPolynomial σ k) where
  fits n p := p=0 ∨ (p.totalDegree:ℤ) ≤ n
  mono h a := a.imp_right (fun b => b.trans h)
  zero _ := Or.inl rfl
  one := Or.inr (by simp)
  add := by
    intro n x y hx hy
    rcases hx with rfl|hx
    · simpa using hy
    rcases hy with rfl|hy
    · simpa using Or.inr hx
    right
    have h := totalDegree_add x y
    omega
  neg := by
    intro n x hx
    simpa only [neg_eq_zero,totalDegree_neg] using hx
  mul := by
    intro m n x y hx hy
    rcases hx with rfl|hx
    · exact Or.inl (zero_mul _)
    rcases hy with rfl|hy
    · exact Or.inl (mul_zero _)
    right
    have h := totalDegree_mul x y
    omega

def extend (b : Bounds R) (d : R) (hd : b.fits 4 d) : Bounds (QuadraticAlgebra R d 0) where
  fits n z := b.fits n z.re ∧ b.fits (n-2) z.im
  mono := by
    intro m n x h a
    exact ⟨b.mono h a.1,b.mono (by omega) a.2⟩
  zero n := ⟨b.zero _,b.zero _⟩
  one := ⟨b.one,b.zero _⟩
  add := by
    intro n x y hx hy
    exact ⟨b.add hx.1 hy.1,b.add hx.2 hy.2⟩
  neg := by
    intro n x hx
    exact ⟨b.neg hx.1,b.neg hx.2⟩
  mul := by
    intro m n x y hx hy
    obtain ⟨rx,ix⟩ := hx
    obtain ⟨ry,iy⟩ := hy
    constructor
    · exact b.add (b.mul rx ry) (b.mono (by omega) (b.mul (b.mul hd ix) iy))
    · simp only [QuadraticAlgebra.im_mul,zero_mul,add_zero]
      exact b.add (b.mono (by omega) (b.mul rx iy)) (b.mono (by omega) (b.mul ix ry))

theorem base_fits (b : Bounds R) {d : R} (hd : b.fits 4 d) {n x} (h : b.fits n x) :
    (extend b d hd).fits n (algebraMap R (QuadraticAlgebra R d 0) x) := ⟨h,b.zero _⟩

theorem root_fits (b : Bounds R) {d : R} (hd : b.fits 4 d) :
    (extend b d hd).fits 2 QuadraticAlgebra.omega := ⟨b.zero _,b.one⟩

/-- Each successive norm doubles the current weighted degree, including after
one or more previous square roots have already been adjoined. -/
theorem norm_fits (b : Bounds R) {d : R} (hd : b.fits 4 d) {n z}
    (h : (extend b d hd).fits n z) : b.fits (2*n) z.norm := by
  simp only [QuadraticAlgebra.norm_def,zero_mul,add_zero,sub_eq_add_neg]
  exact b.add (b.mono (by omega) (b.mul h.1 h.1))
    (b.neg (b.mono (by omega) (b.mul (b.mul hd h.2) h.2)))

/-- Ring evaluation with either choice of the square root. -/
def evalRoot {S L : Type*} [CommRing S] [CommRing L] {d : S}
    (f : S →+* L) (r : L) (hr : r^2=f d) : QuadraticAlgebra S d 0 →+* L where
  toFun z := f z.re + f z.im*r
  map_one' := by simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,zero_mul,add_zero,map_add,map_mul]
    linear_combination -(f x.im)*(f y.im)*hr

@[simp] theorem evalRoot_base {S L : Type*} [CommRing S] [CommRing L] {d : S}
    (f : S →+* L) (r : L) (hr : r^2=f d) :
    (evalRoot f r hr).comp (algebraMap S (QuadraticAlgebra S d 0))=f := by
  ext x
  simp [evalRoot]

/-- A finite tower with a polynomial norm and a bound on the change of degree.
The zero over a specialization lifts to a point above it over an algebraically
closed field. Descent of zeros itself works over any field. -/
structure Descent {R S : Type u} [CommRing R] [CommRing S]
    (b : Bounds R) (c : Bounds S) (m : ℕ) where
  incl : R →+* S
  norm : S → R
  bound : ∀ {n x}, c.fits n x → b.fits (m*n) (norm x)
  vanishes : ∀ {L : Type u} [Field L] (g : S →+* L) (x : S),
    g x=0 → g (incl (norm x))=0
  liftZero : ∀ {L : Type u} [Field L] [IsAlgClosed L] (f : R →+* L) (x : S),
    f (norm x)=0 → ∃ g : S →+* L, g.comp incl=f ∧ g x=0

def trivialDescent (b : Bounds R) : Descent b b 1 where
  incl := RingHom.id R
  norm := id
  bound := by simp
  vanishes _ _ h := h
  liftZero f _ h := ⟨f,rfl,h⟩

def quadraticStep {S : Type u} [CommRing S] {b : Bounds R} {c : Bounds S} {m : ℕ}
    (tower : Descent b c m) (d : S) (hd : c.fits 4 d) : Descent b (extend c d hd) (m*2) where
  incl := (algebraMap S (QuadraticAlgebra S d 0)).comp tower.incl
  norm x := tower.norm x.norm
  bound := by
    intro n x hx
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using tower.bound (norm_fits c hd hx)
  vanishes := by
    intro L _ g x hx
    apply tower.vanishes (g.comp (algebraMap S (QuadraticAlgebra S d 0))) x.norm
    simp [QuadraticAlgebra.algebraMap_norm_eq_mul_star,hx]
  liftZero := by
    intro L _ _ f x hx
    obtain ⟨g,hg,hxg⟩ := tower.liftZero f x.norm hx
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (g d) (by decide : 0<2)
    rw [norm_specializes g r hr x,mul_eq_zero] at hxg
    rcases hxg with hp|hm
    · refine ⟨evalRoot g r hr,?_,hp⟩
      rw [← RingHom.comp_assoc,evalRoot_base,hg]
    · have hr' : (-r)^2=g d := by simpa using hr
      refine ⟨evalRoot g (-r) hr',?_,?_⟩
      · rw [← RingHom.comp_assoc,evalRoot_base,hg]
      · change g x.re+g x.im*(-r)=0
        simpa [sub_eq_add_neg] using hm


end
end PlanarUnitDistances.RadicalNorm
