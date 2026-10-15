import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The remaining positive-left-frame support margins for negative B.

These are continuous two-angle inequalities. The displayed nonnegative
polynomials are exact Bernstein identities after the two half-angle changes
of variables. There is no pose enumeration, numerical oracle or native check.
The upper-U alternative uses two continuous scalar intervals;
the upper-V alternative uses one identity on the whole canonical arc.
This module is source only until the final whole-proof compilation. -/
noncomputable section
namespace N12Compact.C849NegativePositiveMargins

def margin0 (c t C S : ℝ) : ℝ :=
  C^2*(2-c-(7/20)*t^2-(3/20)*c*t) +
    C*S*((63/100)+t-(7/20)*c*t-(3/20)*c^2) +
    (19/25)*S^2-C-S

def margin1 (c t C S : ℝ) : ℝ :=
  C^2*((113/50)-(61/100)*t^2-(13/20)*c*t-c) +
    C*S*((113/100)-(61/100)*c*t-(13/20)*c^2+t) +
    (19/25)*S^2-C-S

def margin2 (c t C S : ℝ) : ℝ :=
  C^2*(2+(13/50)*t^2+(1/2)*c*t-c-t) +
    C*S*((63/100)+(13/50)*c*t+(1/2)*c^2+t-c) +
    (19/25)*S^2-C-S

private theorem half_angle (p q : ℝ) (hp : 0<p) (hq : 0≤q)
    (unit : p^2+q^2=1) (canonical : q≤p) :
    let z := q/(1+p)
    0≤z ∧ z≤5/12 ∧ p*(1+z^2)=1-z^2 ∧ q*(1+z^2)=2*z := by
  have denominator : 0<1+p := by linarith only [hp]
  have orderSquare := mul_nonneg (sub_nonneg.mpr canonical)
    (show 0≤p+q by linarith only [hp,hq])
  have qHigh : q≤5/7 := by
    nlinarith only [unit,orderSquare,sq_nonneg (q-5/7)]
  dsimp only
  refine ⟨div_nonneg hq denominator.le, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ denominator).mpr
    linarith only [qHigh,canonical]
  · field_simp [ne_of_gt denominator]
    linear_combination (p+1)*unit
  · field_simp [ne_of_gt denominator]
    linear_combination q*(p+1)*unit

private def certificate0 (x y : ℝ) : ℝ :=
    (449280000*(12*y)*(5-12*y)^3 +
      1160640000*(12*y)^2*(5-12*y)^2 +
      1195440000*(12*y)^3*(5-12*y) +
      421580000*(12*y)^4)*(3-10*x)^4 +
    (93312000*(5-12*y)^4 +
      1833408000*(12*y)*(5-12*y)^3 +
      4159152000*(12*y)^2*(5-12*y)^2 +
      4137828000*(12*y)^3*(5-12*y) +
      1471584500*(12*y)^4)*(10*x)*(3-10*x)^3 +
    (223948800*(5-12*y)^4 +
      2614809600*(12*y)*(5-12*y)^3 +
      5266080000*(12*y)^2*(5-12*y)^2 +
      5139086400*(12*y)^3*(5-12*y) +
      1884367200*(12*y)^4)*(10*x)^2*(3-10*x)^2 +
    (159563520*(5-12*y)^4 +
      1429937280*(12*y)*(5-12*y)^3 +
      2460834720*(12*y)^2*(5-12*y)^2 +
      2440666680*(12*y)^3*(5-12*y) +
      982515095*(12*y)^4)*(10*x)^3*(3-10*x) +
    (12130560*(5-12*y)^4 +
      135710208*(12*y)*(5-12*y)^3 +
      107722944*(12*y)^2*(5-12*y)^2 +
      198130704*(12*y)^3*(5-12*y) +
      140096783*(12*y)^4)*(10*x)^4

private theorem check0 (c t C S x y : ℝ)
    (xlo : 0≤x) (xhi : x≤3/10) (ylo : 0≤y) (yhi : y≤5/12)
    (cx : c*(1+x^2)=1-x^2) (tx : t*(1+x^2)=2*x)
    (Cy : C*(1+y^2)=1-y^2) (Sy : S*(1+y^2)=2*y) :
    margin0 c t C S ≤ 0 := by
  have dx : 0<1+x^2 := by positivity
  have dy : 0<1+y^2 := by positivity
  have ce : c=(1-x^2)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr cx
  have te : t=(2*x)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr tx
  have Ce : C=(1-y^2)/(1+y^2) := (eq_div_iff (ne_of_gt dy)).mpr Cy
  have Se : S=(2*y)/(1+y^2) := (eq_div_iff (ne_of_gt dy)).mpr Sy
  have hxu : 0≤10*x := by linarith only [xlo]
  have hxc : 0≤3-10*x := by linarith only [xhi]
  have hyc : 0≤5-12*y := by linarith only [yhi]
  have positive : 0≤certificate0 x y := by
    unfold certificate0
    positivity
  have identity :
      (-margin0 c t C S)*(1+x^2)^2*(1+y^2)^2*52488000000000 =
        certificate0 x y := by
    unfold margin0 certificate0
    rw [ce,te,Ce,Se]
    field_simp [ne_of_gt dx,ne_of_gt dy] <;> ring
  have factor : 0<(1+x^2)^2*(1+y^2)^2*(52488000000000:ℝ) := by positivity
  have product : 0≤(-margin0 c t C S)*
      ((1+x^2)^2*(1+y^2)^2*(52488000000000:ℝ)) := by
    rw [← identity] at positive
    simpa only [mul_assoc] using positive
  have := (mul_nonneg_iff_of_pos_right factor).mp product
  linarith only [this]

private def certificate1 (x y : ℝ) : ℝ :=
    (11511631872*(5-12*y)^4 +
      54737952768*(12*y)*(5-12*y)^3 +
      55561001472*(12*y)^2*(5-12*y)^2 +
      48474544128*(12*y)^3*(5-12*y) +
      24605833552*(12*y)^4)*(7-20*x)^4 +
    (51495284736*(5-12*y)^4 +
      223264733184*(12*y)*(5-12*y)^3 +
      198639438336*(12*y)^2*(5-12*y)^2 +
      161719592064*(12*y)^3*(5-12*y) +
      88223712176*(12*y)^4)*(20*x-6)*(7-20*x)^3 +
    (84391538688*(5-12*y)^4 +
      335824745472*(12*y)*(5-12*y)^3 +
      252239781888*(12*y)^2*(5-12*y)^2 +
      186769010112*(12*y)^3*(5-12*y) +
      115194565008*(12*y)^4)*(20*x-6)^2*(7-20*x)^2 +
    (60260557824*(5-12*y)^4 +
      220429472256*(12*y)*(5-12*y)^3 +
      130195914624*(12*y)^2*(5-12*y)^2 +
      81873847776*(12*y)^3*(5-12*y) +
      64048650084*(12*y)^4)*(20*x-6)^3*(7-20*x) +
    (15850328832*(5-12*y)^4 +
      53122583808*(12*y)*(5-12*y)^3 +
      21022484832*(12*y)^2*(5-12*y)^2 +
      8343335568*(12*y)^3*(5-12*y) +
      12470785087*(12*y)^4)*(20*x-6)^4

private theorem check1 (c t C S x y : ℝ)
    (xlo : 3/10≤x) (xhi : x≤7/20) (ylo : 0≤y) (yhi : y≤5/12)
    (cx : c*(1+x^2)=1-x^2) (tx : t*(1+x^2)=2*x)
    (Cy : C*(1+y^2)=1-y^2) (Sy : S*(1+y^2)=2*y) :
    margin1 c t C S ≤ 0 := by
  have dx : 0<1+x^2 := by positivity
  have dy : 0<1+y^2 := by positivity
  have ce : c=(1-x^2)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr cx
  have te : t=(2*x)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr tx
  have Ce : C=(1-y^2)/(1+y^2) := (eq_div_iff (ne_of_gt dy)).mpr Cy
  have Se : S=(2*y)/(1+y^2) := (eq_div_iff (ne_of_gt dy)).mpr Sy
  have hxu : 0≤20*x-6 := by linarith only [xlo]
  have hxc : 0≤7-20*x := by linarith only [xhi]
  have hyc : 0≤5-12*y := by linarith only [yhi]
  have positive : 0≤certificate1 x y := by
    unfold certificate1
    positivity
  have identity :
      (-margin1 c t C S)*(1+x^2)^2*(1+y^2)^2*103680000000000 =
        certificate1 x y := by
    unfold margin1 certificate1
    rw [ce,te,Ce,Se]
    field_simp [ne_of_gt dx,ne_of_gt dy] <;> ring
  have factor : 0<(1+x^2)^2*(1+y^2)^2*(103680000000000:ℝ) := by positivity
  have product : 0≤(-margin1 c t C S)*
      ((1+x^2)^2*(1+y^2)^2*(103680000000000:ℝ)) := by
    rw [← identity] at positive
    simpa only [mul_assoc] using positive
  have := (mul_nonneg_iff_of_pos_right factor).mp product
  linarith only [this]

private def certificate2 (x y : ℝ) : ℝ :=
    (779341824*(12*y)*(5-12*y)^5 +
      3702620160*(12*y)^2*(5-12*y)^4 +
      7192800000*(12*y)^3*(5-12*y)^3 +
      7091297280*(12*y)^4*(5-12*y)^2 +
      3517966080*(12*y)^5*(5-12*y) +
      696190464*(12*y)^6)*(5-12*x)^4 +
    (447897600*(5-12*y)^6 +
      4864167936*(12*y)*(5-12*y)^5 +
      16670499840*(12*y)^2*(5-12*y)^4 +
      27864518400*(12*y)^3*(5-12*y)^3 +
      25248071520*(12*y)^4*(5-12*y)^2 +
      11951133120*(12*y)^5*(5-12*y) +
      2313350496*(12*y)^6)*(12*x)*(5-12*x)^3 +
    (776355840*(5-12*y)^6 +
      6783035904*(12*y)*(5-12*y)^5 +
      20768348160*(12*y)^2*(5-12*y)^4 +
      32375484000*(12*y)^3*(5-12*y)^3 +
      28313484480*(12*y)^4*(5-12*y)^2 +
      13316865120*(12*y)^5*(5-12*y) +
      2617196544*(12*y)^6)*(12*x)^2*(5-12*x)^2 +
    (442298880*(5-12*y)^6 +
      3394711296*(12*y)*(5-12*y)^5 +
      9274357440*(12*y)^2*(5-12*y)^4 +
      13327822800*(12*y)^3*(5-12*y)^3 +
      11359084770*(12*y)^4*(5-12*y)^2 +
      5512367700*(12*y)^5*(5-12*y) +
      1159160706*(12*y)^6)*(12*x)^3*(5-12*x) +
    (49040640*(5-12*y)^6 +
      277191504*(12*y)*(5-12*y)^5 +
      365988960*(12*y)^2*(5-12*y)^4 +
      104229075*(12*y)^3*(5-12*y)^3 +
      65283905*(12*y)^4*(5-12*y)^2 +
      190122745*(12*y)^5*(5-12*y) +
      91229819*(12*y)^6)*(12*x)^4

private theorem check2 (c t C S x y : ℝ)
    (xlo : 0≤x) (xhi : x≤5/12) (ylo : 0≤y) (yhi : y≤5/12)
    (cx : c*(1+x^2)=1-x^2) (tx : t*(1+x^2)=2*x)
    (Cy : C*(1+y^2)=1-y^2) (Sy : S*(1+y^2)=2*y) :
    margin2 c t C S ≤ 0 := by
  have dx : 0<1+x^2 := by positivity
  have dy : 0<1+y^2 := by positivity
  have ce : c=(1-x^2)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr cx
  have te : t=(2*x)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr tx
  have Ce : C=(1-y^2)/(1+y^2) := (eq_div_iff (ne_of_gt dy)).mpr Cy
  have Se : S=(2*y)/(1+y^2) := (eq_div_iff (ne_of_gt dy)).mpr Sy
  have hxu : 0≤12*x := by linarith only [xlo]
  have hxc : 0≤5-12*x := by linarith only [xhi]
  have hyc : 0≤5-12*y := by linarith only [yhi]
  have positive : 0≤certificate2 x y := by
    unfold certificate2
    positivity
  have identity :
      (-margin2 c t C S)*(1+x^2)^2*(1+y^2)^2*10497600000000000 =
        certificate2 x y := by
    unfold margin2 certificate2
    rw [ce,te,Ce,Se]
    field_simp [ne_of_gt dx,ne_of_gt dy] <;> ring
  have factor : 0<(1+x^2)^2*(1+y^2)^2*(10497600000000000:ℝ) := by positivity
  have product : 0≤(-margin2 c t C S)*
      ((1+x^2)^2*(1+y^2)^2*(10497600000000000:ℝ)) := by
    rw [← identity] at positive
    simpa only [mul_assoc] using positive
  have := (mul_nonneg_iff_of_pos_right factor).mp product
  linarith only [this]

/-- The C upper-U alternative. Its original corner-square inequality
supplies c≥50/63. Only two continuous half-angle intervals are needed. -/
theorem upperU (c t C S : ℝ) (hc : 0<c) (ht : 0≤t)
    (unit : c^2+t^2=1) (canonical : t≤c)
    (hC : 0<C) (hS : 0≤S) (unitL : C^2+S^2=1) (canonicalL : S≤C)
    (cLower : 50/63≤c) :
    margin0 c t C S ≤ 0 ∨ margin1 c t C S ≤ 0 := by
  let x := t/(1+c)
  let y := S/(1+C)
  obtain ⟨xlo,xhi,cx,tx⟩ := half_angle c t hc ht unit canonical
  obtain ⟨ylo,yhi,Cy,Sy⟩ := half_angle C S hC hS unitL canonicalL
  change 0≤x at xlo
  change x≤5/12 at xhi
  change c*(1+x^2)=1-x^2 at cx
  change t*(1+x^2)=2*x at tx
  change 0≤y at ylo
  change y≤5/12 at yhi
  change C*(1+y^2)=1-y^2 at Cy
  change S*(1+y^2)=2*y at Sy
  have extra := mul_nonneg (sub_nonneg.mpr cLower)
    (show 0≤1+x^2 by positivity)
  have small : x≤7/20 := by
    nlinarith only [cx,extra,sq_nonneg (x-7/20)]
  by_cases split : x≤3/10
  · exact Or.inl (check0 c t C S x y xlo split ylo yhi cx tx Cy Sy)
  · exact Or.inr (check1 c t C S x y (le_of_lt (lt_of_not_ge split))
      small ylo yhi cx tx Cy Sy)

/-- The C upper-V alternative on the entire canonical negative B arc. -/
theorem upperV (c t C S : ℝ) (hc : 0<c) (ht : 0≤t)
    (unit : c^2+t^2=1) (canonical : t≤c)
    (hC : 0<C) (hS : 0≤S) (unitL : C^2+S^2=1) (canonicalL : S≤C) :
    margin2 c t C S ≤ 0 := by
  obtain ⟨xlo,xhi,cx,tx⟩ := half_angle c t hc ht unit canonical
  obtain ⟨ylo,yhi,Cy,Sy⟩ := half_angle C S hC hS unitL canonicalL
  exact check2 c t C S (t/(1+c)) (S/(1+C))
    xlo xhi ylo yhi cx tx Cy Sy

#print axioms upperU
#print axioms upperV
end N12Compact.C849NegativePositiveMargins
