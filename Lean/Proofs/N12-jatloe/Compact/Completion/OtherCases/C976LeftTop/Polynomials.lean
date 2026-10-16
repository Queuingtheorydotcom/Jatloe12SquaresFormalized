import Compact.Completion.CommonCases.BernsteinQuartic

noncomputable section

/-! The two complete bivariate quartics in C976-LEFT-TOP-ANGLE.md section7.
The 25 coefficients of each polynomial are the exact expansion of the
chapter's rational Bernstein formula on its stated rectangle. The most
delicate last coefficients match the manuscript's printed fractions.
Nested univariate identities prove positivity on the whole rectangles.
Source only; no Lean compilation has been run. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.Polynomials
open CommonCases.BernsteinQuartic
set_option Elab.async false

def Phi (r w : ℝ) : ℝ := 4*(w-1)*(
  650*r^4*w^3-4181*r^4*w^2-3531*r^4*w-
  5762*r^3*w^3+762*r^3*w^2+5086*r^3*w+3362*r^3+
  1100*r^2*w^3+4800*r^2*w^2+2600*r^2*w-1100*r^2-
  2062*r*w^3+2262*r*w^2-814*r*w-338*r-
  650*w^3+481*w^2-169*w)

def Plo (r w : ℝ) : ℝ := 2*(w-1)*(
  2626*r^4*w^3-2140*r^4*w^2-3492*r^4*w-1326*r^4-
  11875*r^3*w^3-123*r^3*w^2+9227*r^3*w+7075*r^3+
  3500*r^2*w^3+15700*r^2*w^2+8700*r^2*w-3500*r^2-
  4475*r*w^3+2877*r*w^2-2573*r*w-325*r-
  1326*w^3+840*w^2-408*w+26)

def hiCertificate (u v : ℝ) : ℝ := value u
  (value v (576425601/2500000) (61343959377/275000000)
    (549771560687/2552343750) (11662883977037/56151562500) (18539000153896/92650078125))
  (value v (3234097557/13040000) (260894951/1100000)
    (15056227652929/66565125000) (1193807392403/5547093750) (617327770586386/3020392546875))
  (value v (50925234847/212552000) (23642049567373/105213240000)
    (136528744328231/651006922500) (465048107173409/2387025382500) (10644535395409252/59078878216875))
  (value v (266411996457/1385839040) (3591848363311/20787585600)
    (24104253924679/157206116100) (9274698666875/69170691084) (4932058421246332/42799365108225))
  (value v (1077874742655/11294588176) (1105819449107/15530058742)
    (108659091293749/2306213723187) (594100361054744/25368350955057) (271661855034224/837155581516881))

def loCertificate (u v : ℝ) : ℝ := value u
  (value v (68351412/390625) (4620997149/19531250)
    (60362514731/244140625) (11691483495219/48828125000) (138809174244633/610351562500))
  (value v (1279692893/5093750) (38618050889/127343750)
    (3792499475861/12734375000) (86529024218359/318359375000) (7711611015318373/31835937500000))
  (value v (16453209689/49816875) (181879023877/498168750)
    (125410860360259/373626562500) (353607363000067/1245421875000) (23904304319516043/103785156250000))
  (value v (43101011766/108268675) (2208517500383/5413433750)
    (140778777316973/406007531250) (3548515512650273/13533584375000) (60484811879859163/338339609375000))
  (value v (312461268540/705911761) (7410813902292/17647794025)
    (28183130714259/88238970125) (2156292523401063/11029871265625) (17028128160128427/220597425312500))

theorem hi_identity (r w : ℝ) : Phi r w =
    hiCertificate ((4075*r-652)/673) ((132*w-33)/7) := by
  dsimp only [Phi,hiCertificate,value]
  ring

theorem lo_identity (r w : ℝ) : Plo r w =
    loCertificate ((4075*r-652)/673) ((50/13)*w) := by
  dsimp only [Plo,loCertificate,value]
  ring

theorem hi_positive (r w : ℝ) (rlo : 4/25 ≤ r) (rhi : r ≤ 53/163)
    (wlo : 1/4 ≤ w) (whi : w ≤ 10/33) : 0 < Phi r w := by
  have un : 0 ≤ (4075*r-652)/673 := by linarith only [rlo]
  have uu : (4075*r-652)/673 ≤ 1 := by linarith only [rhi]
  have vn : 0 ≤ (132*w-33)/7 := by linarith only [wlo]
  have vu : (132*w-33)/7 ≤ 1 := by linarith only [whi]
  rw [hi_identity]
  dsimp only [hiCertificate]
  apply positive _ _ _ _ _ _ un uu <;>
    apply positive _ _ _ _ _ _ vn vu <;> norm_num

theorem lo_positive (r w : ℝ) (rlo : 4/25 ≤ r) (rhi : r ≤ 53/163)
    (wlo : 0 ≤ w) (whi : w ≤ 13/50) : 0 < Plo r w := by
  have un : 0 ≤ (4075*r-652)/673 := by linarith only [rlo]
  have uu : (4075*r-652)/673 ≤ 1 := by linarith only [rhi]
  have vn : 0 ≤ (50/13)*w := by linarith only [wlo]
  have vu : (50/13)*w ≤ 1 := by linarith only [whi]
  rw [lo_identity]
  dsimp only [loCertificate]
  apply positive _ _ _ _ _ _ un uu <;>
    apply positive _ _ _ _ _ _ vn vu <;> norm_num

end N12Compact.Completion.OtherCases.C976LeftTop.Polynomials
