import Compact.Geometry.ClosedFrames
import S12.ShortCluster
import S12.Convex

/-! The inward central square owns a strict horizontal bar for every
orientation. The proof uses only short opposite-face obstructions and the
original three strict anchors; exterior equalities are preserved. -/
namespace N12Compact.CommonCases.InwardPoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive_strong (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (origin : q.Inside 0 0)
    (a : q.Inside (7/20) (-9/100)) (d : q.Inside (13/50) (13/50))
    (missingL : ¬q.Inside (-7/20) (-9/100))
    (missingE : ¬q.Inside (2/5) (-37/50)) :
    q.Inside (27/50) (1/4) := by
  have kl := short_projections q (89/100) (17/50) (by norm_num)
  have ke := short_projections q (7/50) (99/100) (by norm_num)
  have le := short_projections q (-3/4) (13/20) (by norm_num)
  have anchor : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa [OpenSquare.Inside,InBands] using origin
  have kLowU : q.loU < q.c*(27/50)+q.s*(1/4) := by
    linarith only [anchor.1,cp,sn]
  have kLowV : q.loV < -q.s*(27/50)+q.c*(1/4) := by
    linarith only [a.2.2.1,cp,order]
  have kHighV : -q.s*(27/50)+q.c*(1/4) < q.loV+q.side := by
    linarith only [d.2.2.2,cp,sn]
  have lHighU : q.c*(-7/20)+q.s*(-9/100) < q.loU+q.side := by
    linarith only [anchor.2.1,cp,sn]
  have lLowV : q.loV < -q.s*(-7/20)+q.c*(-9/100) := by
    linarith only [a.2.2.1,sn]
  have kHighU : q.c*(27/50)+q.s*(1/4) < q.loU+q.side := by
    by_cases shallow : 61*q.s ≤ 35*q.c
    · have lHighV : -q.s*(-7/20)+q.c*(-9/100) < q.loV+q.side := by
        linarith only [d.2.2.2,shallow]
      have lFace : q.c*(-7/20)+q.s*(-9/100) ≤ q.loU :=
        le_of_not_gt (fun h => missingL ⟨h,lHighU,lLowV,lHighV⟩)
      linarith only [lFace,kl.2.1,side]
    · by_cases lowerL : q.c*(-7/20)+q.s*(-9/100) ≤ q.loU
      · linarith only [lowerL,kl.2.1,side]
      · have lFace : q.loV+q.side ≤ -q.s*(-7/20)+q.c*(-9/100) :=
          le_of_not_gt (fun h => missingL
            ⟨lt_of_not_ge lowerL,lHighU,lLowV,h⟩)
        have eHighU : q.c*(2/5)+q.s*(-37/50) < q.loU+q.side := by
          linarith only [a.2.1,shallow,cp]
        have eHighV : -q.s*(2/5)+q.c*(-37/50) < q.loV+q.side := by
          linarith only [anchor.2.2.2,cp,sn]
        have eLowV : q.loV < -q.s*(2/5)+q.c*(-37/50) := by
          linarith only [lFace,le.2.2.2,side]
        have eFace : q.c*(2/5)+q.s*(-37/50) ≤ q.loU :=
          le_of_not_gt (fun h => missingE ⟨h,eHighU,eLowV,eHighV⟩)
        linarith only [eFace,ke.2.1,side]
  exact ⟨kLowU,kHighU,kLowV,kHighV⟩

private theorem negative_strong (q : OpenSquare) (t : ℝ) (signed : q.s = -t)
    (side : 1 < q.side) (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c)
    (origin : q.Inside 0 0)
    (a : q.Inside (7/20) (-9/100)) (d : q.Inside (13/50) (13/50))
    (missingL : ¬q.Inside (-7/20) (-9/100))
    (missingN : ¬q.Inside (7/20) (61/100))
    (missingE : ¬q.Inside (2/5) (-37/50)) :
    q.Inside (27/50) (1/4) := by
  have kl := short_projections q (89/100) (17/50) (by norm_num)
  have ke := short_projections q (7/50) (99/100) (by norm_num)
  have el := short_projections q (3/4) (-13/20) (by norm_num)
  have nl := short_projections q (7/10) (7/10) (by norm_num)
  rw [signed] at kl ke el nl
  have anchor : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa [OpenSquare.Inside,InBands] using origin
  have aa := a
  simp only [OpenSquare.Inside,InBands,signed] at aa
  have lMissing : ¬ (q.loU < -(7/20)*q.c+(9/100)*t ∧
      -(7/20)*q.c+(9/100)*t < q.loU+q.side ∧
      q.loV < -(7/20)*t-(9/100)*q.c ∧
      -(7/20)*t-(9/100)*q.c < q.loV+q.side) := by
    intro h; apply missingL
    dsimp [OpenSquare.Inside,InBands]; rw [signed]
    convert h using 1 <;> ring
  have eMissing : ¬ (q.loU < (2/5)*q.c+(37/50)*t ∧
      (2/5)*q.c+(37/50)*t < q.loU+q.side ∧
      q.loV < (2/5)*t-(37/50)*q.c ∧
      (2/5)*t-(37/50)*q.c < q.loV+q.side) := by
    intro h; apply missingE
    dsimp [OpenSquare.Inside,InBands]; rw [signed]
    convert h using 1 <;> ring
  have lHighU : -(7/20)*q.c+(9/100)*t < q.loU+q.side := by
    linarith only [anchor.2.1,cp,order]
  have lHighV : -(7/20)*t-(9/100)*q.c < q.loV+q.side := by
    linarith only [anchor.2.2.2,cp,tn]
  have eLowU : q.loU < (2/5)*q.c+(37/50)*t := by
    linarith only [anchor.1,cp,tn]
  have eHighV : (2/5)*t-(37/50)*q.c < q.loV+q.side := by
    linarith only [anchor.2.2.2,cp,order]
  have kLowU : q.loU < (27/50)*q.c-(1/4)*t := by
    linarith only [anchor.1,cp,order]
  have kLowV : q.loV < (27/50)*t+(1/4)*q.c := by
    linarith only [aa.2.2.1,cp,tn]
  have kHighV : (27/50)*t+(1/4)*q.c < q.loV+q.side := by
    by_cases eLowV : (2/5)*t-(37/50)*q.c ≤ q.loV
    · linarith only [eLowV,ke.2.2.2,side]
    · have eFace : q.loU+q.side ≤ (2/5)*q.c+(37/50)*t :=
        le_of_not_gt (fun h => eMissing ⟨eLowU,h,lt_of_not_ge eLowV,eHighV⟩)
      have lLowU : q.loU < -(7/20)*q.c+(9/100)*t := by
        linarith only [eFace,el.2.1,side]
      have lFace : -(7/20)*t-(9/100)*q.c ≤ q.loV :=
        le_of_not_gt (fun h => lMissing ⟨lLowU,lHighU,h,lHighV⟩)
      linarith only [lFace,kl.2.2.2,side]
  have kHighU : (27/50)*q.c-(1/4)*t < q.loU+q.side := by
    by_cases steep : 19*q.c ≤ 34*t
    · linarith only [aa.2.1,steep]
    · have nLowU : q.loU < (7/20)*q.c-(61/100)*t := by
        linarith only [anchor.1,steep,cp]
      have nHighU : (7/20)*q.c-(61/100)*t < q.loU+q.side := by
        linarith only [aa.2.1,tn]
      have nLowV : q.loV < (7/20)*t+(61/100)*q.c := by
        linarith only [anchor.2.2.1,cp,tn]
      have nFace : q.loV+q.side ≤ (7/20)*t+(61/100)*q.c := by
        apply le_of_not_gt
        intro h
        apply missingN
        dsimp [OpenSquare.Inside,InBands]; rw [signed]
        refine ⟨?_,?_,?_,?_⟩ <;> linarith only [nLowU,nHighU,nLowV,h]
      have lLowV : q.loV < -(7/20)*t-(9/100)*q.c := by
        linarith only [nFace,nl.2.2.2,side]
      have lFace : -(7/20)*q.c+(9/100)*t ≤ q.loU :=
        le_of_not_gt (fun h => lMissing ⟨h,lHighU,lLowV,lHighV⟩)
      linarith only [lFace,kl.2.1,side]
  dsimp [OpenSquare.Inside,InBands]
  rw [signed]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [kLowU,kHighU,kLowV,kHighV]

theorem strong (q : OpenSquare) (side : 1 < q.side)
    (origin : q.Inside 0 0)
    (a : q.Inside (7/20) (-9/100)) (d : q.Inside (13/50) (13/50))
    (missingL : ¬q.Inside (-7/20) (-9/100))
    (missingN : ¬q.Inside (7/20) (61/100))
    (missingE : ¬q.Inside (2/5) (-37/50)) : q.Inside (27/50) (1/4) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have o := (same 0 0).mpr origin
  have aa := (same (7/20) (-9/100)).mpr a
  have dd := (same (13/50) (13/50)).mpr d
  have l : ¬r.Inside (-7/20) (-9/100) := fun h => missingL ((same _ _).mp h)
  have n : ¬r.Inside (7/20) (61/100) := fun h => missingN ((same _ _).mp h)
  have e : ¬r.Inside (2/5) (-37/50) := fun h => missingE ((same _ _).mp h)
  apply (same _ _).mp
  by_cases sign : 0 ≤ r.s
  · exact positive_strong r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) o aa dd l e
  · exact negative_strong r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) o aa dd l n e

theorem strong_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (33/20))
    (inward : q.Inside 2 (87/50)) (elbow : q.Inside (113/50) 2)
    (missingSW : ¬q.Inside (33/20) (33/20))
    (missingNE : ¬q.Inside (47/20) (47/20))
    (missingBottom : ¬q.Inside (12/5) 1) : q.Inside (127/50) (199/100) := by
  have h := strong (q.translated 2 (87/50)) side
    (by norm_num [inside_translated_iff]; exact inward)
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact missingSW)
    (by norm_num [inside_translated_iff]; exact missingNE)
    (by norm_num [inside_translated_iff]; exact missingBottom)
  norm_num [inside_translated_iff] at h
  exact h

/-- The original duplicate point follows by one strict triangle combination
from the stronger endpoint and the two strict central anchors. -/
theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (33/20))
    (inward : q.Inside 2 (87/50)) (elbow : q.Inside (113/50) 2)
    (missingSW : ¬q.Inside (33/20) (33/20))
    (missingNE : ¬q.Inside (47/20) (47/20))
    (missingBottom : ¬q.Inside (12/5) 1) : q.Inside (123/50) (199/100) := by
  have endpoint := strong_original q side marker inward elbow missingSW missingNE missingBottom
  let cert : TriangleCertificate :=
    ⟨(113/50,2),(47/20,33/20),(127/50,199/100),(123/50,199/100),1/35,691/971⟩
  have checked : cert.Check := by decide +kernel
  have h := triangle_certificate_sound cert checked q
    (by norm_num [cert]; exact elbow)
    (by norm_num [cert]; exact marker)
    (by norm_num [cert]; exact endpoint)
  norm_num [cert] at h
  exact h

#print axioms strong_original
#print axioms point_original
end N12Compact.CommonCases.InwardPoint
