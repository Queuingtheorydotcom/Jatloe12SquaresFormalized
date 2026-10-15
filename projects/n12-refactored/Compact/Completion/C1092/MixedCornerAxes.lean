import Compact.Completion.C1092.MixedCornerSupports

/-! Complete separating-axis reduction for the actual mixed wall and
its paired corner. Every reverse direction and every up-left source is
excluded using strict points of those same two squares. -/
namespace N12Compact.C1092MixedCornerAxes
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic C1092MixedCornerSupports
set_option Elab.async false

theorem left_blocked (L K : OpenSquare) (side : 1<L.side)
    (dn : Normal L.c L.s) (rp : 0<L.s)
    (G : L.Inside 0 (2/5)) (face : -(2/5)*L.c≤L.loV)
    (cap : L.loU+L.side≤L.s/2) (H : K.Inside 0 (1/2))
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : nx≤0)
    (sep : upper L nx ny≤lower K nx ny) : False := by
  have yp := upward L K nx ny unit G H sep
  have a := up_left L side dn rp G face cap ny (-nx) yp (neg_nonneg.mpr xn)
  have b := (strict_bounds K _ _ nx ny unit H).1
  simp only [neg_neg] at a
  linarith only [a,b,sep]

private theorem reverse_blocked (L K : OpenSquare) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (yn : 0≤ny) (sep : upper K nx ny≤lower L nx ny) : False := by
  have a := (strict_bounds L _ _ nx ny unit G).1
  have b := (strict_bounds K _ _ nx ny unit H).2
  linarith only [a,b,yn,sep]

theorem alternatives (L K : OpenSquare) (side : 1<L.side) (same : L.side=K.side)
    (dn : Normal L.c L.s) (rp : 0<L.s) (kc : 0<K.c)
    (G : L.Inside 0 (2/5)) (face : -(2/5)*L.c≤L.loV)
    (H : K.Inside 0 (1/2))
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) :
    L.loU+L.side≤lower K L.c L.s ∨
      upper L K.c K.s≤K.loU ∨ upper L (-K.s) K.c≤K.loV := by
  have cap := upper_cap L side dn rp G face (fun h => apart _ _ ⟨h,H⟩)
  have dp : 0<L.c := by linarith only [(normal_bounds dn).1]
  have all := CongruentSAT.faceSeparation_of_disjoint L K same apart
  change pairRadius L K≤|L.c*(centerX K-centerX L)+L.s*(centerY K-centerY L)| ∨
    pairRadius L K≤|-L.s*(centerX K-centerX L)+L.c*(centerY K-centerY L)| ∨
    pairRadius K L≤|K.c*(centerX K-centerX L)+K.s*(centerY K-centerY L)| ∨
    pairRadius K L≤|-K.s*(centerX K-centerX L)+K.c*(centerY K-centerY L)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius L nx ny+supportRadius K nx ny=radius)
      (sep : radius≤|nx*(centerX K-centerX L)+ny*(centerY K-centerY L)|) :=
    separated L K nx ny (by rwa [identity])
  rcases all with lu | lv | ku | kv
  · have sep := split L.c L.s _ (parallel_radius L K) lu
    rcases sep with forward | reverse
    · exact Or.inl (by simpa only [(ownU L).2] using forward)
    · exact (reverse_blocked L K G H _ _ L.unit_normal rp.le reverse).elim
  · have sep := split (-L.s) L.c _ (transverse_radius L K) lv
    rcases sep with forward | reverse
    · exact (left_blocked L K side dn rp G face cap H _ _
        (by nlinarith only [L.unit_normal]) (by linarith only [rp]) forward).elim
    · exact (reverse_blocked L K G H _ _ (by nlinarith only [L.unit_normal]) dp.le reverse).elim
  · have identity : supportRadius L K.c K.s+supportRadius K K.c K.s=pairRadius K L := by
      rw [add_comm]
      exact parallel_radius K L
    have sep := split K.c K.s _ identity ku
    rcases sep with forward | reverse
    · exact Or.inr (Or.inl (by simpa only [(ownU K).1] using forward))
    · have flipped : upper L (-K.c) (-K.s)≤lower K (-K.c) (-K.s) := by
        rw [(negative_support L K.c K.s).2,(negative_support K K.c K.s).1]
        exact neg_le_neg reverse
      exact (left_blocked L K side dn rp G face cap H _ _
        (by nlinarith only [K.unit_normal]) (by linarith only [kc]) flipped).elim
  · have identity : supportRadius L (-K.s) K.c+supportRadius K (-K.s) K.c=pairRadius K L := by
      rw [add_comm]
      exact transverse_radius K L
    have sep := split (-K.s) K.c _ identity kv
    rcases sep with forward | reverse
    · exact Or.inr (Or.inr (by simpa only [(ownV K).1] using forward))
    · exact (reverse_blocked L K G H _ _ (by nlinarith only [K.unit_normal]) kc.le reverse).elim

#print axioms alternatives
end N12Compact.C1092MixedCornerAxes
