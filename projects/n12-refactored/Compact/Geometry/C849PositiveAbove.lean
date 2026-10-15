import Compact.Geometry.PositiveBLeftReduction

/-! Original-square binding of the positive-B / upper-U-C sector.
The separate C lower-V sector is left open. No complete849/851 exclusion
is declared by this file. -/
namespace N12Compact.C849PositiveAbove

open S12 S12Pilot FourSquareAnchors

theorem c_missing_faces (C : OpenSquare)
    (hc : 0 < C.c) (hs : 0 ≤ C.s)
    (q : ClosedInside C (113/50) 3)
    (k : ClosedInside C 3 (1543/500))
    (missing : ¬ C.Inside (1543/500) 3) :
    C.loU+C.side ≤ C.c*(1543/500)+C.s*3 ∨
      -C.s*(1543/500)+C.c*3 ≤ C.loV := by
  have lowerU : C.loU < C.c*(1543/500)+C.s*3 := by
    linarith only [q.1,hc]
  have upperV : -C.s*(1543/500)+C.c*3 < C.loV+C.side := by
    linarith only [k.2.2.2,hc,hs]
  by_cases above : C.loU+C.side ≤ C.c*(1543/500)+C.s*3
  · exact Or.inl above
  · exact Or.inr (le_of_not_gt (fun below =>
      missing ⟨lowerU,lt_of_not_ge above,below,upperV⟩))

/-- A point forced by the actual C square in its upper-U missing-point
sector. The strict auxiliary Q premise is retained at the axis endpoint. -/
theorem c_forced_point (C : OpenSquare)
    (hc : 0 < C.c) (hs : 0 ≤ C.s) (ha : 1 < C.side)
    (q : C.Inside (113/50) 3)
    (w : ClosedInside C (213/100) (81/25))
    (k : ClosedInside C 3 (1543/500))
    (above : C.loU+C.side ≤ C.c*(1543/500)+C.s*3) :
    C.Inside (1043/500) 3 := by
  have order : C.s ≤ C.c := by linarith only [k.2.1,above]
  have cBound : C.c ≤ 1 := by nlinarith only [C.unit_normal,sq_nonneg C.s]
  exact ⟨by linarith only [above,ha,cBound],
    by linarith only [q.2.1,hc],
    by linarith only [q.2.2.1,hs],
    by linarith only [w.2.2.2,order,hc]⟩

/-- The resulting foreign point gives the exact B cap needed by the new
endgame. Its other three faces follow from B's own original markers. -/
theorem b_right_cap (B C : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (high : ClosedInside B 2 (1543/500))
    (point : C.Inside (1043/500) 3)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ C.Inside x y)) :
    B.loU+B.side ≤ (1043/500)*B.c+3*B.s := by
  have lowerU : B.loU < B.c*(1043/500)+B.s*3 := by
    linarith only [top.1,bc]
  have lowerV : B.loV < -B.s*(1043/500)+B.c*3 := by
    linarith only [bottom.2.2.1,bsc,bc]
  have upperV : -B.s*(1043/500)+B.c*3 < B.loV+B.side := by
    linarith only [high.2.2.2,bc,bs]
  apply le_of_not_gt
  intro upperU
  exact apart _ _ ⟨⟨lowerU,by linarith only [upperU],lowerV,upperV⟩,point⟩

/-- B strictly owns its upper marker, so the already forced A point can
miss B only through the lower V face. The strict marker premise handles
the axis endpoint without assuming any numerical angle bound. -/
theorem b_lower_face (B : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s)
    (bottom : ClosedInside B (33/20) (47/20))
    (high : B.Inside 2 (1543/500))
    (missing : ¬ B.Inside 2 (5/2)) :
    -2*B.s+(5/2)*B.c ≤ B.loV := by
  have lowerU : B.loU < B.c*2+B.s*(5/2) := by
    linarith only [bottom.1,bc,bs]
  have upperU : B.c*2+B.s*(5/2) < B.loU+B.side := by
    linarith only [high.2.1,bs]
  have upperV : -B.s*2+B.c*(5/2) < B.loV+B.side := by
    linarith only [high.2.2.2,bc]
  apply le_of_not_gt
  intro lowerV
  exact missing ⟨lowerU,upperU,by linarith only [lowerV],upperV⟩

/-- This complete sector contradiction uses the actual C shape and the
upper-left owner's actual missing marker (1,3). Remaining sectors must
still be proved before either original case can enter the registry. -/
theorem impossible (B L C : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (cc : 0 < C.c) (cs : 0 ≤ C.s)
    (haB : 1 < B.side) (haC : 1 < C.side) (same : B.side = L.side)
    (boxL : InsideContainer L)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (high : B.Inside 2 (1543/500))
    (missingA : ¬ B.Inside 2 (5/2))
    (cornerMissing : ¬ B.Inside 1 3)
    (left : ClosedInside L (457/500) 2)
    (lTop : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (cq : C.Inside (113/50) 3)
    (cw : ClosedInside C (213/100) (81/25))
    (ck : ClosedInside C 3 (1543/500))
    (above : C.loU+C.side ≤ C.c*(1543/500)+C.s*3)
    (bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y))
    (bcApart : ∀ x y, ¬ (B.Inside x y ∧ C.Inside x y)) : False := by
  have point := c_forced_point C cc cs haC cq cw ck above
  have highClosed : ClosedInside B 2 (1543/500) :=
    ⟨high.1.le,high.2.1.le,high.2.2.1.le,high.2.2.2.le⟩
  have cap := b_right_cap B C bc bs bsc bottom top highClosed point bcApart
  have lower := b_lower_face B bc bs bottom high missingA
  exact PositiveBLeftReduction.impossible_with_right_cap B L bc bs bsc lc lsc
    haB same boxL bottom top lower cap cornerMissing left lTop
    missingLow missingRight bl

#print axioms impossible
end N12Compact.C849PositiveAbove
