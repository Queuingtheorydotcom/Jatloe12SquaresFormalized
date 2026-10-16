import Compact.Geometry.CentralRightIncomingPositive

/-! The incoming central-axis support comparison is homogeneous in its
test direction. Every signed canonical central frame is covered when
the test angle is at least the adjacent central angle. -/
namespace N12Compact.CentralRightIncomingOrdered

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977NegativeCorner
set_option Elab.async false

private theorem normal_bounds (B : OpenSquare) (canonical : |B.s|≤B.c) :
    0<B.c ∧ B.c≤1 := by
  have zero := le_trans (abs_nonneg B.s) canonical
  have signs := abs_le.mp canonical
  constructor
  · by_contra no
    have c : B.c=0 := by linarith only [zero,no]
    have s : B.s=0 := by linarith only [c,signs.1,signs.2]
    nlinarith only [c,s,B.unit_normal]
  · nlinarith only [B.unit_normal,sq_nonneg B.s,sq_nonneg (B.c-1)]

/-- The two cone endpoints are B's own direction and the diagonal.
Their margins are c−1 and −(c+s)(1−.65c−.35s), respectively. -/
private theorem margin (B : OpenSquare) {C S : ℝ}
    (test : |S|≤C) (canonical : |B.s|≤B.c)
    (order : 0≤S*B.c-C*B.s) :
    (C*B.c+S*B.s)*(3*B.c+2*B.s-1)+
      (S*B.c-C*B.s)*((33/20)*B.c-(47/20)*B.s)≤2*(C+S) := by
  have b := normal_bounds B canonical
  have bs := abs_le.mp canonical
  have ts := abs_le.mp test
  have cp := le_trans (abs_nonneg S) test
  let dx := 1-B.c-(13/20)*B.s^2+(7/20)*B.c*B.s
  let dy := -(7/20)+(7/20)*B.s^2+(13/20)*B.c*B.s-B.s
  have base : B.c*dx+B.s*dy=B.c-1 := by
    dsimp [dx,dy]
    linear_combination ((7/20)*B.s-1)*B.unit_normal
  have last : dx+dy= -(B.c+B.s)*(1-(13/20)*B.c-(7/20)*B.s) := by
    dsimp [dx,dy]
    linear_combination -(13/20)*B.unit_normal
  have lastNonpos : dx+dy≤0 := by
    have product := mul_nonneg (show 0≤B.c+B.s by linarith only [bs.1])
      (show 0≤1-(13/20)*B.c-(7/20)*B.s by linarith only [bs.2,b.2])
    nlinarith only [last,product]
  have linearNonpos : C*dx+S*dy≤0 := by
    clear_value dx dy
    by_cases diagonal : B.c=B.s
    · have same : C=S := by
        rw [←diagonal] at order
        nlinarith only [order,b.1,ts.2]
      have product := mul_nonneg cp (show 0≤-(dx+dy) by linarith only [lastNonpos])
      rw [←same]
      nlinarith only [product,same]
    · have positive : 0<B.c-B.s := sub_pos.mpr (lt_of_le_of_ne bs.2 (Ne.symm diagonal))
      have first := mul_nonneg (sub_nonneg.mpr ts.2) (sub_nonneg.mpr b.2)
      have second := mul_nonneg order (show 0≤-(dx+dy) by linarith only [lastNonpos])
      have cone : (B.c-B.s)*(C*dx+S*dy)=
          (C-S)*(B.c*dx+B.s*dy)+(S*B.c-C*B.s)*(dx+dy) := by ring
      have scaled : (B.c-B.s)*(C*dx+S*dy)≤0 := by
        rw [base] at cone
        nlinarith only [cone,base,first,second]
      exact nonpos_of_mul_nonpos_right scaled positive
  have expression :
      (C*B.c+S*B.s)*(3*B.c+2*B.s-1)+
        (S*B.c-C*B.s)*((33/20)*B.c-(47/20)*B.s)-2*(C+S)=C*dx+S*dy := by
    dsimp [dx,dy]
    linear_combination (3*C+(33/20)*S)*B.unit_normal
  linarith only [expression,linearNonpos]

theorem upper_u_bound (B : OpenSquare) {C S : ℝ}
    (test : |S|≤C) (canonical : |B.s|≤B.c)
    (order : 0≤S*B.c-C*B.s) (side : 1≤B.side)
    (marker : B.Inside (47/20) (33/20))
    (cap : B.loU+B.side≤3*B.c+2*B.s) : lower B C S≤2*(C+S) := by
  let K := C*B.c+S*B.s
  let H := S*B.c-C*B.s
  have cp := le_trans (abs_nonneg S) test
  have product := mul_le_mul test canonical (abs_nonneg B.s) cp
  have absProduct : |S*B.s|≤C*B.c := by simpa only [abs_mul] using product
  have kNonneg : 0≤K := by dsimp [K]; linarith only [(abs_le.mp absProduct).1]
  have hNonneg : 0≤H := order
  have formula : lower B C S=K*B.loU+H*B.loV := by
    rw [lower_in_bands]
    rw [show -C*B.s+S*B.c=H by dsimp [H]; ring]
    change K*(B.loU+B.side/2)+H*(B.loV+B.side/2)-
      B.side/2*(|K|+|H|)=K*B.loU+H*B.loV
    rw [abs_of_nonneg kNonneg,abs_of_nonneg hNonneg]
    ring
  have along := mul_nonneg kNonneg
    (show 0≤3*B.c+2*B.s-1-B.loU by linarith only [cap,side])
  have across := mul_nonneg hNonneg
    (show 0≤(33/20)*B.c-(47/20)*B.s-B.loV by linarith only [marker.2.2.1])
  have bound := margin B test canonical order
  dsimp [K,H] at formula along across
  nlinarith only [formula,along,across,bound]

theorem lower_escape_point (B : OpenSquare) {C S : ℝ}
    (test : |S|≤C) (canonical : |B.s|≤B.c)
    (order : 0≤S*B.c-C*B.s) (side : 1<B.side)
    (marker : B.Inside (47/20) (33/20)) (low : B.Inside 3 (87/50))
    (escape : B.c-3*B.s≤B.loV)
    (incoming : 2*(C+S)<lower B C S) : B.Inside 3 2 := by
  by_contra missing
  have b := normal_bounds B canonical
  have signs := abs_le.mp canonical
  have cap : B.loU+B.side≤3*B.c+2*B.s := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,by linarith only [high],?_,?_⟩ <;>
      nlinarith only [marker.1,low.2.2.1,escape,side,signs.1,b.1,b.2]
  have bound := upper_u_bound B test canonical order side.le marker cap
  linarith only [bound,incoming]

#print axioms upper_u_bound
#print axioms lower_escape_point
end N12Compact.CentralRightIncomingOrdered
