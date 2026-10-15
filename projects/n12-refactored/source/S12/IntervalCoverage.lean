import S12.AngleEnclosure
namespace S12

def CoversInterval (l h : ℚ) : List AngleEnclosure → Prop
  | [] => False
  | w::ws => w.lower≤l ∧ l≤w.upper ∧ (h≤w.upper ∨ CoversInterval w.upper h ws)
instance decidableCoversInterval (l h : ℚ) (ws : List AngleEnclosure) : Decidable (CoversInterval l h ws) := by
  induction ws generalizing l with
  | nil => exact isFalse id
  | cons w ws ih => unfold CoversInterval; infer_instance

theorem coversInterval_sound (ws : List AngleEnclosure) (l h : ℚ) (hc : CoversInterval l h ws)
    (t : ℝ) (ht0 : (l:ℝ)≤t) (ht1 : t≤(h:ℝ)) :
    ∃ w∈ws,(w.lower:ℝ)≤t ∧ t≤(w.upper:ℝ) := by
  induction ws generalizing l with
  | nil => exact hc.elim
  | cons w ws ih =>
    obtain ⟨hlo,_,hh⟩ := hc
    have hlo' : (w.lower:ℝ)≤l := by exact_mod_cast hlo
    by_cases ht : t≤(w.upper:ℝ)
    · exact ⟨w,by simp,le_trans hlo' ht0,ht⟩
    · rcases hh with hh | hh
      · have hhi : (h:ℝ)≤w.upper := by exact_mod_cast hh
        exact False.elim (ht (le_trans ht1 hhi))
      · obtain ⟨v,hv,htv⟩ := ih _ hh (le_of_lt (lt_of_not_ge ht))
        exact ⟨v,by simp [hv],htv⟩

#print axioms coversInterval_sound
end S12
