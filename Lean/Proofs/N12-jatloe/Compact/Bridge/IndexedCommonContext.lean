import Compact.Bridge.IndexedCommonGroups
import Compact.Bridge.HistoricalPoseFanRecipe

/-! A raw fan may be shared by several original poses with the same inputs.
The numeric cache is certified once. Each use still supplies its actual pose
and block, and checks exact input and reference identities for that use. -/

set_option Elab.async false

namespace N12Compact.IndexedCommonGroups
open S12 IntegerSupport IndexedRelaxation

variable {r m a : Nat} {d : Dictionary r m a}

structure FanCache (d : Dictionary r m a) where
  raw : VertexFanTable.RawContext r
  checked : raw.Check d.rows
  numeric : RawSupportFan.Context
  numeric_exact : numeric = (raw.certify d.rows checked).numeric

/-- No canonical raw-fan header is substituted for the actual pruning pose. -/
def FanCache.bind (cache : FanCache d) (header : Header d)
    (inputs_exact : cache.raw.inputs = header.block ++ d.poseRows header.pose)
    (reference_exact : cache.raw.reference =
      HistoricalPoseFanRecipe.reference (d.angles (d.poseAngle header.pose)).val) :
    Context d := .fan {
  pose := header.pose
  block := header.block
  keyAngle := (d.poseAngle header.pose).val
  context := cache.raw.certify d.rows cache.checked
  inputs_exact := inputs_exact
  reference_valid := by
    change cache.raw.reference.Valid
    rw [reference_exact]
    exact HistoricalPoseFanRecipe.reference_valid _
  reference_exact := by
    change cache.raw.reference.value = (d.pose header.pose).angle.val.reference 1
    rw [reference_exact]
    exact HistoricalPoseFanRecipe.reference_exact _
  numeric := cache.numeric
  numeric_exact := cache.numeric_exact
}

@[simp] theorem FanCache.bind_header (cache : FanCache d) (header : Header d)
    (inputs_exact : cache.raw.inputs = header.block ++ d.poseRows header.pose)
    (reference_exact : cache.raw.reference =
      HistoricalPoseFanRecipe.reference (d.angles (d.poseAngle header.pose)).val) :
    (cache.bind header inputs_exact reference_exact).header = header := rfl

#print axioms FanCache.bind
end N12Compact.IndexedCommonGroups
