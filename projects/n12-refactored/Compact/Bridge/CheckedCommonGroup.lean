import Compact.Bridge.IndexedCommonGroups
import Compact.Core.KernelMatrix
import Lean.Elab.Command

/-! One semantic rectangle record emits separate ordinary finite acceptance
facts and one application of the common geometric theorem. Source compression
does not combine the numeric checks or add a computation axiom. -/

namespace N12Compact.CheckedCommonGroup
open Lean Elab Command

syntax (name := checkedPointGroup) "checked_point_group " ident
  "(" term "," term "," term "," term ")" " : " num " × " num
  " in " "(" num "," num "," num "," num ")" " at " term : command

syntax (name := checkedAxisGroup) "checked_axis_group " ident
  "(" term "," term "," term "," term "," term ")" " : " num " × " num
  " in " "(" num "," num "," num "," num ")" : command

elab_rules : command
  | `(checked_point_group $name:ident
      ($sources:term, $neighbors:term, $positive:term, $keys:term) : $u:num × $v:num
      in ($s:num, $sc:num, $n:num, $nc:num) at $point:term) => do
      let scope := mkIdentFrom name (name.getId.appendAfter "_scope")
      let valid := mkIdentFrom name (name.getId.appendAfter "_valid")
      let sourceChecked := mkIdentFrom name (name.getId.appendAfter "_sources_checked")
      let neighborChecked := mkIdentFrom name (name.getId.appendAfter "_neighbors_checked")
      elabCommand (← `(def $scope : N12Compact.IndexedCommonGroups.Scope :=
        ⟨$s, $sc, $n, $nc⟩))
      elabCommand (← `(theorem $valid : ($scope).Valid $u $v := by decide +kernel))
      elabCommand (← `(kernel_matrix $sourceChecked : $sc × 1 =>
        (fun i _ => ($sources (($scope).sourceIndex $valid i)).PointCheck $keys $point)))
      elabCommand (← `(kernel_matrix $neighborChecked : $nc × 1 =>
        (fun j _ => ($neighbors (($scope).neighborIndex $valid j)).PointCheck $keys $point)))
      elabCommand (← `(noncomputable def $name :
          N12Compact.IndexedCommonGroups.CheckedGroup $sources $neighbors :=
        N12Compact.IndexedCommonGroups.pointGroup $sources $neighbors $positive
          $scope $valid $keys $point
          (fun i => $sourceChecked i 0) (fun j => $neighborChecked j 0)))
  | `(checked_axis_group $name:ident
      ($sources:term, $neighbors:term, $positive:term, $keys:term, $opposite:term) :
      $u:num × $v:num in ($s:num, $sc:num, $n:num, $nc:num)) => do
      let scope := mkIdentFrom name (name.getId.appendAfter "_scope")
      let valid := mkIdentFrom name (name.getId.appendAfter "_valid")
      let checked := mkIdentFrom name (name.getId.appendAfter "_pairs_checked")
      elabCommand (← `(def $scope : N12Compact.IndexedCommonGroups.Scope :=
        ⟨$s, $sc, $n, $nc⟩))
      elabCommand (← `(theorem $valid : ($scope).Valid $u $v := by decide +kernel))
      elabCommand (← `(kernel_matrix $checked : $sc × $nc =>
        (fun i j => ($sources (($scope).sourceIndex $valid i)).PairCheck
          ($neighbors (($scope).neighborIndex $valid j)) $keys $opposite)))
      elabCommand (← `(noncomputable def $name :
          N12Compact.IndexedCommonGroups.CheckedGroup $sources $neighbors :=
        N12Compact.IndexedCommonGroups.fallbackGroup $sources $neighbors $positive
          $scope $valid $keys $opposite $checked))

end N12Compact.CheckedCommonGroup
