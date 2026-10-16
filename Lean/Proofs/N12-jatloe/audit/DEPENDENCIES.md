# Separating geometry from finite marker classification

Audit date: 2026-10-10. Source assembled only; no compiler was run for this change.

## Reason and scope

The original `S12.Markers` module executed `computedGroups_eq` with `decide +kernel` whenever any geometric descendant was compiled. The root worker reported that this finite clique calculation reached the 1.2 GiB worker memory bound while preparing basic geometry. This split removes that computation from the core geometry import path; it does not claim to make the full classification proof cheaper or to close it.

`vendor/` remains immutable. All 119 Lean sources (1,179,049 bytes) were authenticated against `evidence/imported-source.json` before being copied to the `source/` overlay. Of those copies, 116 remain byte-identical; only `Markers`, `Diameter`, and the import of `Packing` changed. Three modules were added. The original `vendor/S12.lean` root is also copied unchanged to `source/S12.lean`.

## Preserved declarations and proofs

| Declaration | Original module | New module | Preservation |
|---|---|---|---|
| `S12.computedGroups` | `S12.Markers` | `S12.MarkerClassification` | Definition body copied byte-for-byte. |
| `S12.computedGroups_eq` | `S12.Markers` | `S12.MarkerClassification` | Statement unchanged; now uses proved D4 row normalization and an integer-mask kernel check. Original proof remains in immutable vendor. |
| `S12.groupTable_card` | `S12.Markers` | `S12.MarkerClassification` | Original `decide` proof copied byte-for-byte. |
| `S12.diameter_group_in_table` | `S12.Markers` | `S12.MarkerClassification` | Original proof copied byte-for-byte. |
| `S12.actual_group_in_table` | `S12.Diameter` | `S12.DiameterClassification` | Original proof copied byte-for-byte. |

All original marker coordinates, `Marker`, `diameterLimit`, `distSq`, `DiameterOK`, `groupList`, `groupTable`, `markerCompatible`, instances, `OpenSquare`, `Inside`, `Owns`, geometric diameter lemmas, and packing structures/statements are unchanged. Names remain in the same `S12` namespace. No axiom, admission, `native_decide`, or altered theorem hypothesis was introduced.

## Import audit

- `S12.Markers` no longer imports `S12.Cliques`; its definitions do not use it after `computedGroups` moves.
- `S12.MarkerClassification` explicitly imports `S12.Markers`, `S12.Cliques`, and the new `S12.MarkerAdjacency`.
- `S12.DiameterClassification` explicitly imports `S12.Diameter` and `S12.MarkerClassification`.
- `S12.Packing` imports `S12.DiameterClassification`, preserving its use of `actual_group_in_table`.
- All occurrences of the five moved declarations were checked across the entire overlay and the other current Lean source directories. Each reference retains the appropriate declaration in its transitive imports.
- Core geometry paths through `S12.Diameter`, `S12.ShortCluster`, `S12.TriangleCover`, and `S12.CornerCover` contain neither classification module nor the expensive equality proof.
- Full `S12.Packing` and `S12.PackingConstant` paths still reach both classification modules and `S12.MarkerAdjacency`; their mathematical obligations have not disappeared.
- `S12.CurrentReduction` had missing historical case source imports before this change. Its missing-import set remains identical after the change; this source split does not complete that pre-existing incomplete checkout.

| Entry point | Before local S12 closure | After local S12 closure | Classification computation |
|---|---:|---:|---|
| `S12.Markers` | 3 | 2 | Removed from this dependency path. |
| `S12.Diameter` | 4 | 3 | Removed from this dependency path. |
| `S12.ShortCluster` | 5 | 4 | Removed from this dependency path. |
| `S12.TriangleCover` | 6 | 5 | Removed from this dependency path. |
| `S12.CornerCover` | 9 | 8 | Removed from this dependency path. |
| `S12.Packing` | 6 | 9 | Preserved, through the two new modules. |
| `S12.PackingConstant` | 62 | 65 | Preserved, through the two new modules. |

Counts exclude Mathlib and other libraries. This is an import/source audit, not Lean elaboration evidence. C977 helper files explicitly importing `S12.Packing` still reach classification until their import boundaries are separately refactored.

## D4 reduction of classification evaluation

A second change reduces repeated rational work inside the preserved finite
classification. The square symmetries give three marker orbits, represented
by markers 0, 8, and 12. Their exact compatibility rows are the integer masks
12547, 16131, and 6595, including their diagonal entries. The fast relation
transports the second marker through the same rotation/reflection that takes
the first marker to its orbit representative.

`MarkerAdjacency.lean` proves the geometric rotation and transpose identities,
compatibility invariance, the three representative rows, and
`markerCompatible_iff_fast`. There are 32 coordinate-identity cases, 48
representative-row rational comparisons, and 16 orbit cases: 96 small cases,
instead of a fresh 256-entry rational comparison table. The orbit transport
is symbolic; no matrix equality or native evaluator is assumed.

`cliques_relation_congr` proves that pointwise equivalent relations produce
exactly the same clique list, independently of decidability implementations.
The original `computedGroups` definition and equality statement are unchanged;
its proof now transports the list to `fastMarkerCompatible` before invoking
`decide +kernel`. Thus repeated rational squared-distance comparisons are
absent from that closed kernel computation. This leaves the original clique
enumeration itself in place. Actual time/RSS improvement is **not yet measured**.

The two new/changed classification modules total 218 lines. A tiny independent
Python exact-rational sanity check confirmed all 256 compatibility pairs and
that fast clique enumeration gives exactly the original 103 nonempty groups.
That check is supplementary evidence, not Lean proof acceptance. No compiler
was run by the author of this refactor.

## SHA256 provenance

| Source | Vendor SHA256 | Overlay SHA256 |
|---|---|---|
| `S12/Markers.lean` | `f5983312697b11014b9d328d0978f8cb49334fbffb78c6c4a35f0814485a6e7b` | `77fb03343863564fc98fb1ee9a82d6154c89bd42bc448708b1050ff3fc960c1e` |
| `S12/Diameter.lean` | `9c4caa1a18260c48e910251d0b003f59ad81bfc41fedad0d5ab8933c191e910f` | `8ee3fcaa8bea000bcdcf6ffdeb39435b2eaae2c611a095c1bc1f906221ed47ae` |
| `S12/Packing.lean` | `667a8183490baa10a5001a7918e59ff132a67254768f144a4f2db8493fd4f5e0` | `3278b8f219615ba4733b33d982ee22b8131994732e6666c394167927fc6987c1` |
| `S12/MarkerClassification.lean` | `new module` | `d793ffa8d8cfd31ae525093faeb7e75ea30d2a5154f68bd4962af755b8543aaa` |
| `S12/DiameterClassification.lean` | `new module` | `be071cb22eeac5fee2d77badcc61c758a689301af6a67bbfc5e22e452610cd53` |
| `S12/MarkerAdjacency.lean` | `new module` | `5fad8b0d1b2e3743cdca5e7e2b14704e4dbc26df702ba27e2d5ef9d649e979c9` |

The original 119 vendor files remain unchanged. All moved definition/proof
blocks except the deliberately optimized `computedGroups_eq` proof remain
verbatim in their destination modules. The original equality proof remains
preserved in `vendor/S12/Markers.lean`; its theorem is neither dropped nor
weakened in the overlay.

## Exact source diff

```diff
--- vendor/S12/Markers.lean
+++ source/S12/Markers.lean
@@ -1,5 +1,4 @@
 import S12.Diagonal
-import S12.Cliques
 import Mathlib.Data.Finset.Powerset
 import Mathlib.Order.Fin.Basic
 import Mathlib.Tactic.FinCases
@@ -35,22 +34,4 @@
 def markerCompatible (i j : Marker) : Prop :=
   distSq (marker i) (marker j) < diameterLimit
 instance : DecidableRel markerCompatible := fun _ _ => inferInstanceAs (Decidable (_ < _))
-def computedGroups : Finset (Finset Marker) :=
-  ((cliques markerCompatible (List.finRange 16)).filter fun g => decide g.Nonempty).toFinset
-
-set_option maxRecDepth 100000
-set_option maxHeartbeats 0
-theorem computedGroups_eq : computedGroups = groupTable := by decide +kernel
-
-theorem groupTable_card : groupTable.card = 103 := by decide
-
-theorem diameter_group_in_table (g : Finset Marker) (h : DiameterOK g) :
-    g ∈ groupTable := by
-  rw [← computedGroups_eq]
-  apply List.mem_toFinset.mpr
-  apply List.mem_filter.mpr
-  refine ⟨cliques_complete markerCompatible (List.finRange 16) g (by simp) h.2, ?_⟩
-  exact decide_eq_true h.1
-
-#print axioms diameter_group_in_table
 end S12
--- vendor/S12/Diameter.lean
+++ source/S12/Diameter.lean
@@ -34,18 +34,6 @@
 def Owns (q : OpenSquare) (i : Marker) : Prop :=
   q.Inside (marker i).1 (marker i).2

-theorem actual_group_in_table (q : OpenSquare) (hsize : q.side ≤ 1001/1000)
-    (g : Finset Marker) (hne : g.Nonempty)
-    (howned : ∀ i ∈ g, Owns q i) : g ∈ groupTable := by
-  apply diameter_group_in_table
-  refine ⟨hne, ?_⟩
-  intro i hi j hj
-  have hd := normalized_diameter_bound q hsize _ _ _ _ (howned i hi) (howned j hj)
-  unfold distSq diameterLimit
-  apply (Rat.cast_lt (K := ℝ)).mp
-  push_cast
-  exact hd

 #print axioms inside_distance_bound
-#print axioms actual_group_in_table
 end S12
--- vendor/S12/Packing.lean
+++ source/S12/Packing.lean
@@ -1,4 +1,4 @@
-import S12.Diameter
+import S12.DiameterClassification
 import S12.Enumeration

 namespace S12
--- /dev/null
+++ source/S12/MarkerClassification.lean
@@ -0,0 +1,58 @@
+import S12.Markers
+import S12.Cliques
+import S12.MarkerAdjacency
+
+/-! Original finite marker classification, separated from geometric definitions.
+The theorem statements are preserved. A proved D4 normalization replaces
+repeated rational distance evaluation inside the finite kernel check. -/
+namespace S12
+
+def computedGroups : Finset (Finset Marker) :=
+  ((cliques markerCompatible (List.finRange 16)).filter fun g => decide g.Nonempty).toFinset
+
+set_option maxRecDepth 100000
+set_option maxHeartbeats 0
+
+/-- Extensional change of a clique relation preserves the enumerated list,
+independently of the chosen decidability implementations. -/
+theorem cliques_relation_congr {M : Type} [DecidableEq M]
+    (r s : M → M → Prop) [DecidableRel r] [DecidableRel s]
+    (h : ∀ i j, r i j ↔ s i j) (vs : List M) :
+    cliques r vs = cliques s vs := by
+  induction vs with
+  | nil => rfl
+  | cons i vs ih =>
+      have hp : (fun g : Finset M => decide (∀ j ∈ g, r i j)) =
+          (fun g : Finset M => decide (∀ j ∈ g, s i j)) := by
+        funext g
+        have he : (∀ j ∈ g, r i j) ↔ (∀ j ∈ g, s i j) := by
+          constructor
+          · intro hr j hj
+            exact (h i j).mp (hr j hj)
+          · intro hs j hj
+            exact (h i j).mpr (hs j hj)
+        by_cases hr : ∀ j ∈ g, r i j
+        · have hs := he.mp hr
+          simp [hr, hs]
+        · have hs : ¬ (∀ j ∈ g, s i j) := fun hs => hr (he.mpr hs)
+          simp [hr, hs]
+      simp only [cliques, ih, hp]
+
+theorem computedGroups_eq : computedGroups = groupTable := by
+  unfold computedGroups
+  rw [cliques_relation_congr markerCompatible fastMarkerCompatible
+    markerCompatible_iff_fast (List.finRange 16)]
+  decide +kernel
+
+theorem groupTable_card : groupTable.card = 103 := by decide
+
+theorem diameter_group_in_table (g : Finset Marker) (h : DiameterOK g) :
+    g ∈ groupTable := by
+  rw [← computedGroups_eq]
+  apply List.mem_toFinset.mpr
+  apply List.mem_filter.mpr
+  refine ⟨cliques_complete markerCompatible (List.finRange 16) g (by simp) h.2, ?_⟩
+  exact decide_eq_true h.1
+
+#print axioms diameter_group_in_table
+end S12
--- /dev/null
+++ source/S12/DiameterClassification.lean
@@ -0,0 +1,21 @@
+import S12.Diameter
+import S12.MarkerClassification
+
+/-! Original bridge from geometric ownership to the finite marker table. -/
+namespace S12
+open S12Pilot
+
+theorem actual_group_in_table (q : OpenSquare) (hsize : q.side ≤ 1001/1000)
+    (g : Finset Marker) (hne : g.Nonempty)
+    (howned : ∀ i ∈ g, Owns q i) : g ∈ groupTable := by
+  apply diameter_group_in_table
+  refine ⟨hne, ?_⟩
+  intro i hi j hj
+  have hd := normalized_diameter_bound q hsize _ _ _ _ (howned i hi) (howned j hj)
+  unfold distSq diameterLimit
+  apply (Rat.cast_lt (K := ℝ)).mp
+  push_cast
+  exact hd
+
+#print axioms actual_group_in_table
+end S12
--- /dev/null
+++ source/S12/MarkerAdjacency.lean
@@ -0,0 +1,160 @@
+import S12.Markers
+
+/-!
+Exact fast marker compatibility, factored through the three D4 orbits.
+Only representatives 0, 8, and 12 need rational-distance normalization.
+All original coordinates and compatibility definitions remain unchanged.
+This is kernel-checkable source; no native evaluation is introduced.
+-/
+
+namespace S12
+
+def rotateMarker (i : Marker) : Marker :=
+  match i.val with
+  | 0 => 3 | 1 => 2 | 2 => 5 | 3 => 4
+  | 4 => 7 | 5 => 6 | 6 => 1 | 7 => 0
+  | 8 => 9 | 9 => 10 | 10 => 11 | 11 => 8
+  | 12 => 13 | 13 => 14 | 14 => 15 | _ => 12
+
+def transposeMarker (i : Marker) : Marker :=
+  match i.val with
+  | 0 => 1 | 1 => 0 | 2 => 7 | 3 => 6
+  | 4 => 5 | 5 => 4 | 6 => 3 | 7 => 2
+  | 8 => 8 | 9 => 11 | 10 => 10 | 11 => 9
+  | 12 => 13 | 13 => 12 | 14 => 15 | _ => 14
+
+def rotateMarker2 (i : Marker) : Marker := rotateMarker (rotateMarker i)
+def rotateMarker3 (i : Marker) : Marker := rotateMarker (rotateMarker2 i)
+def transposeRotateMarker (i : Marker) : Marker := transposeMarker (rotateMarker i)
+def transposeRotateMarker2 (i : Marker) : Marker := transposeMarker (rotateMarker2 i)
+def transposeRotateMarker3 (i : Marker) : Marker := transposeMarker (rotateMarker3 i)
+
+theorem marker_rotate (i : Marker) :
+    marker (rotateMarker i) = (4 - (marker i).2, (marker i).1) := by
+  fin_cases i <;> norm_num [rotateMarker, marker]
+
+theorem marker_transpose (i : Marker) :
+    marker (transposeMarker i) = ((marker i).2, (marker i).1) := by
+  fin_cases i <;> norm_num [transposeMarker, marker]
+
+theorem markerCompatible_rotate (i j : Marker) :
+    markerCompatible (rotateMarker i) (rotateMarker j) ↔ markerCompatible i j := by
+  unfold markerCompatible
+  rw [marker_rotate, marker_rotate]
+  rw [show distSq (4 - (marker i).2, (marker i).1)
+      (4 - (marker j).2, (marker j).1) = distSq (marker i) (marker j) by
+        unfold distSq
+        ring]
+
+theorem markerCompatible_transpose (i j : Marker) :
+    markerCompatible (transposeMarker i) (transposeMarker j) ↔ markerCompatible i j := by
+  unfold markerCompatible
+  rw [marker_transpose, marker_transpose]
+  rw [show distSq ((marker i).2, (marker i).1)
+      ((marker j).2, (marker j).1) = distSq (marker i) (marker j) by
+        unfold distSq
+        ring]
+
+theorem markerCompatible_rotate2 (i j : Marker) :
+    markerCompatible (rotateMarker2 i) (rotateMarker2 j) ↔ markerCompatible i j :=
+  (markerCompatible_rotate (rotateMarker i) (rotateMarker j)).trans
+    (markerCompatible_rotate i j)
+
+theorem markerCompatible_rotate3 (i j : Marker) :
+    markerCompatible (rotateMarker3 i) (rotateMarker3 j) ↔ markerCompatible i j :=
+  (markerCompatible_rotate (rotateMarker2 i) (rotateMarker2 j)).trans
+    (markerCompatible_rotate2 i j)
+
+theorem markerCompatible_transposeRotate (i j : Marker) :
+    markerCompatible (transposeRotateMarker i) (transposeRotateMarker j) ↔
+      markerCompatible i j :=
+  (markerCompatible_transpose (rotateMarker i) (rotateMarker j)).trans
+    (markerCompatible_rotate i j)
+
+theorem markerCompatible_transposeRotate2 (i j : Marker) :
+    markerCompatible (transposeRotateMarker2 i) (transposeRotateMarker2 j) ↔
+      markerCompatible i j :=
+  (markerCompatible_transpose (rotateMarker2 i) (rotateMarker2 j)).trans
+    (markerCompatible_rotate2 i j)
+
+theorem markerCompatible_transposeRotate3 (i j : Marker) :
+    markerCompatible (transposeRotateMarker3 i) (transposeRotateMarker3 j) ↔
+      markerCompatible i j :=
+  (markerCompatible_transpose (rotateMarker3 i) (rotateMarker3 j)).trans
+    (markerCompatible_rotate3 i j)
+
+/- Each representative row needs only sixteen exact rational comparisons.
+The three masks include their diagonal/self entries, as the original
+strict-diameter relation does. -/
+theorem markerCompatible_row0 (j : Marker) :
+    markerCompatible 0 j ↔ (12547 : Nat).testBit j.val = true := by
+  fin_cases j <;> norm_num [markerCompatible, marker, distSq, diameterLimit] <;> decide
+
+theorem markerCompatible_row8 (j : Marker) :
+    markerCompatible 8 j ↔ (16131 : Nat).testBit j.val = true := by
+  fin_cases j <;> norm_num [markerCompatible, marker, distSq, diameterLimit] <;> decide
+
+theorem markerCompatible_row12 (j : Marker) :
+    markerCompatible 12 j ↔ (6595 : Nat).testBit j.val = true := by
+  fin_cases j <;> norm_num [markerCompatible, marker, distSq, diameterLimit] <;> decide
+
+/-- Each row is a canonical integer row evaluated at an isometric column.
+This avoids recomputing rational squared distances during clique checking. -/
+def fastCompatibility (i j : Marker) : Bool :=
+  match i.val with
+  | 0 => (12547 : Nat).testBit j.val
+  | 1 => (12547 : Nat).testBit (transposeMarker j).val
+  | 2 => (12547 : Nat).testBit (transposeRotateMarker3 j).val
+  | 3 => (12547 : Nat).testBit (rotateMarker3 j).val
+  | 4 => (12547 : Nat).testBit (rotateMarker2 j).val
+  | 5 => (12547 : Nat).testBit (transposeRotateMarker2 j).val
+  | 6 => (12547 : Nat).testBit (transposeRotateMarker j).val
+  | 7 => (12547 : Nat).testBit (rotateMarker j).val
+  | 8 => (16131 : Nat).testBit j.val
+  | 9 => (16131 : Nat).testBit (rotateMarker3 j).val
+  | 10 => (16131 : Nat).testBit (rotateMarker2 j).val
+  | 11 => (16131 : Nat).testBit (rotateMarker j).val
+  | 12 => (6595 : Nat).testBit j.val
+  | 13 => (6595 : Nat).testBit (rotateMarker3 j).val
+  | 14 => (6595 : Nat).testBit (rotateMarker2 j).val
+  | _ => (6595 : Nat).testBit (rotateMarker j).val
+
+def fastMarkerCompatible (i j : Marker) : Prop := fastCompatibility i j = true
+
+instance : DecidableRel fastMarkerCompatible :=
+  fun _ _ => inferInstanceAs (Decidable (_ = _))
+
+theorem markerCompatible_iff_fast (i j : Marker) :
+    markerCompatible i j ↔ fastMarkerCompatible i j := by
+  fin_cases i
+  · exact markerCompatible_row0 j
+  · exact (markerCompatible_transpose 1 j).symm.trans
+      (markerCompatible_row0 (transposeMarker j))
+  · exact (markerCompatible_transposeRotate3 2 j).symm.trans
+      (markerCompatible_row0 (transposeRotateMarker3 j))
+  · exact (markerCompatible_rotate3 3 j).symm.trans
+      (markerCompatible_row0 (rotateMarker3 j))
+  · exact (markerCompatible_rotate2 4 j).symm.trans
+      (markerCompatible_row0 (rotateMarker2 j))
+  · exact (markerCompatible_transposeRotate2 5 j).symm.trans
+      (markerCompatible_row0 (transposeRotateMarker2 j))
+  · exact (markerCompatible_transposeRotate 6 j).symm.trans
+      (markerCompatible_row0 (transposeRotateMarker j))
+  · exact (markerCompatible_rotate 7 j).symm.trans
+      (markerCompatible_row0 (rotateMarker j))
+  · exact markerCompatible_row8 j
+  · exact (markerCompatible_rotate3 9 j).symm.trans
+      (markerCompatible_row8 (rotateMarker3 j))
+  · exact (markerCompatible_rotate2 10 j).symm.trans
+      (markerCompatible_row8 (rotateMarker2 j))
+  · exact (markerCompatible_rotate 11 j).symm.trans
+      (markerCompatible_row8 (rotateMarker j))
+  · exact markerCompatible_row12 j
+  · exact (markerCompatible_rotate3 13 j).symm.trans
+      (markerCompatible_row12 (rotateMarker3 j))
+  · exact (markerCompatible_rotate2 14 j).symm.trans
+      (markerCompatible_row12 (rotateMarker2 j))
+  · exact (markerCompatible_rotate 15 j).symm.trans
+      (markerCompatible_row12 (rotateMarker j))
+
+end S12
```


## Second extraction: basic square frames and container symmetries

Source assembled 10 October 2026, 20:35 EDT. No Lean invocation was run by this worker. The root worker reported roughly 82 seconds for `ShortCluster` and more than 30 seconds for `WallRowCover` while preparing basic actual-square geometry. Those proofs should remain in the complete classification, but center/containment lemmas do not need them.

Three modules now expose exactly the original definitions and proof bodies:

| New module | Original declarations moved verbatim | Imports |
|---|---|---|
| `S12.SquareFrame` | `centerX`, `centerY`, `center_coordinates`, `relativeU`, `relativeV`, `relative_inside_iff` from `TriangleCover`, and `inside_centered_iff` from `CornerCover`. | `S12.Diagonal` only. |
| `S12.SymmetryBase` | `pullX`, `pullY`, `pullSwap`, their Inside equivalences, `Transform`, `Transform.apply`, `Transform.pull`, `pull_same_side`, `inside_pull` from `Symmetry`. | `S12.Diagonal` only. |
| `S12.Container` | `InsideContainer`, three `container_pull*` lemmas and six `center_pull*` lemmas from `MarkerCoverGeometry`. | `S12.SquareFrame`, `S12.SymmetryBase`. |

The extra `SymmetryBase` split is necessary: original `Symmetry` also contains `five_point_transformed` and `six_point_transformed`, which require `ShortCluster`. Importing the original unsplit `Symmetry` from `Container` would therefore defeat the requested dependency reduction. Those two template theorems remain in `Symmetry` with their original bodies; it now imports both `SymmetryBase` and `ShortCluster`.

`TriangleCover` imports `SquareFrame` plus `ShortCluster` and retains its complete triangle proof. `WallGeometry` imports `SquareFrame` instead of `TriangleCover`. `CornerCover` retains its original `WallGeometry` and `Symmetry` imports, with only `inside_centered_iff` relocated. `MarkerCoverGeometry` imports `Container` and the original `MarkerCoverGeometryBase`, retaining its center-shift and complete region-cover proofs. The base module gains a direct `TriangleCover` import: its four triangle applications had previously inherited that theorem indirectly through `WallGeometry`. Without that explicit preservation, the otherwise small refactor would break the global marker proof.

| Entry point | Earlier local closure | New local closure | Expensive marker-cover/classification proofs in new closure |
|---|---:|---:|---|
| `S12.SquareFrame` | Definitions formerly reached through triangle/corner proofs. | 2 modules | None. |
| `S12.WallGeometry` | 6 modules | 3 modules | None. |
| `S12.SymmetryBase` | Definitions formerly reached through `Symmetry`/`ShortCluster`. | 2 modules | None. |
| `S12.Container` | Definitions formerly reached through 11-module `MarkerCoverGeometry`. | 4 modules | None. |
| `S12.MarkerCoverGeometry` | 11 modules | 14 modules | ShortCluster and WallRowCover retained. |
| `S12.PackingConstant` | 65 modules at this extraction's overlay snapshot | 68 modules | Full classification and coverage retained. |

Counts are local import-graph counts, excluding Mathlib. The before column undoes only this extraction against the concurrent overlay, so it need not match an earlier snapshot's full-project count. This edit increases the full proof by three small modules, while avoiding unrelated large tactic proofs in the core geometry build. It changes neither the global mathematical obligation nor its accepted status.

A source-only reference scan checked 205 references to moved/formerly transitive declarations. All restored S12 overlay references retain their definitions. One Compact match was comment text, and the two pre-existing inactive adapters import absent case-specific modules; they remain explicitly outside the accepted closure. This scan is not elaboration evidence. `audit/geometry-dependency-closures.json` records full details.

All four extracted text blocks were checked byte-for-byte in their destination modules, and all 119 immutable vendor files were rehashed after the edit and unchanged. No theorem body, statement, namespace, axiom, native site or admission was changed. `audit/geometry-dependency-extraction.diff` is the full source diff; `audit/geometry-dependency-extraction.json` preserves before/after and extracted-block hashes.

| Overlay file | SHA-256 after extraction |
|---|---|
| `source/S12/SquareFrame.lean` | `49e1855ce4de71f8a0791f6c2b57c5af88c2fa9102e5324fc67ddfd80f0341f6` |
| `source/S12/TriangleCover.lean` | `591ef2530815cea9c499e0c84d0ae6dfff4254616bfac4c19355eecbaea0377a` |
| `source/S12/WallGeometry.lean` | `a803ce2d86bc423f74007e0ea036eea0deaa785facb2b25c6698160500e4558e` |
| `source/S12/CornerCover.lean` | `e3210052f7175c66c86b454b67dc99e08db40d85d8552241eb6e09cea9284a17` |
| `source/S12/SymmetryBase.lean` | `649d5ae978e0f8733ab32c512ebf081c7d5b9c577b6ad25971df959a8600fdb1` |
| `source/S12/Symmetry.lean` | `8a5651289837924c73b854dac4781dab8e0d9ceece4df3aef5b386bcfbb57806` |
| `source/S12/Container.lean` | `645387a0b344970b27864bfc72160b8e65ae9f574087ac17d277cf15cd2acb15` |
| `source/S12/MarkerCoverGeometry.lean` | `a11458ac6976c1005cc6d9d6474e293bbfbccbcc9f6b5a0e13292a2428b615e9` |
| `source/S12/MarkerCoverGeometryBase.lean` | `403de00f55936383399e1982d37ebb2d99ee2b3d14c8321b802725e73aa3cf97` |


## Cached clique recursion: bounded proof boundaries

The subsequent root-worker replay established `MarkerAdjacency.lean` in about
3.7 seconds, but the unsplit classification check still exceeded its resource
guard. The receipt `.verification/terminal-resources.json` records 63.586 seconds,
1,539,664 KiB peak aggregate RSS, termination for `aggregate_rss_limit`, and
complete process cleanup. Thus replacing rational comparisons alone did not
solve the recursive classification cost.

The next source revision adds `MarkerCliques.lean`. It records the ordinary
finite clique list for each of the 17 suffixes of the 16-marker list, including
the empty suffix. Each theorem unfolds exactly one `cliques` recursion step,
rewrites the recursive call with the already-proved suffix theorem, and checks
only that closed step with `decide +kernel`. The new cached lists contain
104, 92, 86, 74, 68, 56, 50, 38, 32, 20, 13, 8, 5, 4, 3, 2, and 1 entries,
respectively: 656 entries total, including the empty clique in each suffix.
These are 212 lines / 11,054 bytes of source, rather than new case files.

`computedGroups_eq` retains its original statement and definition. Its proof
now rewrites the full fast clique list through `markerCliques0_correct` before
comparing the 103 nonempty entries with the unchanged original group table.
The three classification helper/target modules total 434 lines. This revision
introduces 17 cached recursion boundaries, not 104 separate geometric cases.
No native evaluator, axiom, admission, theorem assumption, or marker coordinate
was added or changed. The literal tables are proof inputs; they are trusted
only after their Lean equalities pass.

The cached suffix revision is **source-only and awaiting the root worker's
bounded validation**. In particular the final nonempty-list/group-table
comparison may need its own smaller proof boundaries if its kernel check
remains expensive. The earlier exact diff above describes the preceding
revision; `audit/marker-cached-cliques.diff` records this revision's two complete
source files against immutable vendor (both are new modules there).

| Source at cached revision | SHA-256 |
|---|---|
| `source/S12/MarkerCliques.lean` | `d5e3c852c53a59b35cb0412b7b2b1f07fb420f0b1563ace83b875e0df81e5c10` |
| `source/S12/MarkerClassification.lean` | `6b2d4105f3f7aecfaaa71450133382b3884470b6b55cdccdb41b56b5d10a4389` |


## Cached recursion validation update

The root worker's bounded replay now passed `S12.MarkerCliques` in 13.964 seconds,
with source SHA-256 `316e12fe872939e0370ba6b0ed387aa616b6ab1c832e0019bcf01f5c3fec9109`.
This is recorded in `.verification/checked-modules.json`. It validates all 17
cached suffix equalities. The accepted source disables asynchronous theorem
elaboration and uses ordinary `decide`, whose generated proofs are checked by
the kernel; it does not use `native_decide`.

The subsequent final table comparison in `MarkerClassification` still hit the
memory guard using `decide +kernel`. That module has now likewise been changed
to ordinary `decide` with asynchronous elaboration disabled; its new replay is
pending. No claim of full classification acceptance is made yet. The earlier
cached-revision hashes/diff are historical; the current source diff is in
`audit/marker-cached-cliques.diff`.


## Integer-mask table comparison and cardinality revision

The final blanket equality check between the two 103-element finite sets of
finite sets exceeded both the 1.4 GiB guard and a single bounded 2 GiB probe.
The accepted suffix module remains unchanged. `MarkerClassification.lean` now
represents each group by a sixteen-bit natural number for the table comparison:
corresponding group lists are identified with decoded mask lists by `rfl`,
finite-set equality is checked only for the natural-number masks, and a general
membership argument transports that equality back to the original groups.
The original `computedGroups` and `groupTable` definitions are unchanged.

The original `groupTable_card` *statement* is also preserved, but its proof is
now deliberately changed from the historical blanket `decide`: a direct list
identity encodes the original groups by their membership bits, `Nodup` is
checked for the resulting natural-number list and transported back through
its map, and `List.toFinset_card_of_nodup` gives the cardinality. This avoids
asking the evaluator to deduplicate 103 nested finite sets.

The latest revision removes every temporary evaluator/trace checkpoint. An
import-only probe passed in 0.825 seconds, with 1,182,752 KiB peak aggregate RSS.
It does not validate the table proof. Three temporary prefix modules under
`Compact/Diagnostics/ClassificationPrefix{1,2,3}.lean` are prepared for bounded
serial diagnosis of (1) relation congruence, (2) decoded-list identities,
(3) mask equality and Nodup. They are diagnostic copies, not new final proof
obligations, and the root worker will remove them after diagnosis.

At this revision the final classification is still awaiting successful
bounded replay. No additional native site, axiom, admission or changed theorem
hypothesis has been introduced. The current classification source hash is
`3d00882cd9c914f01c0d464192d68954aea7267e968d0047aba9e5c6fba36f2a`.


## Structural sorting replaces the remaining quadratic table check

The root worker validated the relation-congruence and corresponding-group
list identities in separate temporary prefixes (2.557 and 2.728 seconds).
The latter are direct definitional equalities (`rfl`), avoiding any pairwise
finite-set equality decision. The remaining mask-level finite-set comparison
was replaced mathematically: sort the two natural-number lists, check equal
sorted lists, and transport membership through a proved sorting permutation.

Core `List.mergeSort` blocked the ordinary reducer because of its well-founded
implementation. The final source uses Mathlib's structurally recursive
`List.insertionSort` and `List.perm_insertionSort` instead. No runtime
replacement or native result is assumed. Distinctness follows from strict
adjacency of the sorted list via `List.chain'_iff_pairwise` and
`List.Pairwise.nodup`; the cardinality proof therefore does not deduplicate
nested finite sets or perform a quadratic Nodup decision.

The two input mask lists have 103 distinct integers each and equal sorted
lists (also checked independently in exact Python integer arithmetic).
The accepted equality of the original group lists to their mask decodings,
together with the sorting proof, preserves the original table exactly.
The original `computedGroups` definition was rechecked byte-for-byte and is
unchanged. At this audit update the structural-sorting revision still awaits
its root-worker bounded replay. Current classification source SHA-256:
`499c24d0bbc7c574c62cd677d2aff6d1aa4be3d568f2090266116d69c4c5c367`.


## Accepted final classification replay

The structural-sorting revision **passed Lean**. The current
`S12.MarkerClassification` source (`499c24d0bbc7c574c62cd677d2aff6d1aa4be3d568f2090266116d69c4c5c367`)
was accepted in 5.457 seconds, recorded in
`.verification/checked-modules.json`. The enclosing bounded replay also passed;
`.verification/classification-insertion-resources.json` records peak aggregate
RSS 1,348,912 KiB, no stop reason, and no remaining processes.
The final printed axiom list for `S12.diameter_group_in_table` is exactly
`[propext, Classical.choice, Quot.sound]`; no native evaluator axiom or admission
appears.

This resolves the original marker-classification compilation bottleneck while
preserving `computedGroups`, all marker/group coordinates, and the original
classification/cardinality theorem statements. Together with the accepted
D4 adjacency and cached suffix modules, it is a checked finite classification.
It is not the global n=12 packing theorem: case exclusions and other obligations
listed elsewhere in the audit remain open. Earlier paragraphs above record
superseded failed revisions; this is the accepted final status for this task.

## Singleton-triangle source simplification (pending focused replay)

`source/S12/SingletonTriangles.lean` preserves all 78 public declaration signatures and every original coordinate definition (compared with immutable `vendor/S12/SingletonTriangles.lean`). Source shrank from 880 to 511 lines. The input overlay already had pruned 7–17-leaf linear trees, rather than a literal 729-leaf full Cartesian expansion.

The replacement now proves one geometric fact: a center in `[457/500,2]²` whose square contains no marker other than marker zero lies strictly below both rays from `(33/20,33/20)` to `(457/500,1)` and `(2,457/500)`. Six regions suffice to prove this using the existing four triangle nonavoidance theorems. Each required replacement point then follows from one split between its two adjacent triangles. Eight identical triangle-hit lemmas reuse existing proofs. All six replacement theorem statements remain unchanged. `Elab.async false` prevents concurrent elaboration in this module.

This is a source-only rewrite until the parent’s bounded replay accepts it; no compiler or search was launched by this worker.

### Focused triangle replay accepted

The parent reports `S12.SingletonTriangles` passed in 29.028 seconds under the existing memory guard. This accepts the new shared localization and all six original replacement conclusions.

## Four-point list assembly simplification (pending focused replay)

`source/S12/FourPointData.lean` retains every literal datum and all 111 historical `native_decide` proof lines byte-for-byte. Its final `fourPointData_checked` statement is unchanged. The former 111-way membership split with a 111-candidate first-success tactic search is replaced by one inductive list-membership cons lemma, composing each already-checked theorem exactly once. `Elab.async false` serializes elaboration within the file. No additional native checks, imports, or modules were introduced.

The worker ran only a source-preservation comparison; compilation remains the parent's bounded check.

### Focused four-point replay accepted

`S12.FourPointData` passed the parent's bounded replay in 24.830 seconds. Its source SHA-256 is `62a9e8f4c7495342b9c600893683f9994b14e7d86ac8a1415c1753eec228301b`, recorded in `.verification/checked-modules.json`. The 111 historical native checks are retained; the change removes repeated theorem search in their final assembly.

## Elementary separating-axis theorem for unequal squares

The new `Compact/Geometry/ScalarSATGeneral.lean` proves interior overlap from strict overlap in the four edge directions, for independently positive half-side lengths `a` and `b` and arbitrary signed relative frame coefficients `c,s` with `c²+s²=1`. Its projection bounds are exactly `|X|,|Y| < a+b*(|c|+|s|)` and `|U|,|V| < b+a*(|c|+|s|)`. Its conclusion supplies the actual common interior coordinates, not a separating-axis premise assumed by a wrapper.

The proof is two applications of a small open-interval intersection lemma, with explicit zero-coordinate and reflection cases. It is 198 Lean lines and introduces no new native proof, axiom, or admission. The module passed in 4.772 seconds; SHA-256 `05ada5563f2793928975c0a1c00fbbec04a7ec1e4d4ac5dd1b482b0585cf6372`.

The parent integrated this theorem into the original `S12.SquareAxes` interface and isolated the elementary geometric support facts in `S12.SquareSupportBase`. These passed in 1.914 and 4.627 seconds respectively. This removes the heavyweight Hahn–Banach separation dependency from the new default geometry path while preserving the original arbitrary-side-length, arbitrary-angle, and boundary-touching separating-axis statement. The historical separation module remains available in the immutable source; it is not an erased obligation or an added assumption.

## Symbolic budget dependency trim

`S12.Budget` does not use marker coordinates or diagonal geometry. Its unused `S12.Markers` import was removed, finite-universe cardinalities now use standard cardinality facts, and the three arithmetic solver calls were isolated into private lemmas about natural-number bounds. Both public budget statements and all their original ownership/disjointness hypotheses are unchanged. Serial elaboration is enabled. The parent reports the revised module passed in7.417 seconds under the1200MiB aggregate guard.

`S12.PackingBudget` now transports its two exemption-table checks through the definitional equality `candidateMasks.map maskSupport = groupList`. The ordinary reducer checks the103 stored marker groups instead of repeatedly reconstructing16-bit supports during membership tests. A generic list zip/map lemma supplies the transport, without a per-candidate case split or a new native check. Its public table statements still use the original mask semantics. This last change is awaiting focused parent replay.

### Exemption-table replay accepted; hull proof reuse prepared

The stored-group `S12.PackingBudget` revision passed in10.016 seconds. `S12.HullBridge` now reuses all37 existing `hullCertN_checked` theorems through one generic list-membership construction. Its remaining finite check contains only key inequality and actual seed membership; it no longer recomputes the rational convex-combination certificates. `hullRows_keys` is a definitional equality. All public statements, seed premises and literal certificate data are preserved, with serial elaboration and no new native checks. The hull revision awaits parent replay.

### Hull replay accepted; transport finite checks factored

The revised `S12.HullBridge` passed in 10.173 seconds. `S12.FamilyTransport` now derives candidate-support distinctness from the existing classification cardinality. Its transformation checker is factored into eight symmetry instances of sorted Nat-mask list equality and eight corresponding canonical marker-list identities, with generic permutation and injectivity arguments supplying the original public statement. This avoids 824 separate nested finite-set conjunction checks and adds no native certificate. The row-shape statement and geometric packing transport remain unchanged; this transport revision awaits parent replay.
