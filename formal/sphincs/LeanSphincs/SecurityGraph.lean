import LeanSphincs.SecurityPosition
import LeanSphincs.SecurityTargetAssignment
import LeanSphincs.SecurityGameSupport

/-! Canonical structural graph preparation. The retained positions can be any subset;
positions omitted by pruning retain their initial labels (in particular surrogate values).
Graph edges and their exact inputs follow leanVM b7a107256, specialized to the candidate. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Graph

open Concrete Completeness
set_option backward.isDefEq.respectTransparency false

abbrev CanonicalGraphLabels := Position → HashOutput

def canonicalGraphSlots
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (labels : CanonicalGraphLabels) : Position → List Digest
  | .chain lay tree leaf chain step =>
      if step.val = 0 then [otsSecret lay tree leaf chain]
      else (Position.chain lay tree leaf chain step).children.map (fun child => truncateHash (labels child))
  | .ftsLeaf index tree leaf => [ftsSecret index tree leaf]
  | position => position.children.map (fun child => truncateHash (labels child))

def canonicalGraphInput (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (position : Position) (labels : CanonicalGraphLabels) : HashInput :=
  tweakableHashInput parameter position.domain
    ((canonicalGraphSlots otsSecret ftsSecret labels position).flatMap (bytesLE 16))

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem canonicalGraphInput_separated :
    ∀ left right : Position, left ≠ right → ∀ before after,
      canonicalGraphInput parameter otsSecret ftsSecret left before ≠
        canonicalGraphInput parameter otsSecret ftsSecret right after := by
  intro left right hne before after heq
  exact Position.input_separated parameter hne _ _ heq

theorem canonicalGraphInput_congr (position : Position) (left right : CanonicalGraphLabels)
    (hchildren : ∀ child ∈ position.children, truncateHash (left child) = truncateHash (right child)) :
    canonicalGraphInput parameter otsSecret ftsSecret position left =
      canonicalGraphInput parameter otsSecret ftsSecret position right := by
  have hmap := List.map_congr_left hchildren
  apply congrArg (fun values : List Digest =>
    tweakableHashInput parameter position.domain (values.flatMap (bytesLE 16)))
  cases position <;> simp only [canonicalGraphSlots] <;>
    first | rfl | exact hmap | (split_ifs <;> first | rfl | exact hmap)

def readCanonicalGraph (f : QueryImpl HashSpec Id) : List Position → CanonicalGraphLabels → CanonicalGraphLabels
  | [], labels => labels
  | position :: rest, labels =>
      readCanonicalGraph f rest (Function.update labels position
        (f (canonicalGraphInput parameter otsSecret ftsSecret position labels)))

theorem readCanonicalGraph_preserves (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels) (position : Position) (hposition : position ∉ positions) :
    readCanonicalGraph parameter otsSecret ftsSecret f positions labels position = labels position := by
  induction positions generalizing labels with
  | nil => rfl
  | cons first rest ih =>
      have hne : position ≠ first := fun h => hposition (by simp [h])
      have hrest : position ∉ rest := fun h => hposition (List.mem_cons_of_mem _ h)
      change readCanonicalGraph parameter otsSecret ftsSecret f rest
        (Function.update labels first (f (canonicalGraphInput parameter otsSecret ftsSecret first labels))) position = _
      rw [ih _ hrest, Function.update_of_ne hne]

theorem readCanonicalGraph_consistent (f : QueryImpl HashSpec Id) (positions : List Position)
    (hnodup : positions.Nodup)
    (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth))
    (labels : CanonicalGraphLabels) :
    ∀ position ∈ positions,
      readCanonicalGraph parameter otsSecret ftsSecret f positions labels position =
        f (canonicalGraphInput parameter otsSecret ftsSecret position
          (readCanonicalGraph parameter otsSecret ftsSecret f positions labels)) := by
  induction positions generalizing labels with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      intro position hposition
      rcases List.mem_cons.mp hposition with hposition | hposition
      · subst position
        have hinput : canonicalGraphInput parameter otsSecret ftsSecret first
            (readCanonicalGraph parameter otsSecret ftsSecret f (first :: rest) labels) =
              canonicalGraphInput parameter otsSecret ftsSecret first labels := by
          apply canonicalGraphInput_congr
          intro child hchild
          apply congrArg truncateHash
          apply readCanonicalGraph_preserves
          intro hmem
          have hlt := Position.depth_lt_of_mem_children hchild
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst child
            omega
          · have := hdepth child hmem
            omega
        rw [hinput]
        change readCanonicalGraph parameter otsSecret ftsSecret f rest
          (Function.update labels first (f (canonicalGraphInput parameter otsSecret ftsSecret first labels))) first = _
        rw [readCanonicalGraph_preserves _ _ _ _ _ _ _ hfirst, Function.update_self]
      · exact ih hrest hsorted _ position hposition

noncomputable def graphOrder (active : Position → Prop) : List Position := by
  classical
  exact ((Finset.univ : Finset Position).filter active).toList.mergeSort
    (fun left right => decide (left.depth ≤ right.depth))

theorem graphOrder_nodup (active : Position → Prop) : (graphOrder active).Nodup := by
  classical
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem mem_graphOrder (active : Position → Prop) (position : Position) :
    position ∈ graphOrder active ↔ active position := by
  classical
  rw [graphOrder, List.mem_mergeSort]
  simp

theorem graphOrder_sorted (active : Position → Prop) :
    (graphOrder active).Pairwise (fun left right => left.depth ≤ right.depth) := by
  classical
  have h := List.pairwise_mergeSort
    (le := fun left right : Position => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    ((Finset.univ : Finset Position).filter active).toList
  simpa only [graphOrder, decide_eq_true_eq] using h

def prepare : List Position → CanonicalGraphLabels → OracleComp HashSpec CanonicalGraphLabels
  | [], labels => pure labels
  | position :: rest, labels => do
      let answer ← liftM (HashSpec.query (canonicalGraphInput parameter otsSecret ftsSecret position labels))
      prepare rest (Function.update labels position answer)

theorem eval_prepare (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels) :
    evalWithAnswerFn f (prepare parameter otsSecret ftsSecret positions labels) =
      readCanonicalGraph parameter otsSecret ftsSecret f positions labels := by
  induction positions generalizing labels with
  | nil => rfl
  | cons position rest ih =>
      simp only [prepare, evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query
          (canonicalGraphInput parameter otsSecret ftsSecret position labels))) =
          f (canonicalGraphInput parameter otsSecret ftsSecret position labels) from
          simulateQ_spec_query f _, ih, readCanonicalGraph]

theorem input_read_above (f : QueryImpl HashSpec Id) (position : Position)
    (positions : List Position) (labels : CanonicalGraphLabels)
    (hdepth : ∀ next ∈ positions, position.depth ≤ next.depth) :
    canonicalGraphInput parameter otsSecret ftsSecret position
      (readCanonicalGraph parameter otsSecret ftsSecret f positions labels) =
        canonicalGraphInput parameter otsSecret ftsSecret position labels := by
  apply canonicalGraphInput_congr
  intro child hchild
  apply congrArg truncateHash
  apply readCanonicalGraph_preserves
  intro hmem
  have := hdepth child hmem
  have := Position.depth_lt_of_mem_children hchild
  omega

/-- Every prepared query is its position's final canonical input. Later preparation cannot
change its payload, since all of its children are at smaller depths. -/
theorem prepare_queriedInputs (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels)
    (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth)) :
    queriedInputs f (prepare parameter otsSecret ftsSecret positions labels) =
      positions.map (fun position => canonicalGraphInput parameter otsSecret ftsSecret position
        (readCanonicalGraph parameter otsSecret ftsSecret f positions labels)) := by
  induction positions generalizing labels with
  | nil => rfl
  | cons position rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hsorted
      rw [prepare, queriedInputs_query_bind, ih _ hrest, List.map_cons]
      congr 1
      exact (input_read_above parameter otsSecret ftsSecret f position (position :: rest) labels
        (by intro next h; rcases List.mem_cons.mp h with rfl | h; exact le_rfl; exact hfirst next h)).symm

end LeanSphincs.Security.Graph
