import SphincsSecurity.Proof.Ots.EncodingFreshRow
import SphincsSecurity.Proof.Ots.ReferenceFamilyGame
import SphincsSecurity.Proof.Base.UniformTableObservation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def encodingSelectionRows (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  match selection with
  | none => fun _ => FirstSuccessTable.invalid decodeEncodingOutput
  | some (index, word) => FirstSuccessTable.allowed decodeEncodingOutput index word

noncomputable def encodingSelectionAllowed (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  if ∀ coordinate, (encodingSelectionRows selection coordinate).Nonempty then encodingSelectionRows selection
  else fun _ => Finset.univ

theorem encodingSelectionAllowed_nonempty (selection : ReferenceSelection) :
    ∀ coordinate, (encodingSelectionAllowed selection coordinate).Nonempty := by
  unfold encodingSelectionAllowed
  split_ifs with hrows
  · exact hrows
  · exact fun _ => Finset.univ_nonempty

theorem encodingSelectionAllowed_fresh (selection : ReferenceSelection) (dummy : Encoding) (coordinate : Fin encodingAttemptLimit) :
    FreshEncodingSupport ((selection.map Prod.snd).getD dummy) (encodingSelectionAllowed selection coordinate) := by
  unfold encodingSelectionAllowed
  split_ifs
  · cases selection with
    | none => exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
    | some selected =>
        obtain ⟨index, word⟩ := selected
        exact firstSuccess_allowed_fresh index word coordinate
  · exact Or.inl rfl

private theorem uniformTable_rows_eq {rows rows' : Fin encodingAttemptLimit → Finset HashOutput} (h : rows = rows')
    (hrows : ∀ coordinate, (rows coordinate).Nonempty) (hrows' : ∀ coordinate, (rows' coordinate).Nonempty) :
    uniformTable rows hrows = uniformTable rows' hrows' := by
  subst h
  rfl

theorem encoding_afterSelect_complete (selection : ReferenceSelection) :
    𝒟[FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection] =
      complete (encodingSelectionAllowed selection) := by
  rw [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection)]
  have hafter : FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      FirstSuccessTable.constrained (encodingSelectionRows selection) := by
    cases selection with
    | none => rfl
    | some selected =>
        obtain ⟨index, word⟩ := selected
        rfl
  rw [hafter, FirstSuccessTable.constrained]
  split_ifs with hrows
  · rw [uniformTable_rows_eq (show encodingSelectionRows selection = encodingSelectionAllowed selection from
      (if_pos hrows).symm) hrows (encodingSelectionAllowed_nonempty selection)]
  · rw [FirstSuccessTable.full, uniformTable_rows_eq (show (fun _ => Finset.univ) = encodingSelectionAllowed selection from
      (if_neg hrows).symm) _ (encodingSelectionAllowed_nonempty selection)]

end SphincsSecurity.Concrete
