import Examples.Extracted

open Lampe Extracted

theorem make_intro :
    STHoare p Extracted.env ⟦⟧ («generics::Pair::generics::make».call h![J] h![a, b])
    fun output => output = ⟨a, ⟨b, ()⟩⟩ := by
  enter_decl
  steps
  congr

theorem make_diag_intro :
    STHoare p Extracted.env ⟦⟧ («generics::Pair::generics::make_diag».call h![J] h![a])
    fun output => output = ⟨a, ⟨a, ()⟩⟩ := by
  enter_decl
  steps
  congr

set_option Lampe.pp.STHoare false
set_option Lampe.pp.Expr false

theorem these_equal_spec :
    STHoare p Extracted.env ⟦⟧ («generics::these_equal».call h![] h![a])
    fun output => output = true := by
  enter_decl
  steps
  enter_block_as (⟦⟧) (fun output => output = (a, (a, ())))
  steps [make_intro]; assumption
  steps
  enter_block_as (⟦⟧) (fun output => output = (a, (a, ())))
  steps [make_diag_intro]; assumption
  steps
  apply STHoare.letIn_intro
  apply STHoare.consequence_frame_left
  apply STHoare.bAnd_intro
  sl
  intro v
  steps
  subst_vars
  simp_all
