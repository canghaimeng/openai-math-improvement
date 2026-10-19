-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.Gauge.Inv
import Submission.Work.GCert.Data.Glue
import Submission.Work.GCert.Data.C588ATSrcOK
import Submission.Work.GCert.Data.C588ATBanks

/-!
C588AT gauged invocation from Tag16 source/E7 checks, existing SourceOK identities,
`GXD.scalOf`, `GLab.ValidE.glab` and `GLab.inv`. Does not use `GXD.ginvOf` or `eCheck`.
-/

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GXD.C588AT
open GXD OAI.PowerSaving OAI.PowerSaving.CB OAI.PowerSaving.CR Matrix Finset

noncomputable section

def es : List (GS.SPar × List Nat) :=
  [(⟨10, 34, 2, 8, 8⟩, glb0), (⟨10, 34, 2, 8, 8⟩, glb1), (⟨10, 34, 2, 8, 8⟩, glb2)]

theorem es_gl : es.flatMap Prod.snd = gl := rfl

theorem es_ok : ∀ e ∈ es, GS.Tag16.sourceECheck raw e.1 e.2 = true := by
  intro e he
  unfold es at he
  rcases List.mem_cons.mp he with h | he
  · subst h; exact echk16_0_ok
  rcases List.mem_cons.mp he with h | he
  · subst h; exact echk16_1_ok
  rcases List.mem_cons.mp he with h | he
  · subst h; exact echk16_2_ok
  exact absurd he List.not_mem_nil

noncomputable def gscal : GX.GScal (Fin raw.v) (Fin raw.R) (Fin raw.ret.length) where
  toScal := scalOf raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid
  gauged := univ.filter (fun q : Fin raw.R => 2 * raw.v + q.val ∈ es.flatMap Prod.snd)
  hE := fun q hq t => by
    obtain ⟨e, he1, he2⟩ := List.mem_flatMap.mp (Finset.mem_filter.mp hq).2
    exact GS.Tag16.sourceECheck_sound srcOK.hv (es_ok e he1) q he2 t

theorem gscal_gauged (q : Fin raw.R) :
    q ∈ gscal.gauged ↔ 2 * raw.v + q.val ∈ es.flatMap Prod.snd := by
  show q ∈ univ.filter (fun q : Fin raw.R => 2 * raw.v + q.val ∈ es.flatMap Prod.snd) ↔ _
  simp

/-- Gauges of the label list `gl` are the Tag16 E7 sources. -/
theorem glab_hg (q : Fin raw.R) (hq : 2 * raw.v + q.val ∈ gl) : q ∈ gscal.gauged :=
  (gscal_gauged q).mpr (es_gl ▸ hq)

noncomputable def glab : GX.GLab (Fin aux.p.h) gscal :=
  validE.glab gscal (roles raw srcOK.hv) GS.toCoef
    (scalOf_MA raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (scalOf_MAi raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (scalOf_MB raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (scalOf_MBi raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (reg raw) (reg_slot raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid) (reg_mem raw)
    glab_hg

noncomputable def ginv : GX.GInvE (Fin aux.p.h) (Fin raw.v) (Fin raw.R) (Fin raw.ret.length) :=
  glab.inv

theorem ginv_cost (φ : ℕ → ℝ) : ginv.cost φ = invPrice φ := by
  have h5 : ∀ k : Fin raw.ret.length,
      bcost φ (GLab.cdim (aux.p.tab.get (aux.SA.get (GXD.reg raw k)))) = bcost φ 8 :=
    fun k => congrArg (bcost φ) (cen_dim _ (GXD.reg_mem raw k))
  have hr := validE.glab_ranks gscal (roles raw srcOK.hv) GS.toCoef
    (scalOf_MA raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (scalOf_MAi raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (scalOf_MB raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (scalOf_MBi raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid)
    (reg raw) (reg_slot raw srcOK.hv srcOK.hAi srcOK.hBi srcOK.hx srcOK.hy srcOK.hid) (reg_mem raw)
    glab_hg
  change GX.GLab.cost glab φ = _
  unfold GX.GLab.cost glab
  rw [hr.1, hr.2.1, hr.2.2.1]
  simp only [hr.2.2.2]
  rw [Finset.sum_congr rfl (fun k _ => h5 k), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fin, ← inv_cost φ, show raw.ret.length = 8 from by decide]
  norm_num [bcost]
  try rfl

theorem ginv_ent (q : Fin raw.R) : ginv.ent q = bankEnt q := rfl

theorem ginv_ent_dim (q : Fin raw.R) :
    (ginv.ent q).dim = GLab.cdim (par.tab.get (st0.get (2 * raw.v + q.val))) := by
  rw [ginv_ent, bankEnt_dim]

theorem ginv_fits : sched.fits ginv.ent := by
  convert fits
  funext q
  exact ginv_ent q

end
end GXD.C588AT

#print axioms GXD.C588AT.gscal
#print axioms GXD.C588AT.ginv
#print axioms GXD.C588AT.ginv_cost
#print axioms GXD.C588AT.ginv_ent
#print axioms GXD.C588AT.ginv_ent_dim
#print axioms GXD.C588AT.ginv_fits
