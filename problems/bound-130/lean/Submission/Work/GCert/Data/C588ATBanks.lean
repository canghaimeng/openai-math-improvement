-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Data.Gen.C588ATSched
import Submission.Work.GCert.Data.C588ATCert
import Submission.Work.GCert.Data.InstC588AT
import Submission.Work.Bridge401.Roles

/-!
C588AT banks for the checked entrance labels. The cyclic table follows
research-context/proof.md Part C and is verified by the unchanged #401
schedule checker. Its use by an actual GInvE requires the independent
semantic invocation proof and identification of that invocation's entrances.
-/

set_option maxRecDepth 100000
namespace GXD.C588AT
open OAI.PowerSaving CB GF
noncomputable section

def sched : GX.BankSched (Fin raw.R) :=
  GX.BankSched.ofTab 4824 raw.R schedRows schedPad schedRes sched_ok

/-- The helper entrance labels from the already checked label certificate. -/
def bankEnt (q : Fin raw.R) : SLbl (Fin aux.p.h) :=
  aux.p.labS aux.S0 (2 * raw.v + q.val)

theorem bankEnt_dim (q : Fin raw.R) :
    (bankEnt q).dim = GLab.cdim (par.tab.get (st0.get (2 * raw.v + q.val))) :=
  GLab.lab_dim (GLab.tabK_good _ _ validE.tab _)

theorem res_ok : ∀ q : Fin raw.R,
    9 - GLab.cdim (par.tab.get (st0.get (2 * raw.v + q.val))) =
      schedRes.getD q.val 0 := by
  decide +kernel

theorem fits : sched.fits bankEnt :=
  GX.BankSched.ofTab_fits _ _ _ _ _ sched_ok bankEnt (fun q => by
    rw [Fintype.card_fin, bankEnt_dim]
    exact res_ok q)

/-- Any invocation with these checked residuals uses this same schedule. -/
theorem fits_of_residuals {H : Type} [Fintype H] (ent : Fin raw.R → SLbl H)
    (he : ∀ q, Fintype.card H - (ent q).dim = schedRes.getD q.val 0) :
    sched.fits ent :=
  GX.BankSched.ofTab_fits _ _ _ _ _ sched_ok ent he

theorem width : 64 * Fintype.card (Fin raw.v) + sched.nb = 11992 := by
  rw [Fintype.card_fin]
  rfl

theorem live_card (Γ : Type) [Fintype Γ] :
    Fintype.card (GX.BLive401 Γ (Fin raw.v) sched.nb) = Fintype.card Γ * 11992 := by
  rw [GX.card_BLive401, width]

theorem pad_price (φ : ℕ → ℝ) :
    ∑ b, bcost φ (sched.pad b) = BridgeRate.C588AT.padPrice φ := by
  rw [sched, GX.BankSched.ofTab_padPrice]
  have repl (n r : ℕ) : rcost φ (List.replicate n r) = (n : ℝ) * bcost φ r := by
    simp only [rcost, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  unfold schedPad
  simp only [rcost_append, repl]
  norm_num [BridgeRate.C588AT.padPrice, bcost]

theorem invoice (φ : ℕ → ℝ) :
    72 * invPrice φ + (Fintype.card (Fin raw.v) : ℝ) * GX.bankPrice377 φ
      + ∑ b, bcost φ (sched.pad b) = Binary.listCost φ BlockAccounting.blocksC588AT := by
  rw [pad_price, Fintype.card_fin, raw_v]
  exact BridgeRate.C588AT.unit_cost φ

end
end GXD.C588AT

#print axioms GXD.C588AT.fits
#print axioms GXD.C588AT.width
#print axioms GXD.C588AT.invoice
