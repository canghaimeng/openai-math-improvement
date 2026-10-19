-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.Bridge377.Bank
import Submission.Work.FoldRate.Group
import Submission.Work.GCert.Data.C588ATPrice
import Submission.Work.GCert.Data.RateC588AT

/-!
The numerical C588AT unit invoice, using the invocation rank counts checked
in C588ATPrice and the attributed #377 idle-data bank geometry. Its linkage
to a constructed invocation and the actual 4824-bank schedule is separate.
-/

namespace OAI.PowerSaving.BridgeRate.C588AT
open Finset Binary Matrix RAM CB FoldRate
noncomputable section

def padPrice (φ : ℕ → ℝ) : ℝ := 504 * bcost φ 1 + 72 * bcost φ 68

def unitPrice (φ : ℕ → ℝ) : ℝ :=
  72 * GXD.C588AT.invPrice φ + (112 : ℝ) * GX.bankPrice377 φ + padPrice φ

theorem unit_cost (φ : ℕ → ℝ) :
    unitPrice φ = listCost φ BlockAccounting.blocksC588AT := by
  unfold unitPrice GXD.C588AT.invPrice padPrice
  simp only [GX.bankPrice377, listCost, BlockAccounting.blocksC588AT,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [bcost]
  ring

theorem unit_tally : unitPrice (fun r => (r : ℝ)) = (11992 : ℝ) * 73 - 2560 := by
  rw [unit_cost]
  exact BlockAccounting.blocksC588AT_tally

end
end OAI.PowerSaving.BridgeRate.C588AT

#print axioms OAI.PowerSaving.BridgeRate.C588AT.unit_cost
