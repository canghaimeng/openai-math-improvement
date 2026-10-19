-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Data.C588ATGinv
import Submission.Work.GCert.Data.InstC588AT
import Submission.Work.Bridge401.End

/-!
C588AT tensor program for the all-length Fourier reduction.

This instantiates the unchanged #401 engine with the actual C588AT invocation,
its checked 4824-bank schedule, and the proved finite-fill moment inequality.
The local invocation retains eight initialized copies and all correction work;
the unit invoice includes the rank-68 padding and both idle terms of the engine.

The proof follows the attributed Work/FourierC588/Seam.lean in the pinned
Kothe–Shea source. Sussman's engine, Dugongue's and jacklightChen's #401/#377
geometry, Mamano's gauged extension, and OpenAI's Fourier interfaces retain
their original notices and licenses. The new source-replay soundness and
C588AT certificate are proved in the imported modules.
-/

namespace OAI.PowerSaving
noncomputable section

/-- Tensor exponent, leaving a saving gap of 1/1000000 before Fourier transfer. -/
def alphaC588AT : ℝ := 1 - 1261 / (10 : ℝ)^6

theorem alphaC588AT_pos : 0 < alphaC588AT := by norm_num [alphaC588AT]
theorem alphaC588AT_lt : alphaC588AT < 1 := by norm_num [alphaC588AT]

lemma envelope_monoC588AT (z : ℝ) (hz : 0 ≤ z) {a b : ℕ} (h : a ≤ b) :
    envelope z a ≤ envelope z b := by
  unfold envelope
  gcongr

lemma envelope_mono_expC588AT {z z' : ℝ} (h : z ≤ z') (k : ℕ) :
    envelope z k ≤ envelope z' k := by
  unfold envelope
  exact Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le (by simp) h)

def hillsC588AT (k : ℕ) := Nat.ceil (((k : ℝ) + 1)^alphaC588AT)

lemma hillsC588AT_eq_envelope : hillsC588AT = envelope alphaC588AT := rfl
lemma hillsC588AT_pos (k : ℕ) : 1 ≤ hillsC588AT k := envelope_pos alphaC588AT k
lemma hillsC588AT_mono {a b : ℕ} (h : a ≤ b) : hillsC588AT a ≤ hillsC588AT b :=
  envelope_monoC588AT alphaC588AT alphaC588AT_pos.le h
lemma hillsC588AT_le (k : ℕ) : hillsC588AT k ≤ k + 1 :=
  envelope_le alphaC588AT alphaC588AT_lt.le k
lemma hillsC588AT_real (k : ℕ) : (hillsC588AT k : ℝ) ≤ 2 * ((k : ℝ) + 1)^alphaC588AT :=
  envelope_real alphaC588AT alphaC588AT_pos.le k

namespace SeamC588AT
open Binary Matrix Finset RAM RAM.Ty
universe U

theorem h9 : Fintype.card (Fin GXD.C588AT.aux.p.h) = 9 := by
  rw [Fintype.card_fin]
  decide

/-- The actual invocation and schedule realize the full proposed unit list. -/
theorem unit_invoice (φ : ℕ → ℝ) :
    72 * GXD.C588AT.ginv.cost φ +
        (Fintype.card (Fin GXD.C588AT.raw.v) : ℝ) * GX.bankPrice377 φ +
        ∑ b, CB.bcost φ (GXD.C588AT.sched.pad b) =
      listCost φ BlockAccounting.blocksC588AT := by
  rw [GXD.C588AT.ginv_cost]
  exact GXD.C588AT.invoice φ

/-- Every colour, both modes, and every batch, with the engine's full charges. -/
theorem engine_C588AT (cl : Paint) (m : Bool) {ι : Type U} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i * envelope alphaC588AT (k i)) :=
  GX.engine_of_ginv_401 GXD.C588AT.ginv h9 GXD.C588AT.sched GXD.C588AT.ginv_fits
    73 11992 rfl GXD.C588AT.width (by norm_num) BlockAccounting.blocksC588AT
    unit_invoice 40 alphaC588AT alphaC588AT_pos.le alphaC588AT_lt.le
    BlockAccounting.fold_C588AT cl m k v

end SeamC588AT

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- OpenAI's tensor-program interface, realized by the checked C588AT engine. -/
theorem hillsC588AT_program (cl : Paint) (m : Bool) {ι : Type U} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i * hillsC588AT (k i)) :=
  SeamC588AT.engine_C588AT cl m k v

theorem envelope_program_geC588AT (z : ℝ) (hz : alphaC588AT ≤ z) (cl : Paint) (m : Bool)
    {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i * envelope z (k i)) :=
  (hillsC588AT_program cl m k v).mono fun i =>
    Nat.mul_le_mul_left _ (envelope_mono_expC588AT hz (k i))

end RAM

namespace SeamC588AT

def targetExponentC588AT : ℝ := 1 - (63 : ℝ) / 50000

lemma tensor_fourier_slack :
    targetExponentC588AT - alphaC588AT = 1 / (1000000 : ℝ) := by
  norm_num [targetExponentC588AT, alphaC588AT]

lemma alphaC588AT_lt_target : alphaC588AT < targetExponentC588AT := by
  norm_num [targetExponentC588AT, alphaC588AT]

end SeamC588AT
end
end OAI.PowerSaving

#print axioms OAI.PowerSaving.SeamC588AT.unit_invoice
#print axioms OAI.PowerSaving.SeamC588AT.engine_C588AT
#print axioms OAI.PowerSaving.RAM.hillsC588AT_program
