-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.SourceTag16Sound
import Submission.Work.GCert.Data.C588ATTag16Checks
import Submission.Work.GCert.Data.Gen.C588ATYChk
import Submission.Work.GCert.Data.Gen.C588ATSrc0

/-!
C588AT source-scalar half from Tag16 checks. Not `GS.ScalOK` and not `GS.scalCheck`.
Four Tag16 source batches plus the existing y-check and `aNoYK`.
-/

set_option maxRecDepth 100000
namespace GXD.C588AT
open GXD

theorem srcOK : GS.SourceOK raw where
  hv := by decide
  hs := fun t ht =>
    if h0 : t < 28 then ⟨0, 28, Nat.zero_le t, h0, GS.Tag16.sourceCheck_sound src16_0_ok⟩ else
    if h1 : t < 56 then ⟨28, 28, Nat.le_of_not_lt h0, h1, GS.Tag16.sourceCheck_sound src16_1_ok⟩ else
    if h2 : t < 84 then ⟨56, 28, Nat.le_of_not_lt h1, h2, GS.Tag16.sourceCheck_sound src16_2_ok⟩ else
    ⟨84, 28, Nat.le_of_not_lt h2, Nat.lt_of_lt_of_le ht (by decide),
      GS.Tag16.sourceCheck_sound src16_3_ok⟩
  hyc := fun t ht =>
    ⟨0, 112, Nat.zero_le t, Nat.lt_of_lt_of_le ht (by decide), GS.YRun.of_check ychk_ok⟩
  hA_noY := GS.aNoYK_sound aNoY_ok

end GXD.C588AT

#print axioms GXD.C588AT.srcOK
