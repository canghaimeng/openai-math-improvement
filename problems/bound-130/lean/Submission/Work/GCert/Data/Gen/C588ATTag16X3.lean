-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.SourceTag16Def
import Submission.Work.GCert.Data.Gen.C588AT
/-! Finite check; Tag16 initialization soundness remains separate. -/
set_option maxRecDepth 100000
namespace GXD.C588AT
theorem src16_3_ok : GS.Tag16.sourceCheck raw ⟨10, 34, 2, 8, 8⟩ 84 28 = true := by
  decide +kernel
end GXD.C588AT
#print axioms GXD.C588AT.src16_3_ok
