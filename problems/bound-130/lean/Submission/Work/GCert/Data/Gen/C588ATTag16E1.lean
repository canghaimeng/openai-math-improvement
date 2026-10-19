-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.SourceTag16Def
import Submission.Work.GCert.Data.Gen.C588ATGl
/-! Finite gauge check; Tag16 initialization soundness remains separate. -/
set_option maxRecDepth 100000
namespace GXD.C588AT
theorem echk16_1_ok : GS.Tag16.sourceECheck raw ⟨10, 34, 2, 8, 8⟩ glb1 = true := by
  decide +kernel
end GXD.C588AT
#print axioms GXD.C588AT.echk16_1_ok
