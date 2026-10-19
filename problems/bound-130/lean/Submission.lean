-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
-- Entry point for the Big O Speedrun exact-DFT target (all positive lengths).
-- Saving 63/50000. Local import path; verifier staging later prefixes `Submission.`.
-- DFTProgram, ConvProgram, paperTime, nlogn and the charged RAM model are OpenAI's
-- unchanged definitions from OAI.Computability.FourierTransform.Goal.
import Submission.Work.FourierC588AT.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (63 : ℝ) / 50000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainC588AT
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hexp : decimalExponentC588AT = 1 - (63 : ℝ) / 50000 := by
    norm_num [decimalExponentC588AT]
  have htime_eq : decimalTimeC588AT =
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (63 : ℝ) / 50000)) := by
    funext n
    simp only [decimalTimeC588AT, hexp]
  rw [← htime_eq]
  exact htime.2.1
