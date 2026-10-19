-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.Gauge.ECheck
import Submission.Work.GCert.Scalar.SourceReplay

/-!
# Source E7 wrapper (generic replay + `gInitL`, `sourceProg`)

A NEW check, not `GS.eCheck`.  Same gauge batches and `gInitL`; items are `sourceProg`
so phase A is replayed under `okBK`.  Soundness: a gauged slot never reaches a y role
in `Mt`.  Does not claim `eCheck = true`.

No `sorry`.  Do not edit `eCheck` or `GS.prog`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

/-- E7 on `sourceProg` (okBK on phase A). -/
noncomputable def sourceECheck (c : Raw) (p : SPar) (gl : List Nat) : Bool :=
  gPre c p 0 gl.length fun v2 nr _ tm K m2 =>
    guard (incK nr gl v2) (guard (Nat.ble (Nat.succ p.us) (Nat.pow 2 (Nat.sub p.sw 1)))
      (guard (Nat.ble (Nat.succ p.us) 2147483648)
        (forceN (List.length c.ret) fun rl =>
          gInitL p.sw p.us gl 0 (Trie.mk p.d) fun tr0 =>
            gItems c p v2 nr tm K m2 rl (sourceProg c) tr0 fun tr3 =>
              gFin p.sw K m2 p.uy c.v 0 0 tr3 c.v 0)))

/-- An accepted source-E7 replay. -/
def SourceERun (c : Raw) (gl : List Nat) : Prop :=
  ∃ (p : SPar) (a0 b : SSt), PGood c p 0 gl.length ∧ (∀ r ∈ gl, 2 * c.v ≤ r ∧ r < 2 * c.v + c.R) ∧
    gl.Nodup ∧ p.us < 2^(p.sw - 1) ∧
    (∀ r, a0.N r = 0 ∧ a0.P r = if r ∈ gl then p.us * 2^(p.sw * gl.idxOf r) else 0) ∧
    ItemsRun c p gl.length (sourceProg c) a0 b ∧ ∀ S, S < c.v → b.P (c.v + S) = b.N (c.v + S)

theorem SourceERun.of_check {c : Raw} {p : SPar} {gl : List Nat}
    (h : sourceECheck c p gl = true) : SourceERun c gl := by
  unfold sourceECheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p 0 gl.length _ h)
  obtain ⟨hinc, h2⟩ := guard_true h1
  obtain ⟨hus, h3⟩ := guard_true h2
  obtain ⟨hus2, h4⟩ := guard_true h3
  rw [forceN_eq] at h4
  obtain ⟨hgl, hnd⟩ := incK_sound _ gl _ hinc
  have hu1 := ble_true hus
  have hu2 := ble_true hus2
  have hlt : ∀ r ∈ gl, r < 2^p.d := fun r hr => by have := (hgl r hr).2; have := hp.hd; omega
  obtain ⟨t0, hwf, hk, hval⟩ := gInitL_sound p.d p.sw p.us gl 0 (Trie.mk p.d) _ (Trie.wf_mk p.d) hlt hnd h4
  have hval' : ∀ r, absS (2^p.d) t0 r = if r ∈ gl then leaf0 p.sw p.us (0 + gl.idxOf r)
      else absS (2^p.d) (Trie.mk p.d) r := hval
  have husw : p.us < 2^(p.sw - 1) := by
    have e : Nat.pow 2 (Nat.sub p.sw 1) = 2^(p.sw - 1) := rfl
    omega
  obtain ⟨hI0, hinit⟩ := init_okL p.d p.sw p.us gl hp.hsw husw (by omega) t0 hwf hval'
  obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p 0 gl.length hp (sourceProg c) t0 _ hI0 hk
  refine ⟨p, _, _, hp, hgl, hnd, husw, hinit, hr, fun S hS => ?_⟩
  have := gFin_sound p.d p.sw (64 + p.sw * gl.length) p.uy c.v 0 0 tr3 hI3.wf c.v 0 hk3 S hS
  rw [Nat.zero_add, if_neg (by omega), Nat.add_zero] at this
  exact this

/-- E7 from a source replay: gauged-slot column in the y rows of `Mt` is zero. -/
theorem SourceERun.ycol {c : Raw} (hv : 0 < c.v) {gl : List Nat} (h : SourceERun c gl)
    (q : Fin c.R) (hq : 2 * c.v + q.val ∈ gl) (S : Fin c.v) : Mt c hv (lY S) (lS q) = 0 := by
  obtain ⟨p, a0, b, hp, hgl, hnd, husw, hi, hr, hfin⟩ := h
  obtain ⟨a1, r1, r2⟩ := ItemsRun_split c p gl.length _ _ a0 b hr
  obtain ⟨a2, ⟨rS, hsh⟩, r3⟩ := r2
  have rA := ItemsRun_cB c p gl.length _ a0 a1 r1
  have rB := ItemsRun_cB c p gl.length _ a2 b r3
  have hokB : ∀ t s, okB c t s = true → emb c (unemb c hv t) = t ∧ emb c (unemb c hv s) = s :=
    fun t s ho => ⟨emb_unemb hv t (okB_spec ho).1, emb_unemb hv s (okB_spec ho).2.1⟩
  have hCA : Cm p.sw gl.length (U c p) (emb c) a1 = MA c hv * Cm p.sw gl.length (U c p) (emb c) a0 := by
    have := GRun_Cm p.sw gl.length (U c p) (okB c) (fun _ => true) (emb c) (unemb c hv) (unemb_emb hv) hokB
      (addsA c) a0 a1 rA
    rw [micF_true] at this
    exact this
  have hCB : Cm p.sw gl.length (U c p) (emb c) b = MB c hv * Cm p.sw gl.length (U c p) (emb c) a2 := by
    have := GRun_Cm p.sw gl.length (U c p) (okB c) (fun _ => true) (emb c) (unemb c hv) (unemb_emb hv) hokB
      (addsB c) a2 b rB
    rw [micF_true] at this
    exact this
  have hCS := cm_scat p 0 gl.length hp a1 a2 rS hsh
  have hus : p.us < 2^p.sw := lt_of_lt_of_le husw (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hT : gl.idxOf (2 * c.v + q.val) < gl.length := List.idxOf_lt_length_of_mem hq
  have u0 : (p.us : ℚ) ≠ 0 := by have := hp.hs; positivity
  have hC0 : ∀ j : Rl c, Cm p.sw gl.length (U c p) (emb c) a0 j ⟨gl.idxOf (2 * c.v + q.val), hT⟩
      = if j = lS q then 1 else 0 := by
    intro j
    show gcont p.sw (U c p) a0 (emb c j) (gl.idxOf (2 * c.v + q.val)) = _
    unfold gcont
    rw [(hi (emb c j)).1, (hi (emb c j)).2, dg_zero_left]
    by_cases hj : emb c j ∈ gl
    · rw [if_pos hj, dg_mul_pow p.sw p.us hus, U_s c p _ (hgl _ hj).1]
      by_cases e : j = lS q
      · have e' : emb c j = 2 * c.v + q.val := by rw [e]; rfl
        rw [if_pos (by rw [e']), if_pos e]
        field_simp
        simp
      · have e' : ¬ gl.idxOf (2 * c.v + q.val) = gl.idxOf (emb c j) := by
          intro he
          apply e
          have := (List.idxOf_inj hq).mp he
          rw [← unemb_emb hv j, ← this]
          exact unemb_emb hv (lS q)
        rw [if_neg e', if_neg e]
        simp
    · have e : ¬ j = lS q := fun e => hj (by rw [e]; exact hq)
      rw [if_neg hj, if_neg e, dg_zero_left]
      simp
  have key : Mt c hv (lY S) (lS q) = Cm p.sw gl.length (U c p) (emb c) b (lY S)
      ⟨gl.idxOf (2 * c.v + q.val), hT⟩ := by
    have e1 := mul_unitCol (Mt c hv) (Cm p.sw gl.length (U c p) (emb c) a0) (lS q) _ hC0 (lY S)
    rw [← e1]
    unfold Mt
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hCA, ← hCS, ← hCB]
  rw [key]
  show gcont p.sw (U c p) b (c.v + S.val) (gl.idxOf (2 * c.v + q.val)) = 0
  unfold gcont
  rw [hfin S.val S.isLt]
  simp

theorem sourceECheck_sound {c : Raw} {p : SPar} {gl : List Nat} (hv : 0 < c.v)
    (h : sourceECheck c p gl = true) (q : Fin c.R) (hq : 2 * c.v + q.val ∈ gl)
    (S : Fin c.v) : Mt c hv (lY S) (lS q) = 0 :=
  SourceERun.ycol hv (SourceERun.of_check h) q hq S

end GS

#print axioms GS.sourceECheck_sound
