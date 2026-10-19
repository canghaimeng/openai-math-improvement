-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.SourceTag16Def
import Submission.Work.GCert.Scalar.SourceReplay
import Submission.Work.Gauge.SourceECheck

/-!
Soundness of `GS.Tag16.init` / `initL` / `segCheck` / `sourceECheck`.

The only packing change is checksum modulus `65536`. Coefficient digits after
dropping the low 64 bits are the original unit contents. Existing
`gPre_sound` / `gItems_sound` / `gFin_sound` / `incK_sound` are reused.
`Tag16.segCheck = true` yields the existing `GS.SegOK`; `Tag16.sourceECheck = true`
yields the existing `GS.SourceERun`. No original checker is edited.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS.Tag16
open SSC GXD OAI.PowerSaving.CR

/-- 16-bit checksum weight of digit `T`. -/
def tau16 (T : Nat) : Nat := (2654435761 * (T + 1)) % 65536

theorem tau16_lt (T : Nat) : tau16 T < 2 ^ 16 := Nat.mod_lt _ (by norm_num)

theorem tau16_lt32 (T : Nat) : tau16 T < 2 ^ 32 :=
  Nat.lt_trans (tau16_lt T) (by norm_num)

/-- First leaf: same high digits as `leaf0`, 16-bit tag in the low word. -/
def leaf16 (sw u T : Nat) : Nat := u <<< (64 + sw * T) + u * tau16 T

theorem leaf16_packed (sw u T : Nat) :
    leaf16 sw u T =
      Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw T)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ T)) 65536)) := rfl

theorem leaf16_facts (sw n u T : Nat) (hu : u < 2 ^ (sw - 1)) (hsw : 1 ≤ sw) (hu2 : u < 2 ^ 31)
    (hT : T < n) :
    leaf16 sw u T < 2 ^ (64 + sw * n) ∧ leaf16 sw u T >>> 64 = u * 2 ^ (sw * T) ∧
      leaf16 sw u T % 2 ^ 64 < 2 ^ 63 := by
  have hc : tau16 T < 2 ^ 32 := tau16_lt32 T
  unfold leaf16
  generalize tau16 T = c at hc ⊢
  have huc : u * c < 2 ^ 63 := by
    have : u * c < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul'' hu2 hc
    have e : (2 : Nat) ^ 31 * 2 ^ 32 = 2 ^ 63 := by norm_num
    omega
  have e0 : u <<< (64 + sw * T) + u * c = u * c + (u * 2 ^ (sw * T)) * 2 ^ 64 := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc, Nat.add_comm]
  have hA : u * 2 ^ (sw * T) < 2 ^ (sw * n) := by
    have h1 : u < 2 ^ sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : u * 2 ^ (sw * T) < 2 ^ sw * 2 ^ (sw * T) := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    have h3 : 2 ^ sw * 2 ^ (sw * T) = 2 ^ (sw * (T + 1)) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    have h4 : 2 ^ (sw * (T + 1)) ≤ 2 ^ (sw * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    omega
  have h64 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, Nat.pow_add, Nat.mul_comm (2 ^ 64)]
    have : (u * 2 ^ (sw * T) + 1) * 2 ^ 64 ≤ 2 ^ (sw * n) * 2 ^ 64 := Nat.mul_le_mul_right _ hA
    have e : (u * 2 ^ (sw * T) + 1) * 2 ^ 64 = u * 2 ^ (sw * T) * 2 ^ 64 + 2 ^ 64 := by ring
    omega
  · rw [e0, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · rw [e0, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    exact huc

theorem init_succ (sw u off n i : Nat) (t : Trie) (k : Trie → Bool) :
    init sw u off (n + 1) i t k =
      forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
          (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 65536))) fun b =>
        forceN (Nat.succ i) fun i2 => init sw u off n i2 (t.set (Nat.add off i) b) k := rfl

theorem init_sound (d sw u off : Nat) : ∀ (n i : Nat) (t : Trie) (k : Trie → Bool), t.wf d →
    off + i + n ≤ 2 ^ d → init sw u off n i t k = true →
    ∃ t', t'.wf d ∧ k t' = true ∧ ∀ r, absS (2 ^ d) t' r
      = if off + i ≤ r ∧ r < off + i + n then leaf16 sw u (r - off) else absS (2 ^ d) t r := by
  intro n
  induction n with
  | zero =>
    intro i t k hwf _ h
    refine ⟨t, hwf, h, fun r => ?_⟩
    have hn : ¬ (off + i ≤ r ∧ r < off + i + 0) := by omega
    rw [if_neg hn]
  | succ n ih =>
    intro i t k hwf hle h
    rw [init_succ, forceN_eq, forceN_eq] at h
    have hi : off + i < 2 ^ d := by omega
    obtain ⟨t', hwf', hk, hval⟩ := ih (i + 1) _ k (Trie.wf_set d t hwf _ _) (by omega) h
    refine ⟨t', hwf', hk, fun r => ?_⟩
    rw [hval r]
    have hs := absS_set d t hwf (off + i) (leaf16 sw u i) hi
    have hs' : absS (2 ^ d) (t.set (Nat.add off i) (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 65536))))
        = Function.update (absS (2 ^ d) t) (off + i) (leaf16 sw u i) := hs
    rw [hs']
    by_cases e : r = off + i
    · have h1 : ¬ (off + (i + 1) ≤ r ∧ r < off + (i + 1) + n) := by omega
      have h2 : off + i ≤ r ∧ r < off + i + (n + 1) := by omega
      have e3 : r - off = i := by omega
      rw [if_neg h1, if_pos h2, e, Function.update_self, ← e, e3]
    · rw [Function.update_of_ne e]
      by_cases hA : off + (i + 1) ≤ r ∧ r < off + (i + 1) + n
      · have h2 : off + i ≤ r ∧ r < off + i + (n + 1) := by omega
        rw [if_pos hA, if_pos h2]
      · have h2 : ¬ (off + i ≤ r ∧ r < off + i + (n + 1)) := by omega
        rw [if_neg hA, if_neg h2]

/-- After `Tag16.init` on the empty trie: existing `GOk` and source digits. -/
theorem init_ok (d sw n u off : Nat) (hsw : 1 ≤ sw) (hu : u < 2 ^ (sw - 1)) (hu2 : u < 2 ^ 31)
    (t' : Trie) (hwf : t'.wf d)
    (hval : ∀ r, absS (2 ^ d) t' r = if off + 0 ≤ r ∧ r < off + 0 + n then leaf16 sw u (r - off)
      else absS (2 ^ d) (Trie.mk d) r) :
    GOk d sw n t' ∧ ∀ r, (absG d (64 + sw * n) t').N r = 0 ∧ (absG d (64 + sw * n) t').P r
      = if off ≤ r ∧ r < off + n then u * 2 ^ (sw * (r - off)) else 0 := by
  have hus : u < 2 ^ sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have key : ∀ r, (absS (2 ^ d) t' r % 2 ^ (64 + sw * n)) >>> 64
        = (if off ≤ r ∧ r < off + n then u * 2 ^ (sw * (r - off)) else 0) ∧
      absS (2 ^ d) t' r >>> (64 + sw * n) = 0 ∧ absS (2 ^ d) t' r % 2 ^ (64 + sw * n) % 2 ^ 64 < 2 ^ 63 := by
    intro r
    rw [hval r, Nat.add_zero]
    by_cases hr : off ≤ r ∧ r < off + n
    · obtain ⟨f1, f2, f3⟩ := leaf16_facts sw n u (r - off) hu hsw hu2 (by omega)
      rw [if_pos hr, if_pos hr, Nat.mod_eq_of_lt f1, Nat.shiftRight_eq_div_pow _ (64 + sw * n),
        Nat.div_eq_of_lt f1]
      exact ⟨f2, rfl, f3⟩
    · rw [if_neg hr, if_neg hr, absS_mk]
      exact ⟨by simp, by simp, by norm_num⟩
  refine ⟨⟨hwf, fun r => ?_⟩, fun r => ?_⟩
  · obtain ⟨k1, k2, k3⟩ := key r
    refine ⟨⟨?_, k3⟩, ?_⟩
    · rw [k1]
      intro T _
      by_cases hr : off ≤ r ∧ r < off + n
      · rw [if_pos hr, dg_mul_pow sw u hus]
        by_cases e : T = r - off
        · rw [if_pos e]; exact hu
        · rw [if_neg e]; exact Nat.two_pow_pos _
      · rw [if_neg hr, dg_zero_left]; exact Nat.two_pow_pos _
    · rw [k2]; exact ok_zero sw n
  · obtain ⟨k1, k2, _⟩ := key r
    refine ⟨?_, k1⟩
    show (absS (2 ^ d) t' r >>> (64 + sw * n)) >>> 64 = 0
    rw [k2]; rfl

theorem incK_eq : @incK = @GS.incK := rfl

theorem initL_cons (sw u r : Nat) (gl : List Nat) (i : Nat) (t : Trie) (k : Trie → Bool) :
    initL sw u (r :: gl) i t k =
      forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
          (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 65536))) fun b =>
        forceN (Nat.succ i) fun i2 => initL sw u gl i2 (t.set r b) k := rfl

theorem initL_sound (d sw u : Nat) : ∀ (gl : List Nat) (i : Nat) (t : Trie) (k : Trie → Bool), t.wf d →
    (∀ r ∈ gl, r < 2 ^ d) → gl.Nodup → initL sw u gl i t k = true →
    ∃ t', t'.wf d ∧ k t' = true ∧ ∀ r, absS (2 ^ d) t' r
      = if r ∈ gl then leaf16 sw u (i + gl.idxOf r) else absS (2 ^ d) t r := by
  intro gl
  induction gl with
  | nil =>
    intro i t k hwf _ _ h
    exact ⟨t, hwf, h, fun r => by rw [if_neg List.not_mem_nil]⟩
  | cons r0 gl ih =>
    intro i t k hwf hlt hnd h
    rw [initL_cons, forceN_eq, forceN_eq] at h
    have hr0 : r0 < 2 ^ d := hlt r0 List.mem_cons_self
    obtain ⟨hn0, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨t', hwf', hk, hval⟩ := ih (i + 1) _ k (Trie.wf_set d t hwf _ _)
      (fun r hr => hlt r (List.mem_cons_of_mem _ hr)) hnd' h
    refine ⟨t', hwf', hk, fun r => ?_⟩
    rw [hval r]
    have hs := absS_set d t hwf r0 (leaf16 sw u i) hr0
    have hs' : absS (2 ^ d) (t.set r0 (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 65536))))
        = Function.update (absS (2 ^ d) t) r0 (leaf16 sw u i) := hs
    rw [hs']
    by_cases e : r = r0
    · subst e
      rw [if_neg hn0, if_pos List.mem_cons_self, Function.update_self, List.idxOf_cons_self, Nat.add_zero]
    · rw [Function.update_of_ne e, List.idxOf_cons_ne _ (Ne.symm e)]
      by_cases hm : r ∈ gl
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        congr 1
        omega
      · rw [if_neg hm, if_neg (fun h => by rcases List.mem_cons.mp h with h | h; exact e h; exact hm h)]

/-- After `Tag16.initL` on the empty trie: existing `GOk` and gauged-source digits. -/
theorem init_okL (d sw u : Nat) (gl : List Nat) (hsw : 1 ≤ sw) (hu : u < 2 ^ (sw - 1)) (hu2 : u < 2 ^ 31)
    (t' : Trie) (hwf : t'.wf d)
    (hval : ∀ r, absS (2 ^ d) t' r = if r ∈ gl then leaf16 sw u (0 + gl.idxOf r) else absS (2 ^ d) (Trie.mk d) r) :
    GOk d sw gl.length t' ∧ ∀ r, (absG d (64 + sw * gl.length) t').N r = 0 ∧
      (absG d (64 + sw * gl.length) t').P r = if r ∈ gl then u * 2 ^ (sw * gl.idxOf r) else 0 := by
  have hus : u < 2 ^ sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have key : ∀ r, (absS (2 ^ d) t' r % 2 ^ (64 + sw * gl.length)) >>> 64
        = (if r ∈ gl then u * 2 ^ (sw * gl.idxOf r) else 0) ∧
      absS (2 ^ d) t' r >>> (64 + sw * gl.length) = 0 ∧
        absS (2 ^ d) t' r % 2 ^ (64 + sw * gl.length) % 2 ^ 64 < 2 ^ 63 := by
    intro r
    rw [hval r, Nat.zero_add]
    by_cases hr : r ∈ gl
    · obtain ⟨f1, f2, f3⟩ := leaf16_facts sw gl.length u (gl.idxOf r) hu hsw hu2
        (List.idxOf_lt_length_of_mem hr)
      rw [if_pos hr, if_pos hr, Nat.mod_eq_of_lt f1, Nat.shiftRight_eq_div_pow _ (64 + sw * gl.length),
        Nat.div_eq_of_lt f1]
      exact ⟨f2, rfl, f3⟩
    · rw [if_neg hr, if_neg hr, absS_mk]
      exact ⟨by simp, by simp, by norm_num⟩
  refine ⟨⟨hwf, fun r => ?_⟩, fun r => ?_⟩
  · obtain ⟨k1, k2, k3⟩ := key r
    refine ⟨⟨?_, k3⟩, ?_⟩
    · rw [k1]
      intro T _
      by_cases hr : r ∈ gl
      · rw [if_pos hr, dg_mul_pow sw u hus]
        by_cases e : T = gl.idxOf r
        · rw [if_pos e]; exact hu
        · rw [if_neg e]; exact Nat.two_pow_pos _
      · rw [if_neg hr, dg_zero_left]; exact Nat.two_pow_pos _
    · rw [k2]; exact ok_zero sw gl.length
  · obtain ⟨k1, k2, _⟩ := key r
    refine ⟨?_, k1⟩
    show (absS (2 ^ d) t' r >>> (64 + sw * gl.length)) >>> 64 = 0
    rw [k2]; rfl

/-- `Tag16.segCheck = true` yields the existing `GS.SegOK`. -/
theorem segCheck_sound {c : Raw} {p : SPar} {lo n : Nat} {pre post : Option Trie}
    {items : List Item} (h : segCheck c p lo n pre items post = true) :
    SegOK c p lo n pre items post := by
  unfold segCheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p lo n _ h)
  rw [forceN_eq] at h1
  refine ⟨hp, ?_⟩
  have hpost : ∀ tr3, GOk p.d p.sw n tr3 →
      Option.rec (motive := fun _ => Bool)
        (guard (gFin p.sw (64 + p.sw * n) (2 ^ (64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
          (gFin p.sw (64 + p.sw * n) (2 ^ (64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
        (fun t => beqK tr3 t) post = true →
      PostSt c p lo n post (absG p.d (64 + p.sw * n) tr3) := by
    intro tr3 hI3 hk
    cases post with
    | none =>
      obtain ⟨f1, f2⟩ := guard_true hk
      exact ⟨hI3.small, fin_of c p lo n hp 0 p.ux tr3 hI3 f1, fin_of c p lo n hp c.v p.uy tr3 hI3 f2⟩
    | some t =>
      have e : tr3 = t := beqK_eq tr3 t hk
      rw [← e]
      exact ⟨hI3, rfl⟩
  cases pre with
  | none =>
    have h2 : init p.sw p.ux lo n 0 (Trie.mk p.d) (fun tr0 =>
        gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2 ^ (64 + p.sw * n))
          c.ret.length items tr0 fun tr3 => Option.rec (motive := fun _ => Bool)
            (guard (gFin p.sw (64 + p.sw * n) (2 ^ (64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
              (gFin p.sw (64 + p.sw * n) (2 ^ (64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
            (fun t => beqK tr3 t) post) = true := h1
    have hle : lo + 0 + n ≤ 2 ^ p.d := by have := hp.hd; have := hp.hn; omega
    obtain ⟨t0, hwf, hk, hval⟩ := init_sound p.d p.sw p.ux lo n 0 (Trie.mk p.d) _ (Trie.wf_mk p.d)
      hle h2
    obtain ⟨hI0, hinit⟩ := init_ok p.d p.sw n p.ux lo hp.hsw hp.hxs hp.hx2 t0 hwf hval
    obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p lo n hp items t0 _ hI0 hk
    exact ⟨_, _, hinit, hr, hpost tr3 hI3 hk3⟩
  | some t =>
    intro hI0
    have h2 : gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n)
        (2 ^ (64 + p.sw * n)) c.ret.length items t (fun tr3 => Option.rec (motive := fun _ => Bool)
          (guard (gFin p.sw (64 + p.sw * n) (2 ^ (64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
            (gFin p.sw (64 + p.sw * n) (2 ^ (64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
          (fun t => beqK tr3 t) post) = true := h1
    obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p lo n hp items t _ hI0 h2
    exact ⟨_, hr, hpost tr3 hI3 hk3⟩

theorem sourceCheck_sound {c : Raw} {p : SPar} {lo n : Nat}
    (h : sourceCheck c p lo n = true) : SourceRun c lo n :=
  SourceRun.of_seg (segCheck_sound h)

/-- `Tag16.sourceECheck = true` yields the existing `GS.SourceERun`. -/
theorem sourceECheck_run {c : Raw} {p : SPar} {gl : List Nat}
    (h : sourceECheck c p gl = true) : SourceERun c gl := by
  unfold sourceECheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p 0 gl.length _ h)
  obtain ⟨hinc, h2⟩ := guard_true h1
  obtain ⟨hus, h3⟩ := guard_true h2
  obtain ⟨hus2, h4⟩ := guard_true h3
  rw [forceN_eq] at h4
  have hinc' : GS.incK (2 * c.v + c.R) gl (2 * c.v) = true := by
    rw [← incK_eq]; exact hinc
  obtain ⟨hgl, hnd⟩ := incK_sound _ gl _ hinc'
  have hu1 := ble_true hus
  have hu2 := ble_true hus2
  have hlt : ∀ r ∈ gl, r < 2 ^ p.d := fun r hr => by have := (hgl r hr).2; have := hp.hd; omega
  obtain ⟨t0, hwf, hk, hval⟩ := initL_sound p.d p.sw p.us gl 0 (Trie.mk p.d) _ (Trie.wf_mk p.d) hlt hnd h4
  have hval' : ∀ r, absS (2 ^ p.d) t0 r = if r ∈ gl then leaf16 p.sw p.us (0 + gl.idxOf r)
      else absS (2 ^ p.d) (Trie.mk p.d) r := hval
  have husw : p.us < 2 ^ (p.sw - 1) := by
    have e : Nat.pow 2 (Nat.sub p.sw 1) = 2 ^ (p.sw - 1) := rfl
    omega
  obtain ⟨hI0, hinit⟩ := init_okL p.d p.sw p.us gl hp.hsw husw (by omega) t0 hwf hval'
  obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p 0 gl.length hp (sourceProg c) t0 _ hI0 hk
  refine ⟨p, _, _, hp, hgl, hnd, husw, hinit, hr, fun S hS => ?_⟩
  have := gFin_sound p.d p.sw (64 + p.sw * gl.length) p.uy c.v 0 0 tr3 hI3.wf c.v 0 hk3 S hS
  rw [Nat.zero_add, if_neg (by omega), Nat.add_zero] at this
  exact this

theorem sourceECheck_sound {c : Raw} {p : SPar} {gl : List Nat} (hv : 0 < c.v)
    (h : sourceECheck c p gl = true) (q : Fin c.R) (hq : 2 * c.v + q.val ∈ gl)
    (S : Fin c.v) : Mt c hv (lY S) (lS q) = 0 :=
  SourceERun.ycol hv (sourceECheck_run h) q hq S

end GS.Tag16

#print axioms GS.Tag16.tau16_lt32
#print axioms GS.Tag16.leaf16_facts
#print axioms GS.Tag16.init_ok
#print axioms GS.Tag16.init_okL
#print axioms GS.Tag16.incK_eq
#print axioms GS.Tag16.segCheck_sound
#print axioms GS.Tag16.sourceCheck_sound
#print axioms GS.Tag16.sourceECheck_run
#print axioms GS.Tag16.sourceECheck_sound
