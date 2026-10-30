/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Complete

/-!
  The run as a trace: the stack and the blocked flags before each position, frames, and counting of events over position ranges.
  Positions are indices into the event list; `stk tr p` and `blk tr p z` describe the state just before the event at p.  Adapted
  from the BS-DFS formalization (Bsdfs/Positions.lean, Bsdfs/Trace.lean, Bsdfs/Phases.lean, Bsdfs/RunTrace.lean).
-/

namespace Johnson

variable {n : Nat}

/-- the step stamp of an observable event (start, output, term) -/
def Ev.obs : Ev n → Option Nat
  | .start s | .output s _ | .term s => some s
  | _ => none

namespace Trace
variable (tr : List (Ev n))

/-- the stack before position p: enter pushes, exit pops -/
def stk : Nat → List (Fin n)
  | 0 => []
  | p + 1 =>
    match tr[p]? with
    | some (.enter _ v _) => stk p ++ [v]
    | some (.exit ..) => (stk p).dropLast
    | _ => stk p

/-- the blocked flag of z before position p: an entry blocks, an unblock unblocks -/
def blk : Nat → Fin n → Bool
  | 0, _ => false
  | p + 1, z =>
    match tr[p]? with
    | some (.enter _ v _) => if v = z then true else blk p z
    | some (.unblock _ u _) => if u = z then false else blk p z
    | _ => blk p z

/-- number of positions q with lo < q ≤ hi and P q -/
def cnt (P : Nat → Prop) [DecidablePred P] (lo hi : Nat) : Nat :=
  (List.range' (lo + 1) (hi - lo)).countP (fun q => decide (P q))

/-- events at position q, as Booleans for counting -/
def enterAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.enter _ v _) => v == z | _ => false
def unblockAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.unblock _ u _) => u == z | _ => false
def failAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.exit _ v false) => v == z | _ => false

/-- an observable event (start, output, term) at q -/
def isObs (q : Nat) : Bool := match tr[q]? with | some e => e.obs.isSome | none => false

/-- the frame entered at e (an enter event) is open at the positions e+1 .. x and its exit event is at x -/
def Frame (e x : Nat) : Prop :=
  e < x ∧ (∃ σ v h, tr[e]? = some (.enter σ v h)) ∧ (∃ σ v f, tr[x]? = some (.exit σ v f)) ∧
    (stk tr (x + 1)).length = (stk tr e).length ∧ ∀ q, e < q → q ≤ x → (stk tr e).length < (stk tr q).length

end Trace

open Trace

/-- a and c are consecutive observable events -/
structure Consec (tr : List (Ev n)) (a c : Nat) : Prop where
  lt : a < c
  bound : c < tr.length
  obs_a : isObs tr a = true
  obs_c : isObs tr c = true
  between : ∀ q, a < q → q < c → isObs tr q = false

/-! ## One step of the replays -/

section steps
variable {tr : List (Ev n)}

theorem Trace.stk_succ (p : Nat) : stk tr (p + 1) = match tr[p]? with
    | some (.enter _ v _) => stk tr p ++ [v]
    | some (.exit ..) => (stk tr p).dropLast
    | _ => stk tr p := rfl

theorem Trace.blk_succ (p : Nat) (z : Fin n) : blk tr (p + 1) z = match tr[p]? with
    | some (.enter _ v _) => if v = z then true else blk tr p z
    | some (.unblock _ u _) => if u = z then false else blk tr p z
    | _ => blk tr p z := rfl

theorem Trace.stk_succ_enter {p σ : Nat} {v : Fin n} {h : Nat} (hp : tr[p]? = some (.enter σ v h)) : stk tr (p + 1) = stk tr p ++ [v] := by
  simp [stk, hp]

theorem Trace.stk_succ_exit {p σ : Nat} {v : Fin n} {f : Bool} (hp : tr[p]? = some (.exit σ v f)) : stk tr (p + 1) = (stk tr p).dropLast := by
  simp [stk, hp]

theorem Trace.stk_succ_other {p : Nat} (h1 : ∀ σ v h, tr[p]? ≠ some (.enter σ v h)) (h2 : ∀ σ v f, tr[p]? ≠ some (.exit σ v f)) : stk tr (p + 1) = stk tr p := by
  rw [Trace.stk_succ]
  split
  · next heq => exact absurd heq (h1 _ _ _)
  · next heq => exact absurd heq (h2 _ _ _)
  · rfl

theorem Trace.blk_succ_enter {p σ : Nat} {v : Fin n} {h : Nat} (hp : tr[p]? = some (.enter σ v h)) (z : Fin n) : blk tr (p + 1) z = if v = z then true else blk tr p z := by
  simp [blk, hp]

theorem Trace.blk_succ_unblock {p σ : Nat} {u : Fin n} {L : List (Fin n)} (hp : tr[p]? = some (.unblock σ u L)) (z : Fin n) : blk tr (p + 1) z = if u = z then false else blk tr p z := by
  simp [blk, hp]

theorem Trace.blk_succ_other {p : Nat} (h1 : ∀ σ v h, tr[p]? ≠ some (.enter σ v h)) (h2 : ∀ σ u L, tr[p]? ≠ some (.unblock σ u L)) (z : Fin n) : blk tr (p + 1) z = blk tr p z := by
  rw [Trace.blk_succ]
  split
  · next heq => exact absurd heq (h1 _ _ _)
  · next heq => exact absurd heq (h2 _ _ _)
  · rfl

theorem Trace.enterAt_iff {z : Fin n} {q : Nat} : enterAt tr z q = true ↔ ∃ σ h, tr[q]? = some (.enter σ z h) := by
  unfold enterAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e <;> simp

theorem Trace.unblockAt_iff {z : Fin n} {q : Nat} : unblockAt tr z q = true ↔ ∃ σ L, tr[q]? = some (.unblock σ z L) := by
  unfold unblockAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e <;> simp

theorem Trace.failAt_iff {z : Fin n} {q : Nat} : failAt tr z q = true ↔ ∃ σ, tr[q]? = some (.exit σ z false) := by
  unfold failAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e with
    | exit σ v f => cases f <;> simp
    | _ => simp

/-- while the stack never gets shorter than r, its bottom r entries stay put -/
theorem Trace.stk_take_persist {p q r : Nat} (hpq : p ≤ q) (hr : ∀ i, p ≤ i → i ≤ q → r ≤ (stk tr i).length) : (stk tr q).take r = (stk tr p).take r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  clear hpq
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← ih (fun i h1 h2 => hr i h1 (by omega))]
    have hq := hr (p + d) (by omega) (by omega)
    have hq1 := hr (p + d + 1) (by omega) (by omega)
    rw [show p + (d + 1) = p + d + 1 by omega, Trace.stk_succ]
    rw [Trace.stk_succ] at hq1
    split
    · simp [List.take_append_of_le_length hq]
    · next heq =>
      simp only [heq] at hq1
      rw [List.dropLast_eq_take, List.take_take]
      congr 1
      simp at hq1
      omega
    · rfl

/-- a node off the stack stays off until it is entered -/
theorem Trace.not_mem_stk_of_no_enter {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (hz : z ∉ stk tr p₁) (h : ∀ q, p₁ ≤ q → q < p₂ → enterAt tr z q = false) : z ∉ stk tr p₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => exact hz
  | succ d ih =>
    have ih' := ih (fun q h1 h2 => h q h1 (by omega))
    have hq := h (p₁ + d) (by omega) (by omega)
    rw [show p₁ + (d + 1) = p₁ + d + 1 by omega, Trace.stk_succ]
    split
    · next σ v hh heq =>
      have hvz : v ≠ z := by
        intro hvz; subst hvz
        have : enterAt tr v (p₁ + d) = true := Trace.enterAt_iff.mpr ⟨σ, hh, heq⟩
        rw [hq] at this; exact Bool.false_ne_true this
      simp [ih', hvz.symm]
    · exact fun hm => ih' ((List.dropLast_sublist _).subset hm)
    · exact ih'

/-- an unblocked node gets blocked only by an entry -/
theorem Trace.exists_enter_of_blk {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (h1 : blk tr p₁ z = false) (h2 : blk tr p₂ z = true) : ∃ q, p₁ ≤ q ∧ q < p₂ ∧ enterAt tr z q = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => rw [Nat.add_zero, h1] at h2; cases h2
  | succ d ih =>
    by_cases hb : blk tr (p₁ + d) z = true
    · obtain ⟨q, hq1, hq2, hq⟩ := ih hb
      exact ⟨q, hq1, by omega, hq⟩
    · rw [show p₁ + (d + 1) = p₁ + d + 1 by omega, Trace.blk_succ] at h2
      split at h2
      · next σ v hh heq =>
        by_cases hvz : v = z
        · subst hvz; exact ⟨p₁ + d, by omega, by omega, Trace.enterAt_iff.mpr ⟨σ, hh, heq⟩⟩
        · simp [hvz] at h2; exact absurd h2 hb
      · next σ u L heq =>
        by_cases huz : u = z
        · simp [huz] at h2
        · simp [huz] at h2; exact absurd h2 hb
      · exact absurd h2 hb

end steps

/-! ## Counting over position ranges -/

section counting

theorem Trace.cnt_split (P : Nat → Prop) [DecidablePred P] {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) : cnt P lo hi = cnt P lo mid + cnt P mid hi := by
  unfold cnt
  have : List.range' (lo + 1) (hi - lo) = List.range' (lo + 1) (mid - lo) ++ List.range' (mid + 1) (hi - mid) := by
    rw [show mid + 1 = lo + 1 + (mid - lo) by omega, List.range'_append_1]; congr 1; omega
  rw [this, List.countP_append]

theorem Trace.cnt_zero (P : Nat → Prop) [DecidablePred P] {lo hi : Nat} (h : ∀ q, lo < q → q ≤ hi → ¬ P q) : cnt P lo hi = 0 := by
  unfold cnt
  rw [List.countP_eq_zero]
  intro q hq
  simp only [List.mem_range'_1] at hq
  simpa using h q (by omega) (by omega)

/-- one more position: the count of (lo, hi + 1] -/
theorem Trace.cnt_succ (P : Nat → Prop) [DecidablePred P] {lo hi : Nat} (h : lo ≤ hi) : cnt P lo (hi + 1) = cnt P lo hi + (if P (hi + 1) then 1 else 0) := by
  rw [Trace.cnt_split P h (Nat.le_succ hi)]
  congr 1
  unfold cnt
  rw [show hi + 1 - hi = 1 by omega]
  simp [List.range']

theorem nodup_map_of_inj {α β : Type} {l : List α} {f : α → β} (hl : l.Nodup) (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun a ha b hb => hf a (by simp [ha]) b (by simp [hb]))⟩
    intro hx
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hx
    exact hl.1 (by rw [hf x (by simp) y (by simp [hy]) hfy.symm]; exact hy)

/-- an injection from the P-positions into the Q-positions of (lo, hi] -/
theorem Trace.cnt_le_of_inj (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] (f : Nat → Nat) {lo hi : Nat} (hmap : ∀ q, lo < q → q ≤ hi → P q → lo < f q ∧ f q ≤ hi ∧ Q (f q)) (hinj : ∀ q₁ q₂, lo < q₁ → q₁ ≤ hi → lo < q₂ → q₂ ≤ hi → P q₁ → P q₂ → f q₁ = f q₂ → q₁ = q₂) : cnt P lo hi ≤ cnt Q lo hi := by
  unfold cnt
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hmem : ∀ q ∈ (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q)), lo < q ∧ q ≤ hi ∧ P q := by
    intro q hq
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hq
    exact ⟨by omega, by omega, hq.2⟩
  have hnd : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).Nodup := (List.nodup_range' (step := 1)).filter _
  have hnd' := nodup_map_of_inj (f := f) hnd (fun q₁ hq₁ q₂ hq₂ heq => by
    obtain ⟨a1, b1, c1⟩ := hmem q₁ hq₁
    obtain ⟨a2, b2, c2⟩ := hmem q₂ hq₂
    exact hinj q₁ q₂ a1 b1 a2 b2 c1 c2 heq)
  have hsub : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).map f ⊆ (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (Q q)) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    obtain ⟨a1, b1, c1⟩ := hmem q hq
    obtain ⟨h1, h2, h3⟩ := hmap q a1 b1 c1
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
    exact ⟨by omega, h3⟩
  have := hnd'.length_le_of_subset hsub
  simpa using this

/-- at most one position of (lo, hi] satisfies P -/
theorem Trace.cnt_le_one (P : Nat → Prop) [DecidablePred P] {lo hi : Nat} (h : ∀ q₁ q₂, lo < q₁ → q₁ ≤ hi → lo < q₂ → q₂ ≤ hi → P q₁ → P q₂ → q₁ = q₂) : cnt P lo hi ≤ 1 := by
  unfold cnt
  rw [List.countP_eq_length_filter]
  match hf : (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q)) with
  | [] => simp
  | [_] => simp
  | q₁ :: q₂ :: rest =>
    exfalso
    have hnd : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).Nodup := (List.nodup_range' (step := 1)).filter _
    have hm : ∀ q, q ∈ (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q)) → lo < q ∧ q ≤ hi ∧ P q := by
      intro q hq
      simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hq
      exact ⟨by omega, by omega, hq.2⟩
    rw [hf] at hnd hm
    obtain ⟨a1, b1, c1⟩ := hm q₁ (by simp)
    obtain ⟨a2, b2, c2⟩ := hm q₂ (by simp)
    have := h q₁ q₂ a1 b1 a2 b2 c1 c2
    subst this
    simp at hnd

/-- the first position in (lo, q] with P -/
theorem Trace.exists_first {P : Nat → Prop} {lo : Nat} : ∀ q, lo < q → P q → ∃ q₀, lo < q₀ ∧ q₀ ≤ q ∧ P q₀ ∧ ∀ q', lo < q' → q' < q₀ → ¬ P q'
  | q, h1, h2 => by
    by_cases hex : ∃ q', lo < q' ∧ q' < q ∧ P q'
    · obtain ⟨q', a1, a2, a3⟩ := hex
      obtain ⟨q₀, b1, b2, b3, b4⟩ := Trace.exists_first q' a1 a3
      exact ⟨q₀, b1, by omega, b3, b4⟩
    · exact ⟨q, h1, Nat.le_refl _, h2, fun q' a1 a2 a3 => hex ⟨q', a1, a2, a3⟩⟩
termination_by q => q

end counting

/-! ## Frames -/

section frames
variable {tr : List (Ev n)}

theorem Trace.Frame.push {e x : Nat} (h : Frame tr e x) : (stk tr (e + 1)).length = (stk tr e).length + 1 := by
  obtain ⟨-, ⟨σ, v, hh, he⟩, -⟩ := h
  rw [Trace.stk_succ_enter he]; simp

theorem Trace.Frame.isOpen {e x q : Nat} (h : Frame tr e x) (h1 : e < q) (h2 : q ≤ x) : (stk tr e).length + 1 ≤ (stk tr q).length :=
  h.2.2.2.2 q h1 h2

theorem Trace.Frame.prefix {e x q : Nat} (h : Frame tr e x) (h1 : e < q) (h2 : q ≤ x) : (stk tr q).take ((stk tr e).length + 1) = stk tr (e + 1) := by
  rw [Trace.stk_take_persist (p := e + 1) h1 (fun i hi1 hi2 => h.isOpen (by omega) (by omega)), ← h.push, List.take_length]

/-- while the frame is the top frame, the stack is the frame's own stack -/
theorem Trace.Frame.top {e x q : Nat} (h : Frame tr e x) (h1 : e < q) (h2 : q ≤ x) (hlen : (stk tr (e + 1)).length = (stk tr q).length) : stk tr q = stk tr (e + 1) := by
  have := h.prefix h1 h2
  rw [← h.push, hlen, List.take_length] at this
  exact this

theorem Trace.Frame.exit_unique {e x x' : Nat} (h : Frame tr e x) (h' : Frame tr e x') : x = x' := by
  rcases Nat.lt_trichotomy x x' with hlt | heq | hgt
  · have := h'.isOpen (q := x + 1) (by have := h.1; omega) (by omega); have := h.2.2.2.1; omega
  · exact heq
  · have := h.isOpen (q := x' + 1) (by have := h'.1; omega) (by omega); have := h'.2.2.2.1; omega

end frames

/-! ## Appending events keeps the past -/

section append
variable {T E : List (Ev n)}

theorem Trace.lt_of_getElem? {q : Nat} {e : Ev n} (h : T[q]? = some e) : q < T.length := (List.getElem?_eq_some_iff.mp h).1

theorem Trace.stk_append : ∀ {q : Nat}, q ≤ T.length → stk (T ++ E) q = stk T q
  | 0, _ => rfl
  | q + 1, hq => by
    rw [Trace.stk_succ, Trace.stk_succ, List.getElem?_append_left (by omega), Trace.stk_append (by omega)]

theorem Trace.blk_append : ∀ {q : Nat}, q ≤ T.length → ∀ z, blk (T ++ E) q z = blk T q z
  | 0, _, _ => rfl
  | q + 1, hq, z => by
    rw [Trace.blk_succ, Trace.blk_succ, List.getElem?_append_left (by omega), Trace.blk_append (by omega)]

theorem Trace.Frame.exit_lt {e x : Nat} (h : Frame T e x) : x < T.length := by
  obtain ⟨σ, v, f, hx⟩ := h.2.2.1
  exact Trace.lt_of_getElem? hx

theorem Trace.Frame.append {e x : Nat} (h : Frame T e x) : Frame (T ++ E) e x := by
  have hx := h.exit_lt
  obtain ⟨hex, ⟨σ, v, hh, he⟩, ⟨σ', v', f, hxe⟩, hsz, hopen⟩ := h
  refine ⟨hex, ⟨σ, v, hh, by rw [List.getElem?_append_left (by omega)]; exact he⟩, ⟨σ', v', f, by rw [List.getElem?_append_left hx]; exact hxe⟩, ?_, ?_⟩
  · rw [Trace.stk_append (by omega), Trace.stk_append (by omega)]; exact hsz
  · intro q h1 h2
    rw [Trace.stk_append (by omega), Trace.stk_append (by omega)]
    exact hopen q h1 h2

theorem Trace.stk_snoc_other {e : Ev n} (h1 : ∀ σ v h, e ≠ .enter σ v h) (h2 : ∀ σ v f, e ≠ .exit σ v f) : stk (T ++ [e]) (T.length + 1) = stk T T.length := by
  rw [Trace.stk_succ_other (fun σ v h he => h1 σ v h (by simpa using he)) (fun σ v f he => h2 σ v f (by simpa using he)), Trace.stk_append (Nat.le_refl _)]

theorem Trace.stk_snoc_enter {σ : Nat} {v : Fin n} {h : Nat} : stk (T ++ [.enter σ v h]) (T.length + 1) = stk T T.length ++ [v] := by
  have hp : (T ++ [Ev.enter σ v h])[T.length]? = some (.enter σ v h) := by simp
  rw [Trace.stk_succ_enter hp, Trace.stk_append (Nat.le_refl _)]

theorem Trace.stk_snoc_exit {σ : Nat} {v : Fin n} {f : Bool} : stk (T ++ [.exit σ v f]) (T.length + 1) = (stk T T.length).dropLast := by
  have hp : (T ++ [Ev.exit σ v f])[T.length]? = some (.exit σ v f) := by simp
  rw [Trace.stk_succ_exit hp, Trace.stk_append (Nat.le_refl _)]

theorem Trace.blk_snoc_other {e : Ev n} (h1 : ∀ σ v h, e ≠ .enter σ v h) (h2 : ∀ σ u L, e ≠ .unblock σ u L) (z : Fin n) : blk (T ++ [e]) (T.length + 1) z = blk T T.length z := by
  rw [Trace.blk_succ_other (fun σ v h he => h1 σ v h (by simpa using he)) (fun σ u L he => h2 σ u L (by simpa using he)), Trace.blk_append (Nat.le_refl _)]

theorem Trace.blk_snoc_enter {σ : Nat} {v : Fin n} {h : Nat} (z : Fin n) : blk (T ++ [.enter σ v h]) (T.length + 1) z = if v = z then true else blk T T.length z := by
  have hp : (T ++ [Ev.enter σ v h])[T.length]? = some (.enter σ v h) := by simp
  rw [Trace.blk_succ_enter hp, Trace.blk_append (Nat.le_refl _)]

theorem Trace.blk_snoc_unblock {σ : Nat} {u : Fin n} {L : List (Fin n)} (z : Fin n) : blk (T ++ [.unblock σ u L]) (T.length + 1) z = if u = z then false else blk T T.length z := by
  have hp : (T ++ [Ev.unblock σ u L])[T.length]? = some (.unblock σ u L) := by simp
  rw [Trace.blk_succ_unblock hp, Trace.blk_append (Nat.le_refl _)]

end append

end Johnson
