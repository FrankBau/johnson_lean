/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Tally

/-!
  Facts about single positions of the run (`PosOK`): the event itself as the code emits it (`EvOK`), the call entered there
  (`CallOK`), the frame an exit closes, and the UNBLOCK chain an unblock event belongs to (`ChainAt`).  The facts at a position
  look only at positions up to the exit of the call involved, so they survive appending further events (`PosOK.append`).
  `RunOK`: `PosOK` at every position.  Adapted from the BS-DFS formalization (Bsdfs/RunTrace.lean).
-/

namespace Johnson

open Trace

variable {n : Nat}

section posok
variable (G : Graph n) (s t : Fin n)

/-- the facts of the event at q, as the code emits it -/
def EvOK (T : List (Ev n)) (q : Nat) : Prop :=
  match T[q]? with
  | some (.enter _ z h) => h = (stk T q).length ∧ z ∉ stk T q ∧ z ≠ t ∧ blk T q z = false ∧ StackPath G s t (stk T q ++ [z])
  | some (.exit _ v _) => (stk T q).getLast? = some v
  | some (.output _ P) => P = stk T q ++ [t] ∧ P.Nodup ∧ ∀ x ∈ stk T q, blk T q x = true
  | some (.unblock _ u L) => blk T q u = true ∧ L.Nodup ∧ (∀ x ∈ L, u ∈ G.succ x) ∧ u ∉ (stk T q).dropLast ∧ G.Reach (stk T q).dropLast t u
  | some (.start _) => q = 0
  | some (.term _) => stk T q = []
  | _ => True

/-- the facts of the call entered at e and exited at x: its frame, its return value, Call Completeness -/
structure CallOK (T : List (Ev n)) (e x : Nat) : Prop where
  frame : Frame T e x
  ret : ∀ σ v f, T[x]? = some (.exit σ v f) → (f = true ↔ ∃ q σ' P, e < q ∧ q < x ∧ T[q]? = some (.output σ' P))
  complete : ∀ p, G.SimplePath s t p → (stk T (e + 1)) <+: p → ∃ q σ, e < q ∧ q < x ∧ T[q]? = some (.output σ p)

end posok

/-- the unblock event at q belongs to the UNBLOCK chain at the fruitful return of the top frame (e, x): the chain runs from q to
    the exit at x and consists of unblock events only -/
structure ChainAt (T : List (Ev n)) (q e x : Nat) : Prop where
  frame : Frame T e x
  lt : e < q ∧ q < x
  top : stk T q = stk T (e + 1)
  exit : ∃ σ v, T[x]? = some (.exit σ v true)
  all : ∀ r, q ≤ r → r < x → ∃ σ u L, T[r]? = some (.unblock σ u L)

/-- everything the delay proof needs to know about position q -/
structure PosOK (G : Graph n) (s t : Fin n) (T : List (Ev n)) (q : Nat) : Prop where
  ev : EvOK G s t T q
  call : ∀ σ v h, T[q]? = some (.enter σ v h) → ∃ x, CallOK G s t T q x
  exit : ∀ σ v f, T[q]? = some (.exit σ v f) → ∃ e, Frame T e q
  chain : ∀ σ u L, T[q]? = some (.unblock σ u L) → ∃ e x, ChainAt T q e x

/-- `PosOK` at every position of the trace -/
def RunOK (G : Graph n) (s t : Fin n) (T : List (Ev n)) : Prop := ∀ q, q < T.length → PosOK G s t T q

/-! ## Appending events keeps the past -/

section stable
variable {G : Graph n} {s t : Fin n} {T E : List (Ev n)}

theorem EvOK.append {q : Nat} (hq : q < T.length) (h : EvOK G s t T q) : EvOK G s t (T ++ E) q := by
  unfold EvOK at h ⊢
  rw [List.getElem?_append_left hq, Trace.stk_append (Nat.le_of_lt hq)]
  simp only [Trace.blk_append (Nat.le_of_lt hq)]
  exact h

theorem CallOK.append {e x : Nat} (h : CallOK G s t T e x) : CallOK G s t (T ++ E) e x := by
  have hx := h.frame.exit_lt
  have hex := h.frame.1
  refine ⟨h.frame.append, ?_, ?_⟩
  · intro σ v f hxe
    rw [List.getElem?_append_left hx] at hxe
    rw [h.ret σ v f hxe]
    constructor
    · rintro ⟨q, σ', P, h1, h2, hq⟩; exact ⟨q, σ', P, h1, h2, by rw [List.getElem?_append_left (by omega)]; exact hq⟩
    · rintro ⟨q, σ', P, h1, h2, hq⟩; exact ⟨q, σ', P, h1, h2, by rw [List.getElem?_append_left (by omega)] at hq; exact hq⟩
  · intro p hp hpre
    rw [Trace.stk_append (by omega)] at hpre
    obtain ⟨q, σ, h1, h2, hq⟩ := h.complete p hp hpre
    exact ⟨q, σ, h1, h2, by rw [List.getElem?_append_left (by omega)]; exact hq⟩

theorem ChainAt.append {q e x : Nat} (h : ChainAt T q e x) : ChainAt (T ++ E) q e x := by
  have hx := h.frame.exit_lt
  obtain ⟨hl1, hl2⟩ := h.lt
  refine ⟨h.frame.append, h.lt, ?_, ?_, ?_⟩
  · rw [Trace.stk_append (by omega), Trace.stk_append (by omega)]; exact h.top
  · obtain ⟨σ, v, hxe⟩ := h.exit
    exact ⟨σ, v, by rw [List.getElem?_append_left hx]; exact hxe⟩
  · intro r h1 h2
    obtain ⟨σ, u, L, hr⟩ := h.all r h1 h2
    exact ⟨σ, u, L, by rw [List.getElem?_append_left (by omega)]; exact hr⟩

theorem PosOK.append {q : Nat} (hq : q < T.length) (h : PosOK G s t T q) : PosOK G s t (T ++ E) q := by
  refine ⟨h.ev.append hq, ?_, ?_, ?_⟩
  · intro σ v hh he
    rw [List.getElem?_append_left hq] at he
    obtain ⟨x, hc⟩ := h.call σ v hh he
    exact ⟨x, hc.append⟩
  · intro σ v f he
    rw [List.getElem?_append_left hq] at he
    obtain ⟨e, hfr⟩ := h.exit σ v f he
    exact ⟨e, hfr.append⟩
  · intro σ u L he
    rw [List.getElem?_append_left hq] at he
    obtain ⟨e, x, hc⟩ := h.chain σ u L he
    exact ⟨e, x, hc.append⟩

end stable

/-! ## Reading `RunOK` -/

section run
variable {G : Graph n} {s t : Fin n} {T : List (Ev n)}

theorem RunOK.ev (hR : RunOK G s t T) {q : Nat} {e : Ev n} (he : T[q]? = some e) : EvOK G s t T q := (hR q (Trace.lt_of_getElem? he)).ev

theorem RunOK.enter (hR : RunOK G s t T) {q σ : Nat} {z : Fin n} {h : Nat} (he : T[q]? = some (.enter σ z h)) :
    h = (stk T q).length ∧ z ∉ stk T q ∧ z ≠ t ∧ blk T q z = false ∧ StackPath G s t (stk T q ++ [z]) := by
  have := hR.ev he; simp only [EvOK, he] at this; exact this

theorem RunOK.exit (hR : RunOK G s t T) {q σ : Nat} {v : Fin n} {f : Bool} (he : T[q]? = some (.exit σ v f)) : (stk T q).getLast? = some v := by
  have := hR.ev he; simp only [EvOK, he] at this; exact this

theorem RunOK.output (hR : RunOK G s t T) {q σ : Nat} {P : List (Fin n)} (he : T[q]? = some (.output σ P)) :
    P = stk T q ++ [t] ∧ P.Nodup ∧ ∀ x ∈ stk T q, blk T q x = true := by
  have := hR.ev he; simp only [EvOK, he] at this; exact this

theorem RunOK.unblock (hR : RunOK G s t T) {q σ : Nat} {u : Fin n} {L : List (Fin n)} (he : T[q]? = some (.unblock σ u L)) :
    blk T q u = true ∧ L.Nodup ∧ (∀ x ∈ L, u ∈ G.succ x) ∧ u ∉ (stk T q).dropLast ∧ G.Reach (stk T q).dropLast t u := by
  have := hR.ev he; simp only [EvOK, he] at this; exact this

theorem RunOK.callOK (hR : RunOK G s t T) {e x : Nat} (hfr : Frame T e x) : CallOK G s t T e x := by
  obtain ⟨σ, v, hh, he⟩ := hfr.2.1
  obtain ⟨x', hc⟩ := (hR e (Trace.lt_of_getElem? he)).call σ v hh he
  rw [hc.frame.exit_unique hfr] at hc
  exact hc

theorem RunOK.frame_of_enter (hR : RunOK G s t T) {e σ : Nat} {v : Fin n} {h : Nat} (he : T[e]? = some (.enter σ v h)) : ∃ x, Frame T e x := by
  obtain ⟨x, hc⟩ := (hR e (Trace.lt_of_getElem? he)).call σ v h he
  exact ⟨x, hc.frame⟩

theorem RunOK.frame_of_exit (hR : RunOK G s t T) {x σ : Nat} {v : Fin n} {f : Bool} (hx : T[x]? = some (.exit σ v f)) : ∃ e, Frame T e x :=
  (hR x (Trace.lt_of_getElem? hx)).exit σ v f hx

theorem RunOK.chain (hR : RunOK G s t T) {q σ : Nat} {u : Fin n} {L : List (Fin n)} (hq : T[q]? = some (.unblock σ u L)) : ∃ e x, ChainAt T q e x :=
  (hR q (Trace.lt_of_getElem? hq)).chain σ u L hq

end run

end Johnson
