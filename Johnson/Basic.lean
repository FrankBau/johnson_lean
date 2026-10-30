/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Exec
import Std.Tactic.Do

/-!
  Generic facts used by several proof files: the loop cursor of `mvcgen` (a list split as `pref ++ cur :: suff`), Hoare
  triples over `StateM` as statements about the run, and `johnson_of_root`: a property of the trace of `johnson` from a
  spec of the root call.  Copied from the BS-DFS formalization (Bsdfs/Basic.lean) and adapted.
-/

open Std.Do

set_option mvcgen.warning false

namespace Johnson

variable {n : Nat}

/-! ## The loop cursor -/

section split
variable {α : Type} {xs pref suff : List α} {cur : α}

theorem mem_of_eq_append_cons (h : xs = pref ++ cur :: suff) : cur ∈ xs := by simp [h]

theorem not_mem_of_nodup_split (hnd : xs.Nodup) (h : xs = pref ++ cur :: suff) : cur ∉ pref := by
  rw [h] at hnd
  intro hc
  exact (List.nodup_append.mp hnd).2.2 cur hc cur (by simp) rfl

end split

/-! ## Hoare triples and the run -/

/-- a Hoare triple over `StateM` is a statement about the run, by definition -/
theorem StateM.triple_iff {σ α : Type} (x : StateM σ α) (P : σ → Prop) (Q : α → σ → Prop) :
    ⦃fun s => ⌜P s⌝⦄ x ⦃⇓ r s => ⌜Q r s⌝⦄ ↔ ∀ s, P s → Q (x.run s).1 (x.run s).2 :=
  ⟨fun h s hs => h s hs, fun h s hs => h s hs⟩

/-- the trace of `johnson` is the start event at step 0, the trace of the root call, and the term event: a spec of the root
    call from the state after the start event gives a property of the whole trace -/
theorem johnson_of_root {G : Graph n} {s t : Fin n} (P : St n → Prop) (Q : List (Ev n) → Prop)
    (hpre : P ⟨Vector.replicate n false, Vector.replicate n [], #[], 0, #[Ev.start 0]⟩)
    (hroot : ⦃fun st => ⌜P st⌝⦄ search G t s 0 ⦃⇓ _ st => ⌜Q (st.trace.toList ++ [Ev.term st.steps])⌝⦄) : Q (johnson G s t) := by
  unfold johnson
  dsimp only
  generalize hx : StateT.run _ _ = x
  refine StateM.of_wp_run_eq hx (fun x => Q x.2.trace.toList) ?_
  mvcgen [M.tick, M.emit, M.steps, hroot]
  simp +zetaDelta only [Array.toList_push]
  exact ‹Q _›

end Johnson
