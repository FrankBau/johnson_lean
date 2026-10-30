/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Paths

/-!
  The global invariant of Johnson's algorithm between steps, for the stack S, the blocked flags and the B-lists, and how
  the three state changes keep it: entering a vertex (`Inv.push`), the failed return (`Inv.fail`), and the fruitful return
  with its UNBLOCK chain (`Inv.chain`).

  Johnson's Lemma 1 (ii) is not a clause but a consequence (`Inv.dead`): a blocked vertex off the stack is on the B-list of
  each successor (B), so its successors are blocked (F), and a walk avoiding the stack stays blocked up to t, which never is
  (T).  The clause (E) on stale entries has no counterpart in Johnson's paper: UNBLOCK(u) empties only B(u), so a vertex
  unblocked through one B-list stays on the B-lists of its other successors, and may be back on the stack when one of them
  is emptied.  (E) says that this never unblocks a vertex on the stack.
-/

namespace Johnson

variable {n : Nat}

/-! ## Vectors -/

@[simp] theorem vget_set_self {α : Type} (b : Vector α n) (v : Fin n) (a : α) : (b.set v.1 a v.2)[v] = a := by
  simp [Fin.getElem_fin]

theorem vget_set_ne {α : Type} (b : Vector α n) {v x : Fin n} (a : α) (h : x ≠ v) : (b.set v.1 a v.2)[x] = b[x] := by
  simp only [Fin.getElem_fin, Vector.getElem_set, Fin.val_inj]
  simp [Ne.symm h]

/-! ## The invariant -/

section
variable (G : Graph n) (t : Fin n)

/-- the global invariant between steps, for the stack S (bottom first), the blocked flags bl and the B-lists B -/
structure Inv (S : List (Fin n)) (bl : Vector Bool n) (B : Vector (List (Fin n)) n) : Prop where
  /-- (A) every vertex on the stack is blocked -/
  stack : ∀ x : Fin n, x ∈ S → bl[x] = true
  /-- (T) t is never blocked -/
  target : bl[t] = false
  /-- (B) a blocked vertex off the stack is on the B-list of each of its successors -/
  reg : ∀ x : Fin n, bl[x] = true → x ∉ S → ∀ w ∈ G.succ x, x ∈ B[w]
  /-- (D) B-lists hold predecessors -/
  edge : ∀ w x : Fin n, x ∈ B[w] → w ∈ G.succ x
  /-- (E) if x ∈ B[w] is on the stack, then w is on the stack up to x, or w is off the stack and cannot reach t avoiding the
      stack up to x -/
  stale : ∀ w x : Fin n, x ∈ B[w] → ∀ L, L ++ [x] <+: S → w ∈ L ++ [x] ∨ (w ∉ S ∧ ¬ G.Reach (L ++ [x]) t w)
  /-- (F) only blocked vertices have nonempty B-lists -/
  wait : ∀ w : Fin n, B[w] ≠ [] → bl[w] = true
  /-- (N) B-lists have no duplicates -/
  nodup : ∀ w : Fin n, (B[w]).Nodup

/-- what UNBLOCK(v), called at the fruitful return of v from the stack S ++ [v], does to the blocked flags and B-lists -/
structure ChainPost (S : List (Fin n)) (v : Fin n) (bl0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (bl1 : Vector Bool n) (B1 : Vector (List (Fin n)) n) : Prop where
  /-- nothing gets blocked -/
  mono : ∀ x : Fin n, bl1[x] = true → bl0[x] = true
  /-- v gets unblocked -/
  top : bl1[v] = false
  /-- whatever waited on an unblocked vertex is unblocked -/
  closed : ∀ u x : Fin n, bl0[u] = true → bl1[u] = false → x ∈ B0[u] → bl1[x] = false
  /-- the B-list of an unblocked vertex is emptied -/
  cleared : ∀ u : Fin n, bl0[u] = true → bl1[u] = false → B1[u] = []
  /-- the other B-lists are kept -/
  kept : ∀ u : Fin n, (bl0[u] = true → bl1[u] = true) → B1[u] = B0[u]
  /-- an unblocked vertex is v, or off the stack and reaches t avoiding S (Johnson's Lemma 1 (i)) -/
  off : ∀ u : Fin n, bl0[u] = true → bl1[u] = false → u = v ∨ (u ∉ S ++ [v] ∧ G.Reach S t u)

end

section steps
variable {G : Graph n} {t : Fin n}

/-- Johnson's Lemma 1 (ii): a blocked vertex off the stack cannot reach t avoiding the stack -/
theorem Inv.dead {S : List (Fin n)} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} (hI : Inv G t S bl B) {x : Fin n} (hx : bl[x] = true) (hxS : x ∉ S) : ¬ G.Reach S t x := by
  rintro ⟨l, hw⟩
  induction hw with
  | refl => rw [hI.target] at hx; cases hx
  | step hxy hy _ ih => exact ih (hI.wait _ (List.ne_nil_of_mem (hI.reg _ hx hxS _ hxy))) hy

/-- entering v: v goes on the stack and gets blocked -/
theorem Inv.push {S : List (Fin n)} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} (hI : Inv G t S bl B) {v : Fin n} (hv : bl[v] = false) (hvS : v ∉ S) (hvt : v ≠ t) :
    Inv G t (S ++ [v]) (bl.set v.1 true v.2) B where
  stack := by
    intro x hx
    by_cases hxv : x = v
    · subst hxv; simp
    · rw [vget_set_ne _ _ hxv]
      exact hI.stack x (by simpa [hxv] using hx)
  target := by rw [vget_set_ne _ _ (Ne.symm hvt)]; exact hI.target
  reg := by
    intro x hx hxS w hw
    have hxv : x ≠ v := fun h => hxS (by simp [h])
    rw [vget_set_ne _ _ hxv] at hx
    exact hI.reg x hx (fun h => hxS (by simp [h])) w hw
  edge := hI.edge
  stale := by
    intro w x hxw L hL
    have hw0 := hI.wait w (List.ne_nil_of_mem hxw)
    have hwv : w ≠ v := fun h => by rw [h, hv] at hw0; cases hw0
    rcases List.prefix_concat_iff.mp hL with h | h
    · -- x = v and L = S: w is blocked, so it is on the stack, or off it and cannot reach t
      obtain ⟨rfl, hx⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at hx
      subst hx
      by_cases hwS : w ∈ L
      · left; simp [hwS]
      · right
        exact ⟨by simp [hwS, hwv], fun hr => hI.dead hw0 hwS (hr.mono (fun z hz => by simp [hz]))⟩
    · rcases hI.stale w x hxw L h with h1 | ⟨h1, h2⟩
      · left; exact h1
      · right; exact ⟨by simp [h1, hwv], h2⟩
  wait := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; simp
    · rw [vget_set_ne _ _ hwv]; exact hI.wait w hw
  nodup := hI.nodup

/-- the failed return of v from the stack S ++ [v]: v goes on the B-list of each successor, all of which are blocked -/
theorem Inv.fail {S : List (Fin n)} {bl : Vector Bool n} {B B' : Vector (List (Fin n)) n} {v : Fin n} (hI : Inv G t (S ++ [v]) bl B) (hvS : v ∉ S)
    (hsucc : ∀ w ∈ G.succ v, bl[w] = true) (hmem : ∀ w x : Fin n, x ∈ B'[w] ↔ x ∈ B[w] ∨ (x = v ∧ w ∈ G.succ v)) (hnd : ∀ w : Fin n, (B'[w]).Nodup) :
    Inv G t S bl B' where
  stack := fun x hx => hI.stack x (by simp [hx])
  target := hI.target
  reg := by
    intro x hx hxS w hw
    by_cases hxv : x = v
    · subst hxv; exact (hmem w x).mpr (Or.inr ⟨rfl, hw⟩)
    · exact (hmem w x).mpr (Or.inl (hI.reg x hx (by simp [hxS, hxv]) w hw))
  edge := by
    intro w x hx
    rcases (hmem w x).mp hx with h | ⟨rfl, h⟩
    · exact hI.edge w x h
    · exact h
  stale := by
    intro w x hx L hL
    have hxS : x ∈ S := hL.subset (by simp)
    have hxv : x ≠ v := fun h => hvS (h ▸ hxS)
    rcases (hmem w x).mp hx with h | ⟨h, _⟩
    · rcases hI.stale w x h L (hL.trans (List.prefix_append S [v])) with h1 | ⟨h1, h2⟩
      · left; exact h1
      · right; exact ⟨fun h' => h1 (by simp [h']), h2⟩
    · exact absurd h hxv
  wait := by
    intro w hw
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hw
    rcases (hmem w x).mp hx with h | ⟨-, h⟩
    · exact hI.wait w (List.ne_nil_of_mem h)
    · exact hsucc w h
  nodup := hnd

/-- each B-list after the chain is emptied, or kept for a vertex that stays blocked -/
theorem ChainPost.blist {S : List (Fin n)} {v : Fin n} {bl0 bl1 : Vector Bool n} {B0 B1 : Vector (List (Fin n)) n} (hc : ChainPost G t S v bl0 B0 bl1 B1) (u : Fin n) :
    (bl0[u] = true ∧ bl1[u] = false ∧ B1[u] = []) ∨ (B1[u] = B0[u] ∧ (bl0[u] = true → bl1[u] = true)) := by
  by_cases h : bl0[u] = true ∧ bl1[u] = false
  · left; exact ⟨h.1, h.2, hc.cleared u h.1 h.2⟩
  · right
    have hk : bl0[u] = true → bl1[u] = true := by
      intro h0
      cases h1 : bl1[u]
      · exact absurd ⟨h0, h1⟩ h
      · rfl
    exact ⟨hc.kept u hk, hk⟩

/-- the fruitful return of v from the stack S ++ [v]: after UNBLOCK(v) the invariant holds for S -/
theorem Inv.chain {S : List (Fin n)} {v : Fin n} {bl0 bl1 : Vector Bool n} {B0 B1 : Vector (List (Fin n)) n} (hI : Inv G t (S ++ [v]) bl0 B0) (hvS : v ∉ S) (hc : ChainPost G t S v bl0 B0 bl1 B1) :
    Inv G t S bl1 B1 where
  stack := by
    intro x hx
    cases h1 : bl1[x]
    · have h0 := hI.stack x (by simp [hx])
      rcases hc.off x h0 h1 with h | ⟨h, _⟩
      · exact absurd (h ▸ hx) hvS
      · exact absurd (by simp [hx]) h
    · rfl
  target := by
    cases h1 : bl1[t]
    · rfl
    · have := hc.mono t h1; rw [hI.target] at this; cases this
  reg := by
    intro x hx hxS w hw
    have h0 := hc.mono x hx
    have hxv : x ≠ v := fun h => by rw [h, hc.top] at hx; cases hx
    have hold := hI.reg x h0 (by simp [hxS, hxv]) w hw
    rcases hc.blist w with ⟨hw0, hw1, -⟩ | ⟨hB, -⟩
    · rw [hc.closed w x hw0 hw1 hold] at hx; cases hx
    · rw [hB]; exact hold
  edge := by
    intro w x hx
    rcases hc.blist w with ⟨-, -, hB⟩ | ⟨hB, -⟩
    · rw [hB] at hx; cases hx
    · rw [hB] at hx; exact hI.edge w x hx
  stale := by
    intro w x hx L hL
    rcases hc.blist w with ⟨-, -, hB⟩ | ⟨hB, -⟩
    · rw [hB] at hx; cases hx
    · rw [hB] at hx
      rcases hI.stale w x hx L (hL.trans (List.prefix_append S [v])) with h1 | ⟨h1, h2⟩
      · left; exact h1
      · right; exact ⟨fun h' => h1 (by simp [h']), h2⟩
  wait := by
    intro w hw
    rcases hc.blist w with ⟨-, -, hB⟩ | ⟨hB, hk⟩
    · exact absurd hB hw
    · exact hk (hI.wait w (hB ▸ hw))
  nodup := by
    intro w
    rcases hc.blist w with ⟨-, -, hB⟩ | ⟨hB, -⟩
    · rw [hB]; exact List.nodup_nil
    · rw [hB]; exact hI.nodup w

end steps

end Johnson
