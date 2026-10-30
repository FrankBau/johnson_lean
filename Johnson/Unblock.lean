/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Invariant

/-!
  The UNBLOCK chain at the fruitful return of v from the stack S ++ [v].  One spec for `unblock u d`, relative to the state
  at its call: it unblocks u and, recursively, everything that waited on a vertex it unblocks (`closed`), empties exactly the
  B-lists of the vertices it unblocks, and every vertex it unblocks is v or off the stack with a walk to t avoiding S
  (`off`, Johnson's Lemma 1 (i)).  The last fact is where the stale-entry clause (E) is used: a vertex w on the B-list of a
  vertex u that the chain unblocks cannot be on the stack below v, because u reaches t avoiding S.

  The depth guard: the vertices of the nested calls, P ++ [u], are distinct and unblocked, and the next one is blocked, so
  P ++ [u, w] has no duplicates and d + 2 ≤ n.
-/

open Std.Do

set_option mvcgen.warning false

namespace Johnson

variable {n : Nat}

section
variable (G : Graph n) (t : Fin n) (S : List (Fin n)) (v : Fin n)

/-- the part of the invariant that holds throughout the chain, for the stack S ++ [v] -/
structure BInv (b : Vector Bool n) (B : Vector (List (Fin n)) n) : Prop where
  target : b[t] = false
  edge : ∀ w x : Fin n, x ∈ B[w] → w ∈ G.succ x
  stale : ∀ w x : Fin n, x ∈ B[w] → ∀ L, L ++ [x] <+: S ++ [v] → w ∈ L ++ [x] ∨ (w ∉ S ++ [v] ∧ ¬ G.Reach (L ++ [x]) t w)
  wait : ∀ w : Fin n, B[w] ≠ [] → b[w] = true
  nodup : ∀ w : Fin n, (B[w]).Nodup

/-- precondition of `unblock u d` in the chain of v -/
structure UPre (u : Fin n) (d : Nat) (b : Vector Bool n) (B : Vector (List (Fin n)) n) : Prop where
  nd : (S ++ [v]).Nodup
  reach : G.Reach S t v
  blk : b[u] = true
  pos : u = v ∨ (u ∉ S ++ [v] ∧ G.Reach S t u)
  vfree : u ≠ v → b[v] = false
  inv : BInv G t S v b B
  /-- d distinct unblocked vertices: those of the enclosing calls -/
  deep : ∃ P : List (Fin n), P.Nodup ∧ P.length = d ∧ ∀ x ∈ P, b[x] = false

/-- invariant of the loop over L = B0[u] in `unblock u d`, after the entries pref, relative to the state (b0, B0) at the call -/
structure ULoop (u : Fin n) (b0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (pref : List (Fin n)) (b : Vector Bool n) (B : Vector (List (Fin n)) n) : Prop where
  mono : ∀ x : Fin n, b[x] = true → b0[x] = true
  self : b[u] = false
  prog : ∀ x ∈ pref, b[x] = false
  closed : ∀ y x : Fin n, y ≠ u → b0[y] = true → b[y] = false → x ∈ B0[y] → b[x] = false
  cleared : ∀ y : Fin n, b0[y] = true → b[y] = false → B[y] = []
  kept : ∀ y : Fin n, (b0[y] = true → b[y] = true) → B[y] = B0[y]
  off : ∀ y : Fin n, b0[y] = true → b[y] = false → y = v ∨ (y ∉ S ++ [v] ∧ G.Reach S t y)
  inv : BInv G t S v b B

/-- what `unblock u d` guarantees, relative to the state (b0, B0) at the call -/
structure UPost (u : Fin n) (b0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (b1 : Vector Bool n) (B1 : Vector (List (Fin n)) n) : Prop where
  mono : ∀ x : Fin n, b1[x] = true → b0[x] = true
  self : b1[u] = false
  closed : ∀ y x : Fin n, b0[y] = true → b1[y] = false → x ∈ B0[y] → b1[x] = false
  cleared : ∀ y : Fin n, b0[y] = true → b1[y] = false → B1[y] = []
  kept : ∀ y : Fin n, (b0[y] = true → b1[y] = true) → B1[y] = B0[y]
  off : ∀ y : Fin n, b0[y] = true → b1[y] = false → y = v ∨ (y ∉ S ++ [v] ∧ G.Reach S t y)
  inv : BInv G t S v b1 B1

end

section steps
variable {G : Graph n} {t : Fin n} {S : List (Fin n)} {v : Fin n}

theorem Inv.binv {bl : Vector Bool n} {B : Vector (List (Fin n)) n} (hI : Inv G t (S ++ [v]) bl B) : BInv G t S v bl B :=
  ⟨hI.target, hI.edge, hI.stale, hI.wait, hI.nodup⟩

theorem UPost.chainPost {b0 b1 : Vector Bool n} {B0 B1 : Vector (List (Fin n)) n} (h : UPost G t S v v b0 B0 b1 B1) : ChainPost G t S v b0 B0 b1 B1 :=
  ⟨h.mono, h.self, h.closed, h.cleared, h.kept, h.off⟩

theorem not_blocked_of_mono {b0 b : Vector Bool n} {x : Fin n} (hmono : ∀ x : Fin n, b[x] = true → b0[x] = true) (h0 : b0[x] = false) : b[x] = false := by
  cases h : b[x]
  · rfl
  · have := hmono x h; rw [h0] at this; cases this

/-- the depth guard: P ++ [u] has no duplicates -/
theorem UPre.depth {u : Fin n} {d : Nat} {b : Vector Bool n} {B : Vector (List (Fin n)) n} (h : UPre G t S v u d b B) : d < n := by
  obtain ⟨P, hnd, hlen, hfree⟩ := h.deep
  have hu : u ∉ P := fun hu => by have := hfree u hu; rw [h.blk] at this; cases this
  have := nodup_length_le _ (nodup_snoc hnd hu)
  simp [hlen] at this
  omega

/-- the loop state right after u is unblocked and its B-list emptied -/
theorem uloop_init {u : Fin n} {d : Nat} {b0 : Vector Bool n} {B0 : Vector (List (Fin n)) n} (h : UPre G t S v u d b0 B0) :
    ULoop G t S v u b0 B0 [] (b0.set u.1 false u.2) (B0.set u.1 [] u.2) := by
  have hut : u ≠ t := fun hut => by have := h.inv.target; rw [← hut, h.blk] at this; cases this
  refine { mono := ?_, self := by simp, prog := by simp, closed := ?_, cleared := ?_, kept := ?_, off := ?_, inv := ?_ }
  · intro x hx
    by_cases hxu : x = u
    · subst hxu; simp at hx
    · rwa [vget_set_ne _ _ hxu] at hx
  · intro y x hyu hy0 hy _
    rw [vget_set_ne _ _ hyu, hy0] at hy; cases hy
  · intro y hy0 hy
    by_cases hyu : y = u
    · subst hyu; simp
    · rw [vget_set_ne _ _ hyu, hy0] at hy; cases hy
  · intro y hy
    by_cases hyu : y = u
    · subst hyu; have := hy h.blk; simp at this
    · exact vget_set_ne _ _ hyu
  · intro y hy0 hy
    by_cases hyu : y = u
    · subst hyu; exact h.pos
    · rw [vget_set_ne _ _ hyu, hy0] at hy; cases hy
  · refine ⟨by rw [vget_set_ne _ _ (Ne.symm hut)]; exact h.inv.target, ?_, ?_, ?_, ?_⟩
    · intro w x hx
      by_cases hwu : w = u
      · subst hwu; simp at hx
      · rw [vget_set_ne _ _ hwu] at hx; exact h.inv.edge w x hx
    · intro w x hx
      by_cases hwu : w = u
      · subst hwu; simp at hx
      · rw [vget_set_ne _ _ hwu] at hx; exact h.inv.stale w x hx
    · intro w hw
      by_cases hwu : w = u
      · subst hwu; simp at hw
      · rw [vget_set_ne _ _ hwu] at hw ⊢; exact h.inv.wait w hw
    · intro w
      by_cases hwu : w = u
      · subst hwu; simp
      · rw [vget_set_ne _ _ hwu]; exact h.inv.nodup w

/-- an entry w of B0[u] that is already unblocked -/
theorem uloop_skip {u : Fin n} {b0 b : Vector Bool n} {B0 B : Vector (List (Fin n)) n} {pref : List (Fin n)} {w : Fin n} (h : ULoop G t S v u b0 B0 pref b B) (hw : b[w] = false) :
    ULoop G t S v u b0 B0 (pref ++ [w]) b B := by
  refine { h with prog := ?_ }
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h.prog x hx
  · simp at hx; subst hx; exact hw

/-- a blocked entry w of B0[u] is off the stack and reaches t avoiding S: by (E), as u does -/
theorem child_pos {u w : Fin n} {d : Nat} {b0 : Vector Bool n} {B0 : Vector (List (Fin n)) n} (h : UPre G t S v u d b0 B0) (hw : w ∈ B0[u]) (hwv : w ≠ v) :
    w ∉ S ++ [v] ∧ G.Reach S t w := by
  have hvS : v ∉ S := fun hv => (List.nodup_append.mp h.nd).2.2 v hv v (by simp) rfl
  have hru : G.Reach S t u := by
    rcases h.pos with rfl | ⟨_, hr⟩
    · exact h.reach
    · exact hr
  have huS : u ∉ S := by
    rcases h.pos with rfl | ⟨hu, _⟩
    · exact hvS
    · exact fun h' => hu (by simp [h'])
  refine ⟨?_, hru.step (h.inv.edge u w hw) huS⟩
  intro hwS
  have hwS' : w ∈ S := by simpa [hwv] using hwS
  obtain ⟨A, C, rfl⟩ := List.append_of_mem hwS'
  have hpre : A ++ [w] <+: A ++ w :: C ++ [v] := ⟨C ++ [v], by simp⟩
  have hsub : ∀ z, z ∈ A ++ [w] → z ∈ A ++ w :: C := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ hz
    · simp at hz; subst hz; simp
  rcases h.inv.stale u w hw A hpre with h1 | ⟨_, h2⟩
  · exact huS (hsub u h1)
  · exact h2 (hru.mono hsub)

/-- the preconditions of the nested call `unblock w (d + 1)` for a blocked entry w of B0[u] -/
theorem uloop_child_pre {u w : Fin n} {d : Nat} {b0 b : Vector Bool n} {B0 B : Vector (List (Fin n)) n} {pref : List (Fin n)}
    (h0 : UPre G t S v u d b0 B0) (h : ULoop G t S v u b0 B0 pref b B) (hw : w ∈ B0[u]) (hwb : b[w] = true) :
    UPre G t S v w (d + 1) b B := by
  have hvb : b[v] = false := by
    by_cases huv : u = v
    · subst huv; exact h.self
    · exact not_blocked_of_mono h.mono (h0.vfree huv)
  have hwv : w ≠ v := fun hwv => by rw [hwv, hvb] at hwb; cases hwb
  obtain ⟨P, hnd, hlen, hfree⟩ := h0.deep
  have hu : u ∉ P := fun hu => by have := hfree u hu; rw [h0.blk] at this; cases this
  refine { nd := h0.nd, reach := h0.reach, blk := hwb, pos := Or.inr (child_pos h0 hw hwv), vfree := fun _ => hvb, inv := h.inv, deep := ⟨P ++ [u], nodup_snoc hnd hu, by simp [hlen], ?_⟩ }
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact not_blocked_of_mono h.mono (hfree x hx)
  · simp at hx; subst hx; exact h.self

/-- after the nested call `unblock w (d + 1)` for a blocked entry w -/
theorem uloop_child_post {u w : Fin n} {b0 b b' : Vector Bool n} {B0 B B' : Vector (List (Fin n)) n} {pref : List (Fin n)}
    (h : ULoop G t S v u b0 B0 pref b B) (hc : UPost G t S v w b B b' B') :
    ULoop G t S v u b0 B0 (pref ++ [w]) b' B' := by
  refine { mono := fun x hx => h.mono x (hc.mono x hx), self := not_blocked_of_mono hc.mono h.self, prog := ?_, closed := ?_, cleared := ?_, kept := ?_, off := ?_, inv := hc.inv }
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact not_blocked_of_mono hc.mono (h.prog x hx)
    · simp at hx; subst hx; exact hc.self
  · intro y x hyu hy0 hy' hx
    cases hy : b[y]
    · exact not_blocked_of_mono hc.mono (h.closed y x hyu hy0 hy hx)
    · have hB : B[y] = B0[y] := h.kept y (fun _ => hy)
      exact hc.closed y x hy hy' (by rw [hB]; exact hx)
  · intro y hy0 hy'
    cases hy : b[y]
    · rw [hc.kept y (fun h' => by rw [hy] at h'; cases h')]; exact h.cleared y hy0 hy
    · exact hc.cleared y hy hy'
  · intro y hk
    have h1 : b[y] = true → b'[y] = true := fun hb => hk (h.mono y hb)
    have h2 : b0[y] = true → b[y] = true := fun hb0 => hc.mono y (hk hb0)
    rw [hc.kept y h1, h.kept y h2]
  · intro y hy0 hy'
    cases hy : b[y]
    · exact h.off y hy0 hy
    · exact hc.off y hy hy'

/-- all entries of B0[u] processed -/
theorem uloop_final {u : Fin n} {b0 b : Vector Bool n} {B0 B : Vector (List (Fin n)) n} (h : ULoop G t S v u b0 B0 B0[u] b B) :
    UPost G t S v u b0 B0 b B where
  mono := h.mono
  self := h.self
  closed := by
    intro y x hy0 hy hx
    by_cases hyu : y = u
    · subst hyu; exact h.prog x hx
    · exact h.closed y x hyu hy0 hy hx
  cleared := h.cleared
  kept := h.kept
  off := h.off
  inv := h.inv

end steps

/-- UNBLOCK spec (ghost equations first, so that `mvcgen` instantiates b0, B0 and O0 by unification) -/
theorem unblock_spec (G : Graph n) (t : Fin n) (S : List (Fin n)) (v : Fin n) (Sa : Array (Fin n)) (u : Fin n) (d : Nat) (b0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (O0 : List (List (Fin n))) :
    ⦃fun st => ⌜st.blocked = b0 ∧ st.B = B0 ∧ outputs st.trace.toList = O0 ∧ st.S = Sa ∧ NoAbort st.trace ∧ UPre G t S v u d b0 B0⌝⦄
    unblock u d
    ⦃⇓ _ st => ⌜st.S = Sa ∧ outputs st.trace.toList = O0 ∧ NoAbort st.trace ∧ UPost G t S v u b0 B0 st.blocked st.B⌝⦄ := by
  -- spec of the nested call; vacuous unless d + 1 < n
  have ih : ∀ w (b1 : Vector Bool n) (B1 : Vector (List (Fin n)) n) (O1 : List (List (Fin n))),
      ⦃fun st => ⌜st.blocked = b1 ∧ st.B = B1 ∧ outputs st.trace.toList = O1 ∧ st.S = Sa ∧ NoAbort st.trace ∧ UPre G t S v w (d + 1) b1 B1⌝⦄
      unblock w (d + 1)
      ⦃⇓ _ st => ⌜st.S = Sa ∧ outputs st.trace.toList = O1 ∧ NoAbort st.trace ∧ UPost G t S v w b1 B1 st.blocked st.B⌝⦄ := by
    intro w b1 B1 O1
    by_cases hd : d + 1 < n
    · exact unblock_spec G t S v Sa w (d + 1) b1 B1 O1
    · intro st hP
      exact absurd hP.2.2.2.2.2.depth hd
  rw [unblock]
  mvcgen [M.tick, M.emit, M.steps, M.isBlocked, M.setBlocked, M.blist, M.setBlist, ih] invariants
  · ⇓⟨xs, _⟩ st => ⌜st.S = Sa ∧ outputs st.trace.toList = O0 ∧ NoAbort st.trace ∧ ULoop G t S v u b0 B0 xs.prefix st.blocked st.B⌝
  case vc1.step.isTrue.isTrue.pre =>
    -- nested call: its precondition
    obtain ⟨-, hB, -, -, -, pre⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ ∧ _ = Sa ∧ NoAbort _ ∧ UPre G t S v u d b0 B0›
    obtain ⟨hS, -, hna, hinv⟩ := ‹_ = Sa ∧ _ ∧ NoAbort _ ∧ ULoop G t S v u b0 B0 _ _ _›
    have hsplit := ‹_ = _ ++ _ :: _›
    have hblk := ‹_ = true›
    simp +zetaDelta only at hsplit hblk ⊢
    rw [hB] at hsplit
    exact ⟨trivial, trivial, trivial, hS, hna, uloop_child_pre pre hinv (mem_of_eq_append_cons hsplit) hblk⟩
  case vc2.step.isTrue.isTrue.post.success =>
    -- nested call: back in the loop
    obtain ⟨-, hout, -, hinv⟩ := ‹_ = Sa ∧ _ ∧ NoAbort _ ∧ ULoop G t S v u b0 B0 _ _ _›
    obtain ⟨hS', hout', hna', hpost⟩ := ‹_ = Sa ∧ _ ∧ NoAbort _ ∧ UPost G t S v _ _ _ _ _›
    simp +zetaDelta only at hout' hpost
    exact ⟨hS', by rw [hout', hout], hna', uloop_child_post hinv hpost⟩
  case vc3.step.isTrue.isFalse =>
    -- the depth guard fails: impossible
    obtain ⟨-, hB, -, -, -, pre⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ ∧ _ = Sa ∧ NoAbort _ ∧ UPre G t S v u d b0 B0›
    obtain ⟨-, -, -, hinv⟩ := ‹_ = Sa ∧ _ ∧ NoAbort _ ∧ ULoop G t S v u b0 B0 _ _ _›
    have hsplit := ‹_ = _ ++ _ :: _›
    have hblk := ‹_ = true›
    have hd := ‹¬ d + 1 < n›
    simp +zetaDelta only at hsplit hblk
    rw [hB] at hsplit
    exact absurd (uloop_child_pre pre hinv (mem_of_eq_append_cons hsplit) hblk).depth hd
  case vc4.step.isFalse =>
    -- an entry that is already unblocked
    obtain ⟨hS, hout, hna, hinv⟩ := ‹_ = Sa ∧ _ ∧ NoAbort _ ∧ ULoop G t S v u b0 B0 _ _ _›
    have hblk := ‹¬ _ = true›
    simp +zetaDelta only at hblk ⊢
    exact ⟨hS, hout, hna, uloop_skip hinv (by simpa using hblk)⟩
  case vc5.pre =>
    -- u is unblocked and its B-list emptied
    obtain ⟨hb, hB, hout, hS, hna, pre⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ ∧ _ = Sa ∧ NoAbort _ ∧ UPre G t S v u d b0 B0›
    simp +zetaDelta only
    rw [hb, hB]
    exact ⟨hS, by simp [hout], by simp [hna, Ev.isAbort], uloop_init pre⟩
  case vc6.post.success =>
    -- all entries processed
    obtain ⟨-, hB, -, -, -, -⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ ∧ _ = Sa ∧ NoAbort _ ∧ UPre G t S v u d b0 B0›
    obtain ⟨hS, hout, hna, hinv⟩ := ‹_ = Sa ∧ _ ∧ NoAbort _ ∧ ULoop G t S v u b0 B0 _ _ _›
    simp +zetaDelta only at hinv
    rw [hB] at hinv
    exact ⟨hS, hout, hna, uloop_final hinv⟩
termination_by n - d

end Johnson
