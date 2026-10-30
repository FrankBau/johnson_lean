/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Unblock

/-!
  Soundness and completeness of Johnson's algorithm (Corollary 1 and Lemma 2 of Johnson 1975, for s-t paths): every output is
  a simple s-t path, and every simple s-t path is output exactly once.

  One spec for `search v h` carries the global invariant `Inv` from the call to the return, together with Call Completeness
  (every simple s-t path extending the stack is output by the call), the return value (found iff the call made an output), and
  for a failed call that nothing got unblocked.  Soundness rests on clause (A) of `Inv`: a vertex on the stack is blocked, so
  `search` is never called for one.  Completeness rests on `Inv.dead`: a blocked vertex off the stack cannot reach t avoiding
  the stack.  No-duplicate output comes from the prefixes: outputs of different successors differ at position h + 1.
-/

open Std.Do

set_option mvcgen.warning false

namespace Johnson

variable {n : Nat}

/-! ## The spec of `search` -/

section
variable (G : Graph n) (s t : Fin n)

/-- precondition of `search v h` with stack S0, blocked flags bl0 and B-lists B0 -/
structure SearchPre (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (bl0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) : Prop where
  stack : StackPath G s t (S0.toList ++ [v])
  size : S0.size = h
  free : bl0[v] = false
  inv : Inv G t S0.toList bl0 B0

/-- what `search v h` guarantees: N are its outputs, r its return value, bl and B the state at its return -/
structure SearchPost (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (bl0 : Vector Bool n) (r : Bool) (bl : Vector Bool n) (B : Vector (List (Fin n)) n) (N : List (List (Fin n))) : Prop where
  nodup : G.WF → N.Nodup
  sound : ∀ p ∈ N, G.SimplePath s t p ∧ (S0.toList ++ [v]) <+: p                       -- Corollary 1
  complete : ∀ p, G.SimplePath s t p → (S0.toList ++ [v]) <+: p → p ∈ N                -- Call Completeness
  ret : r = true ↔ N ≠ []
  inv : Inv G t S0.toList bl B
  fail : r = false → (∀ x : Fin n, bl0[x] = true → bl[x] = true) ∧ bl[v] = true

/-- invariant of the successor loop (L1) of `search v h` after the successors pref -/
structure LoopInv (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (bl0 : Vector Bool n) (pref : List (Fin n)) (found : Bool) (bl : Vector Bool n) (B : Vector (List (Fin n)) n) (N : List (List (Fin n))) : Prop where
  nodup : G.WF → N.Nodup
  sound : ∀ p ∈ N, G.SimplePath s t p ∧ ∃ w ∈ pref, (S0.toList ++ [v, w]) <+: p
  complete : ∀ p, G.SimplePath s t p → ∀ w ∈ pref, (S0.toList ++ [v, w]) <+: p → p ∈ N
  ret : found = true ↔ N ≠ []
  inv : Inv G t (S0.toList ++ [v]) bl B
  fail : found = false → (∀ x : Fin n, bl0[x] = true → bl[x] = true) ∧ ∀ w ∈ pref, bl[w] = true

end

/-- invariant of the loop of the failed return (L2), after the successors pref: v is on their B-lists -/
structure FailInv (v : Fin n) (B0 : Vector (List (Fin n)) n) (pref : List (Fin n)) (B : Vector (List (Fin n)) n) : Prop where
  mem : ∀ w x : Fin n, x ∈ B[w] ↔ x ∈ B0[w] ∨ (x = v ∧ w ∈ pref)
  nodup : ∀ w : Fin n, (B[w]).Nodup

section steps
variable {G : Graph n} {s t : Fin n} {h : Nat} {v : Fin n} {S0 : Array (Fin n)} {bl0 : Vector Bool n} {B0 : Vector (List (Fin n)) n}

theorem push_append (S0 : Array (Fin n)) (v w : Fin n) : (S0.push v).toList ++ [w] = S0.toList ++ [v, w] := by simp

theorem SearchPre.v_not_mem (pre : SearchPre G s t h v S0 bl0 B0) : v ∉ S0.toList := pre.stack.v_not_mem

theorem SearchPre.t_not_mem (pre : SearchPre G s t h v S0 bl0 B0) : t ∉ S0.toList ++ [v] := pre.stack.2.2.1

theorem SearchPre.length (pre : SearchPre G s t h v S0 bl0 B0) : S0.toList.length = h := by simpa using pre.size

/-- the depth guard: the stack S0 ++ [v] has no duplicates -/
theorem SearchPre.depth (pre : SearchPre G s t h v S0 bl0 B0) : h < n := by
  have := nodup_length_le _ pre.stack.2.1
  simp [pre.length] at this
  omega

theorem loop_init (pre : SearchPre G s t h v S0 bl0 B0) : LoopInv G s t h v S0 bl0 [] false (bl0.set v.1 true v.2) B0 [] where
  nodup := fun _ => List.nodup_nil
  sound := by simp
  complete := by simp
  ret := by simp
  inv := pre.inv.push pre.free pre.v_not_mem (fun h' => pre.t_not_mem (by simp [h']))
  fail := by
    intro _
    refine ⟨?_, by simp⟩
    intro x hx
    by_cases hxv : x = v
    · subst hxv; simp
    · rw [vget_set_ne _ _ hxv]; exact hx

/-- the closing edge (v, t): output S0 ++ [v, t] -/
theorem loop_output (pre : SearchPre G s t h v S0 bl0 B0) {pref : List (Fin n)} {found : Bool} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} (hinv : LoopInv G s t h v S0 bl0 pref found bl B N) (hmem : t ∈ G.succ v) (htp : G.WF → t ∉ pref) :
    LoopInv G s t h v S0 bl0 (pref ++ [t]) true bl B (N ++ [S0.toList ++ [v, t]]) := by
  have hb0 : G.SimplePath s t (S0.toList ++ [v, t]) := by simpa using StackPath.simple pre.stack hmem
  refine { hinv with nodup := ?_, sound := ?_, complete := ?_, ret := by simp, fail := by simp }
  · intro hG
    refine List.nodup_append.mpr ⟨hinv.nodup hG, by simp, ?_⟩
    intro a ha c hc heq
    simp at hc; subst hc; subst heq
    obtain ⟨_, w', hw', hpre⟩ := hinv.sound _ ha
    have := eq_of_prefix_pair hpre (List.prefix_refl _)
    subst this; exact htp hG hw'
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
      exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
    · simp at hp; subst hp
      exact ⟨hb0, t, by simp, List.prefix_refl _⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact List.mem_append_left _ (hinv.complete p hp w' hw' hpre)
    · simp at hw'; subst hw'
      rw [hp.eq_of_prefix_t hpre]; simp

/-- a blocked successor w ≠ t: no simple path continues the stack with w -/
theorem loop_blocked {pref : List (Fin n)} {found : Bool} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} {w : Fin n} (hinv : LoopInv G s t h v S0 bl0 pref found bl B N) (hwb : bl[w] = true) :
    LoopInv G s t h v S0 bl0 (pref ++ [w]) found bl B N := by
  refine { hinv with sound := ?_, complete := ?_, fail := ?_ }
  · intro p hp
    obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
    exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact hinv.complete p hp w' hw' hpre
    · simp at hw'; subst hw'
      by_cases hwS : w' ∈ S0.toList ++ [v]
      · exact absurd hpre (hp.not_prefix_of_mem hwS)
      · exfalso
        have hwalk := hp.suffix_walk (by simpa using hpre : (S0.toList ++ [v] ++ [w']) <+: p)
        exact hinv.inv.dead hwb hwS ⟨_, hwalk.mono (fun z hz => List.mem_append_left _ hz)⟩
  · intro hf
    obtain ⟨h1, h2⟩ := hinv.fail hf
    refine ⟨h1, fun w' hw' => ?_⟩
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact h2 w' hw'
    · simp at hw'; subst hw'; exact hwb

/-- an unblocked successor is off the stack: (A) -/
theorem LoopInv.not_mem {pref : List (Fin n)} {found : Bool} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} {w : Fin n} (hinv : LoopInv G s t h v S0 bl0 pref found bl B N) (hwb : bl[w] = false) :
    w ∉ S0.toList ++ [v] := fun hw => by rw [hinv.inv.stack w hw] at hwb; cases hwb

/-- an unblocked successor w ≠ t: the precondition of the call `search w (h + 1)` -/
theorem loop_child_pre (pre : SearchPre G s t h v S0 bl0 B0) {pref : List (Fin n)} {found : Bool} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} {w : Fin n} (hinv : LoopInv G s t h v S0 bl0 pref found bl B N) (hmem : w ∈ G.succ v) (hwt : w ≠ t) (hwb : bl[w] = false) :
    SearchPre G s t (h + 1) w (S0.push v) bl B where
  stack := by rw [Array.toList_push]; exact StackPath.snoc pre.stack hmem (hinv.not_mem hwb) hwt
  size := by simp [pre.size]
  free := hwb
  inv := by rw [Array.toList_push]; exact hinv.inv

/-- back from the call `search w (h + 1)` -/
theorem loop_child_post {pref : List (Fin n)} {found r : Bool} {bl bl' : Vector Bool n} {B B' : Vector (List (Fin n)) n} {N Nc : List (List (Fin n))} {w : Fin n}
    (hinv : LoopInv G s t h v S0 bl0 pref found bl B N) (hwp : G.WF → w ∉ pref) (hpost : SearchPost G s t (h + 1) w (S0.push v) bl r bl' B' Nc) :
    LoopInv G s t h v S0 bl0 (pref ++ [w]) (found || r) bl' B' (N ++ Nc) := by
  have hsnd : ∀ p ∈ Nc, G.SimplePath s t p ∧ (S0.toList ++ [v, w]) <+: p := by
    intro p hp; have := hpost.sound p hp; rw [push_append] at this; exact this
  refine { nodup := ?_, sound := ?_, complete := ?_, ret := ?_, inv := ?_, fail := ?_ }
  · intro hG
    refine List.nodup_append.mpr ⟨hinv.nodup hG, hpost.nodup hG, ?_⟩
    intro a ha c hc heq
    subst heq
    obtain ⟨_, w', hw', hpre⟩ := hinv.sound a ha
    have := eq_of_prefix_pair hpre (hsnd a hc).2
    subst this; exact hwp hG hw'
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
      exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
    · exact ⟨(hsnd p hp).1, w, by simp, (hsnd p hp).2⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact List.mem_append_left _ (hinv.complete p hp w' hw' hpre)
    · simp at hw'; subst hw'
      exact List.mem_append_right _ (hpost.complete p hp (by rw [push_append]; exact hpre))
  · rw [Bool.or_eq_true, hinv.ret, hpost.ret]
    constructor
    · rintro (h1 | h1) heq <;> simp_all
    · intro h1
      by_cases hN : N = []
      · right; subst hN; simpa using h1
      · left; exact hN
  · have := hpost.inv; rw [Array.toList_push] at this; exact this
  · intro hf
    simp only [Bool.or_eq_false_iff] at hf
    obtain ⟨g1, g2⟩ := hinv.fail hf.1
    obtain ⟨k1, k2⟩ := hpost.fail hf.2
    refine ⟨fun x hx => k1 x (g1 x hx), fun w' hw' => ?_⟩
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact k1 w' (g2 w' hw')
    · simp at hw'; subst hw'; exact k2

/-- every simple path with prefix S0 ++ [v] continues with a successor of v -/
theorem LoopInv.complete' (pre : SearchPre G s t h v S0 bl0 B0) {found : Bool} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} (hinv : LoopInv G s t h v S0 bl0 (G.succ v) found bl B N) (p : List (Fin n)) (hp : G.SimplePath s t p) (hpre : (S0.toList ++ [v]) <+: p) : p ∈ N := by
  obtain ⟨w, rest, rfl, hw⟩ := hp.cont hpre pre.t_not_mem
  exact hinv.complete _ hp w hw ⟨rest, by simp⟩

/-- the precondition of UNBLOCK(v) at the fruitful return: v reaches t avoiding S0, along one of its outputs -/
theorem loop_upre (pre : SearchPre G s t h v S0 bl0 B0) {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} (hinv : LoopInv G s t h v S0 bl0 (G.succ v) true bl B N) :
    UPre G t S0.toList v v 0 bl B where
  nd := pre.stack.2.1
  reach := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (hinv.ret.mp rfl)
    obtain ⟨hb, w, _, hpre⟩ := hinv.sound p hp
    exact ⟨_, (hb.suffix_walk (prefix_of_pair hpre)).mono (fun z hz => List.mem_append_left _ hz)⟩
  blk := hinv.inv.stack v (by simp)
  pos := Or.inl rfl
  vfree := fun h' => absurd rfl h'
  inv := hinv.inv.binv
  deep := ⟨[], by simp, rfl, by simp⟩

/-- the fruitful return: after UNBLOCK(v) -/
theorem post_found (pre : SearchPre G s t h v S0 bl0 B0) {bl bl' : Vector Bool n} {B B' : Vector (List (Fin n)) n} {N : List (List (Fin n))} (hinv : LoopInv G s t h v S0 bl0 (G.succ v) true bl B N) (hc : UPost G t S0.toList v v bl B bl' B') :
    SearchPost G s t h v S0 bl0 true bl' B' N where
  nodup := hinv.nodup
  sound := fun p hp => by obtain ⟨hb, w, _, hpre⟩ := hinv.sound p hp; exact ⟨hb, prefix_of_pair hpre⟩
  complete := hinv.complete' pre
  ret := hinv.ret
  inv := hinv.inv.chain pre.v_not_mem hc.chainPost
  fail := by simp

theorem fail_init (B : Vector (List (Fin n)) n) (hnd : ∀ w : Fin n, (B[w]).Nodup) : FailInv v B [] B :=
  ⟨by simp, hnd⟩

/-- the failed return, v ∉ B[w]: v is appended to B[w] -/
theorem fail_add {B0 B : Vector (List (Fin n)) n} {pref : List (Fin n)} {w : Fin n} (hf : FailInv v B0 pref B) (hv : v ∉ B[w]) :
    FailInv v B0 (pref ++ [w]) (B.set w.1 (B[w] ++ [v]) w.2) := by
  refine ⟨?_, ?_⟩
  · intro w' x
    by_cases hw : w' = w
    · subst hw
      rw [vget_set_self, List.mem_append, hf.mem]
      simp only [List.mem_singleton, List.mem_append]
      constructor
      · rintro ((h1 | ⟨h1, h2⟩) | h1)
        · exact Or.inl h1
        · exact Or.inr ⟨h1, Or.inl h2⟩
        · exact Or.inr ⟨h1, Or.inr trivial⟩
      · rintro (h1 | ⟨h1, -⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inr h1
    · rw [vget_set_ne _ _ hw, hf.mem]
      simp [hw]
  · intro w'
    by_cases hw : w' = w
    · subst hw; rw [vget_set_self]; exact nodup_snoc (hf.nodup w') hv
    · rw [vget_set_ne _ _ hw]; exact hf.nodup w'

/-- the failed return, v ∈ B[w]: nothing changes -/
theorem fail_skip {B0 B : Vector (List (Fin n)) n} {pref : List (Fin n)} {w : Fin n} (hf : FailInv v B0 pref B) (hv : v ∈ B[w]) :
    FailInv v B0 (pref ++ [w]) B := by
  refine ⟨?_, hf.nodup⟩
  intro w' x
  rw [hf.mem]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨h1, List.mem_append_left _ h2⟩
  · rintro (h1 | ⟨rfl, h2⟩)
    · exact Or.inl h1
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact Or.inr ⟨rfl, h2⟩
      · simp at h2; subst h2; exact (hf.mem w' x).mp hv

/-- the failed return: v goes on the B-lists of its successors -/
theorem post_fail (pre : SearchPre G s t h v S0 bl0 B0) {bl : Vector Bool n} {B B' : Vector (List (Fin n)) n} {N : List (List (Fin n))} (hinv : LoopInv G s t h v S0 bl0 (G.succ v) false bl B N) (hf : FailInv v B (G.succ v) B') :
    SearchPost G s t h v S0 bl0 false bl B' N where
  nodup := hinv.nodup
  sound := fun p hp => by obtain ⟨hb, w, _, hpre⟩ := hinv.sound p hp; exact ⟨hb, prefix_of_pair hpre⟩
  complete := hinv.complete' pre
  ret := hinv.ret
  inv := hinv.inv.fail pre.v_not_mem (hinv.fail rfl).2 hf.mem hf.nodup
  fail := fun _ => ⟨(hinv.fail rfl).1, hinv.inv.stack v (by simp)⟩

end steps

/-! ## The induction over the calls -/

/-- spec of `search v h`: Call Completeness, the return value and the invariant; induction on n - h -/
theorem search_spec (G : Graph n) (s t : Fin n) (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (bl0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (O0 : List (List (Fin n))) :
    ⦃fun st => ⌜st.S = S0 ∧ st.blocked = bl0 ∧ st.B = B0 ∧ outputs st.trace.toList = O0 ∧ NoAbort st.trace ∧ SearchPre G s t h v S0 bl0 B0⌝⦄
    search G t v h
    ⦃⇓ r st => ⌜st.S = S0 ∧ NoAbort st.trace ∧ ∃ N, outputs st.trace.toList = O0 ++ N ∧ SearchPost G s t h v S0 bl0 r st.blocked st.B N⌝⦄ := by
  -- spec of the recursive call; vacuous unless h + 1 < n
  have ih : ∀ w (S1 : Array (Fin n)) (bl1 : Vector Bool n) (B1 : Vector (List (Fin n)) n) (O1 : List (List (Fin n))),
      ⦃fun st => ⌜st.S = S1 ∧ st.blocked = bl1 ∧ st.B = B1 ∧ outputs st.trace.toList = O1 ∧ NoAbort st.trace ∧ SearchPre G s t (h + 1) w S1 bl1 B1⌝⦄
      search G t w (h + 1)
      ⦃⇓ r st => ⌜st.S = S1 ∧ NoAbort st.trace ∧ ∃ N, outputs st.trace.toList = O1 ++ N ∧ SearchPost G s t (h + 1) w S1 bl1 r st.blocked st.B N⌝⦄ := by
    intro w S1 bl1 B1 O1
    by_cases hh : h + 1 < n
    · exact search_spec G s t (h + 1) w S1 bl1 B1 O1
    · intro st hP
      exact absurd hP.2.2.2.2.2.depth hh
  have hub := unblock_spec G t S0.toList v (S0.push v) v 0
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.isBlocked, M.setBlocked, M.blist, M.setBlist, M.stack, ih, hub] invariants
  · ⇓⟨xs, found⟩ st => ⌜st.S = S0.push v ∧ NoAbort st.trace ∧ ∃ N, outputs st.trace.toList = O0 ++ N ∧ LoopInv G s t h v S0 bl0 xs.prefix found st.blocked st.B N⌝
  · ⇓⟨xs, _⟩ st => ⌜st.S = S0.push v ∧ NoAbort st.trace ∧ ∃ N Bs, outputs st.trace.toList = O0 ++ N ∧ LoopInv G s t h v S0 bl0 (G.succ v) false st.blocked Bs N ∧ FailInv v Bs xs.prefix st.B⌝
  case vc1.step.isTrue =>
    -- closing edge (v, t): output S0 ++ [v, t]
    obtain ⟨-, -, -, -, -, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    obtain ⟨hS, hna, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    have hmem := mem_of_eq_append_cons hsplit
    have hcur := ‹_ = t›
    simp +zetaDelta only
    subst hcur
    refine ⟨hS, by simp [hna, Ev.isAbort], N ++ [S0.toList ++ [v, _]], ?_, loop_output pre hinv hmem (fun hG => not_mem_of_nodup_split (hG v) hsplit)⟩
    simp [hN, hS]
  case vc2.step.isFalse.isTrue.isTrue.pre =>
    -- recursive call: its precondition
    obtain ⟨-, -, -, -, -, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    obtain ⟨hS, hna, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have hnt := ‹¬_ = t›
    have hfree := ‹(!_) = true›
    simp +zetaDelta only at hfree ⊢
    rw [hS]
    exact ⟨trivial, trivial, trivial, trivial, hna, loop_child_pre pre hinv hmem hnt (by simpa using hfree)⟩
  case vc3.step.isFalse.isTrue.isTrue.post.success =>
    -- recursive call: back in the loop
    obtain ⟨hS, -, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    obtain ⟨hS', hna', Nc, hNc, hpost⟩ := ‹_ ∧ NoAbort _ ∧ ∃ N, _ ∧ SearchPost G s t (h + 1) _ _ _ _ _ _ N›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    simp +zetaDelta only at hS' hNc hpost ⊢
    rw [hS] at hS' hpost
    exact ⟨hS', hna', N ++ Nc, by rw [hNc, hN, List.append_assoc], loop_child_post hinv (fun hG => not_mem_of_nodup_split (hG v) hsplit) hpost⟩
  case vc4.step.isFalse.isTrue.isFalse =>
    -- the depth guard fails: impossible
    obtain ⟨-, -, -, -, -, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    obtain ⟨-, -, N, -, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have hnt := ‹¬_ = t›
    have hfree := ‹(!_) = true›
    have hh := ‹¬ h + 1 < n›
    simp +zetaDelta only at hfree
    exact absurd (loop_child_pre pre hinv hmem hnt (by simpa using hfree)).depth hh
  case vc5.step.isFalse.isFalse =>
    -- blocked successor
    obtain ⟨hS, hna, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    have hblk := ‹¬(!_) = true›
    simp +zetaDelta only at hblk ⊢
    exact ⟨hS, hna, N, hN, loop_blocked hinv (by simpa using hblk)⟩
  case vc6.pre =>
    -- entry: push v and block it
    obtain ⟨hS, hb, hB, hout, hna, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    simp +zetaDelta only
    rw [hS, hb, hB]
    exact ⟨rfl, by simp [hna, Ev.isAbort], [], by simp [hout], loop_init pre⟩
  case vc7.post.success.isTrue.pre =>
    -- fruitful: the precondition of UNBLOCK(v)
    obtain ⟨-, -, -, -, -, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    obtain ⟨hS, hna, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    have hf := ‹_ = true›
    subst hf
    exact ⟨trivial, trivial, trivial, hS, hna, loop_upre pre hinv⟩
  case vc8.post.success.isTrue.post.success =>
    -- fruitful: after UNBLOCK(v), exit and pop
    obtain ⟨-, -, -, -, -, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    obtain ⟨-, -, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    obtain ⟨hS', hout', hna', hpost⟩ := ‹_ = S0.push v ∧ _ ∧ NoAbort _ ∧ UPost G t S0.toList v v _ _ _ _›
    have hf := ‹_ = true›
    subst hf
    simp +zetaDelta only
    rw [hS']
    exact ⟨by simp, by simp [hna', Ev.isAbort], N, by simp [hout', hN], post_found pre hinv hpost⟩
  case vc9.step.isTrue =>
    -- failed return: v goes on B[w]
    obtain ⟨hS, hna, N, Bs, hN, hinv, hf⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N Bs, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ Bs N ∧ FailInv v Bs _ _›
    have hv := ‹¬ v ∈ _›
    simp +zetaDelta only at hv ⊢
    exact ⟨hS, hna, N, Bs, hN, hinv, fail_add hf hv⟩
  case vc10.step.isFalse =>
    -- failed return: v is on B[w] already
    obtain ⟨hS, hna, N, Bs, hN, hinv, hf⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N Bs, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ Bs N ∧ FailInv v Bs _ _›
    have hv := ‹¬¬ v ∈ _›
    simp +zetaDelta only at hv ⊢
    exact ⟨hS, hna, N, Bs, hN, hinv, fail_skip hf (by simpa using hv)⟩
  case vc11.post.success.isFalse.pre =>
    -- failed return: start of the loop over the successors
    obtain ⟨hS, hna, N, hN, hinv⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ _ N›
    have hf := ‹¬ _ = true›
    simp only [Bool.not_eq_true] at hf
    subst hf
    exact ⟨hS, hna, N, _, hN, hinv, fail_init _ hinv.inv.nodup⟩
  case vc12.post.success.isFalse.post.success =>
    -- failed return: exit and pop
    obtain ⟨-, -, -, -, -, pre⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ ∧ NoAbort _ ∧ SearchPre G s t h v S0 bl0 B0›
    obtain ⟨hS, hna, N, Bs, hN, hinv, hf⟩ := ‹_ = S0.push v ∧ NoAbort _ ∧ ∃ N Bs, _ ∧ LoopInv G s t h v S0 bl0 _ _ _ Bs N ∧ FailInv v Bs _ _›
    have hfound := ‹¬ _ = true›
    simp only [Bool.not_eq_true] at hfound
    subst hfound
    simp +zetaDelta only
    rw [hS]
    exact ⟨by simp, by simp [hna, Ev.isAbort], N, by simp [hN], post_fail pre hinv hf⟩
termination_by n - h

/-! ## Johnson's Lemma 1 -/

/-- Johnson's Lemma 1, for s-t paths: at the fruitful return of v from the stack S ++ [v], UNBLOCK(v) unblocks exactly those
    blocked vertices x off the stack that reach t avoiding S, (i), and none of these reaches t avoiding S ++ [v], (ii); so
    every such walk passes through v -/
theorem lemma1 {G : Graph n} {t : Fin n} {S : List (Fin n)} {v : Fin n} {bl0 bl1 : Vector Bool n} {B0 B1 : Vector (List (Fin n)) n}
    (hI : Inv G t (S ++ [v]) bl0 B0) (hvS : v ∉ S) (hc : ChainPost G t S v bl0 B0 bl1 B1) (x : Fin n) (hx : bl0[x] = true) (hxS : x ∉ S ++ [v]) :
    (bl1[x] = false ↔ G.Reach S t x) ∧ ¬ G.Reach (S ++ [v]) t x := by
  refine ⟨⟨fun h1 => ?_, fun hr => ?_⟩, hI.dead hx hxS⟩
  · rcases hc.off x hx h1 with rfl | ⟨_, hr⟩
    · exact absurd (by simp) hxS
    · exact hr
  · cases h1 : bl1[x]
    · rfl
    · exact absurd hr ((hI.chain hvS hc).dead h1 (fun h' => hxS (List.mem_append_left _ h')))

/-! ## The theorems -/

theorem root_pre {G : Graph n} {s t : Fin n} (hst : s ≠ t) : SearchPre G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []) where
  stack := ⟨rfl, by simp, by simpa using Ne.symm hst, by simp⟩
  size := rfl
  free := by simp
  inv := ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- the root call's spec gives properties of the run: its trace is the start event, the events of the root call, and the
    term event -/
theorem johnson_of_search (G : Graph n) (s t : Fin n) (hst : s ≠ t) (Q : List (Ev n) → Prop)
    (hQ : ∀ (T : Array (Ev n)) σ r bl B N, NoAbort T → outputs T.toList = N → SearchPost G s t 0 s #[] (Vector.replicate n false) r bl B N → Q (T.toList ++ [Ev.term σ])) : Q (johnson G s t) := by
  refine johnson_of_root (fun st => st.S = #[] ∧ st.blocked = Vector.replicate n false ∧ st.B = Vector.replicate n [] ∧ outputs st.trace.toList = [] ∧ NoAbort st.trace ∧ SearchPre G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []))
    Q ⟨rfl, rfl, rfl, rfl, by simp [NoAbort, Ev.isAbort], root_pre hst⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  obtain ⟨-, hna, N, hN, hpost⟩ := (StateM.triple_iff _ _ _).mp (search_spec G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []) []) st hpre
  exact hQ _ _ _ _ _ N hna (by simpa using hN) hpost

variable (G : Graph n) (s t : Fin n)

/-- soundness (Johnson's Corollary 1): every output is a simple s-t path -/
theorem johnson_sound (hst : s ≠ t) : ∀ p ∈ outputs (johnson G s t), G.SimplePath s t p := by
  refine johnson_of_search G s t hst (fun tr => ∀ p ∈ outputs tr, G.SimplePath s t p) (fun T σ r bl B N _ hN hpost => ?_)
  intro p hp
  simp only [outputs_append, hN] at hp
  simp at hp
  exact (hpost.sound p hp).1

/-- completeness (Johnson's Lemma 2): every simple s-t path is output exactly once -/
theorem johnson_complete_once (hG : G.WF) (hst : s ≠ t) : ∀ p, G.SimplePath s t p → (outputs (johnson G s t)).count p = 1 := by
  refine johnson_of_search G s t hst (fun tr => ∀ p, G.SimplePath s t p → (outputs tr).count p = 1) (fun T σ r bl B N _ hN hpost => ?_)
  intro p hp
  have hout : outputs (T.toList ++ [Ev.term σ]) = N := by simp [hN]
  rw [hout]
  -- every simple path starts with s, so it has the prefix [s] of the root call
  exact (hpost.nodup hG).count_of_mem (hpost.complete p hp (by simpa using prefix_of_head hp.1))

/-- the depth guards never fail: the run has no `abort` event, so it is the run of Johnson's algorithm without them -/
theorem johnson_guards_vacuous (hst : s ≠ t) : ∀ e ∈ johnson G s t, e.isAbort = false := by
  refine johnson_of_search G s t hst (fun tr => ∀ e ∈ tr, e.isAbort = false) (fun T σ r bl B N hna _ _ => ?_)
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hna e he
  · simp at he; subst he; rfl

end Johnson
