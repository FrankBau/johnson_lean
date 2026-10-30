/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.RunFacts

/-!
  The trace facts of the run, as Hoare specs extending `unblock_spec` and `search_spec` (same `mvcgen` cases, the same step
  lemmas for the invariant).  The UNBLOCK chain appends unblock events only, each with its facts (`TrUnb`).  A call of
  `search v h` emits its entry, the events of its loop (outputs and the complete traces of its child calls), the UNBLOCK chain
  if it is fruitful, and its exit (`TrCall`).  Every position of this segment satisfies `PosOK`; the entry gets its `CallOK`,
  and the chain events their `ChainAt`, at the exit.  Adapted from the BS-DFS formalization (Bsdfs/RunSearch.lean).
-/

open Std.Do

set_option mvcgen.warning false

namespace Johnson

open Trace

variable {n : Nat}

/-! ## The UNBLOCK chain -/

/-- the trace facts of an UNBLOCK chain on the stack Sl, from the trace T0 to T: only unblock events are appended, each with
    its facts; the stack stays Sl; the replay of the blocked flags ends at b -/
structure TrUnb (G : Graph n) (s t : Fin n) (Sl : List (Fin n)) (T0 T : List (Ev n)) (b : Vector Bool n) : Prop where
  ext : ∃ E, T = T0 ++ E ∧ ∀ e ∈ E, ∃ σ u L, e = .unblock σ u L
  stk : ∀ q, T0.length ≤ q → q ≤ T.length → stk T q = Sl
  ev : ∀ q, T0.length ≤ q → q < T.length → EvOK G s t T q
  blk_now : ∀ z, blk T T.length z = b[z]

section unb
variable {G : Graph n} {s t : Fin n} {S : List (Fin n)} {v : Fin n}

theorem TrUnb.len {Sl : List (Fin n)} {T0 T : List (Ev n)} {b : Vector Bool n} (tu : TrUnb G s t Sl T0 T b) : T0.length ≤ T.length := by
  obtain ⟨E, hE, -⟩ := tu.ext; rw [hE]; simp

/-- the unblock event of u, right after u is unblocked and its B-list emptied -/
theorem tu_init {u : Fin n} {d : Nat} {b0 : Vector Bool n} {B0 : Vector (List (Fin n)) n} {T0 : List (Ev n)} (h : UPre G t S v u d b0 B0)
    (hstk : stk T0 T0.length = S ++ [v]) (hblk : ∀ z, blk T0 T0.length z = b0[z]) {σ : Nat} :
    TrUnb G s t (S ++ [v]) T0 (T0 ++ [.unblock σ u B0[u]]) (b0.set u.1 false u.2) := by
  have hvS : v ∉ S := fun hv => (List.nodup_append.mp h.nd).2.2 v hv v (by simp) rfl
  refine ⟨⟨[.unblock σ u B0[u]], rfl, by simp⟩, ?_, ?_, ?_⟩
  · intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rcases Nat.eq_or_lt_of_le h1 with hq | hq
    · subst hq; rw [Trace.stk_append (Nat.le_refl _)]; exact hstk
    · rw [show q = T0.length + 1 by omega, Trace.stk_snoc_other (by intros; simp) (by intros; simp), hstk]
  · intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rw [show q = T0.length by omega]
    simp only [EvOK, List.getElem?_concat_length]
    rw [Trace.stk_append (Nat.le_refl _), hstk]
    simp only [Trace.blk_append (Nat.le_refl _), hblk]
    have hpos : u ∉ S ∧ G.Reach S t u := by
      rcases h.pos with rfl | ⟨hu, hr⟩
      · exact ⟨hvS, h.reach⟩
      · exact ⟨fun h' => hu (List.mem_append_left _ h'), hr⟩
    exact ⟨h.blk, h.inv.nodup u, fun x hx => h.inv.edge u x hx, by simpa using hpos.1, by simpa using hpos.2⟩
  · intro z
    simp only [List.length_append, List.length_singleton]
    rw [Trace.blk_snoc_unblock, hblk]
    by_cases hz : u = z
    · subst hz; simp
    · rw [vget_set_ne _ _ (Ne.symm hz)]; simp [hz]

/-- after a nested call: its events are appended -/
theorem tu_child {Sl : List (Fin n)} {T0 T T' : List (Ev n)} {b b' : Vector Bool n} (tu : TrUnb G s t Sl T0 T b) (tc : TrUnb G s t Sl T T' b') : TrUnb G s t Sl T0 T' b' := by
  obtain ⟨E, hE, hEu⟩ := tu.ext
  obtain ⟨E', hE', hE'u⟩ := tc.ext
  have hlen := tu.len
  refine ⟨⟨E ++ E', by rw [hE', hE]; simp, fun e he => ?_⟩, ?_, ?_, tc.blk_now⟩
  · rcases List.mem_append.mp he with he | he
    · exact hEu e he
    · exact hE'u e he
  · intro q h1 h2
    rcases Nat.lt_or_ge T.length q with hq | hq
    · exact tc.stk q (by omega) h2
    · rw [hE', Trace.stk_append hq]; exact tu.stk q h1 hq
  · intro q h1 h2
    rcases Nat.lt_or_ge q T.length with hq | hq
    · rw [hE']; exact (tu.ev q h1 hq).append hq
    · exact tc.ev q hq h2

end unb

/-- UNBLOCK spec with its trace facts (ghost equations first) -/
theorem unblock_spec_tr (G : Graph n) (s t : Fin n) (S : List (Fin n)) (v : Fin n) (Sa : Array (Fin n)) (u : Fin n) (d : Nat) (b0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (T0 : List (Ev n)) :
    ⦃fun st => ⌜st.blocked = b0 ∧ st.B = B0 ∧ st.trace.toList = T0 ∧ st.S = Sa ∧ UPre G t S v u d b0 B0 ∧ Sa.toList = S ++ [v] ∧ stk T0 T0.length = S ++ [v] ∧ ∀ z, blk T0 T0.length z = b0[z]⌝⦄
    unblock u d
    ⦃⇓ _ st => ⌜st.S = Sa ∧ UPost G t S v u b0 B0 st.blocked st.B ∧ TrUnb G s t (S ++ [v]) T0 st.trace.toList st.blocked⌝⦄ := by
  -- spec of the nested call; vacuous unless d + 1 < n
  have ih : ∀ w (b1 : Vector Bool n) (B1 : Vector (List (Fin n)) n) (T1 : List (Ev n)),
      ⦃fun st => ⌜st.blocked = b1 ∧ st.B = B1 ∧ st.trace.toList = T1 ∧ st.S = Sa ∧ UPre G t S v w (d + 1) b1 B1 ∧ Sa.toList = S ++ [v] ∧ stk T1 T1.length = S ++ [v] ∧ ∀ z, blk T1 T1.length z = b1[z]⌝⦄
      unblock w (d + 1)
      ⦃⇓ _ st => ⌜st.S = Sa ∧ UPost G t S v w b1 B1 st.blocked st.B ∧ TrUnb G s t (S ++ [v]) T1 st.trace.toList st.blocked⌝⦄ := by
    intro w b1 B1 T1
    by_cases hd : d + 1 < n
    · exact unblock_spec_tr G s t S v Sa w (d + 1) b1 B1 T1
    · intro st hP
      exact absurd hP.2.2.2.2.1.depth hd
  rw [unblock]
  mvcgen [M.tick, M.emit, M.steps, M.isBlocked, M.setBlocked, M.blist, M.setBlist, ih] invariants
  · ⇓⟨xs, _⟩ st => ⌜st.S = Sa ∧ ULoop G t S v u b0 B0 xs.prefix st.blocked st.B ∧ TrUnb G s t (S ++ [v]) T0 st.trace.toList st.blocked⌝
  case vc1.step.isTrue.isTrue.pre =>
    -- nested call: its precondition
    have hsplit := ‹_ = _ ++ _ :: _›
    have hblk := ‹_ = true›
    obtain ⟨-, hB, -, -, pre, hSa, -, -⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ = T0 ∧ _ = Sa ∧ UPre G t S v u d b0 B0 ∧ _›
    obtain ⟨hS, hinv, tu⟩ := ‹_ = Sa ∧ ULoop G t S v u b0 B0 _ _ _ ∧ TrUnb G s t (S ++ [v]) T0 _ _›
    simp +zetaDelta only at hsplit hblk ⊢
    rw [hB] at hsplit
    exact ⟨trivial, trivial, trivial, hS, uloop_child_pre pre hinv (mem_of_eq_append_cons hsplit) hblk, hSa, tu.stk _ tu.len (Nat.le_refl _), tu.blk_now⟩
  case vc2.step.isTrue.isTrue.post.success =>
    -- nested call: back in the loop
    obtain ⟨-, hinv, tu⟩ := ‹_ = Sa ∧ ULoop G t S v u b0 B0 _ _ _ ∧ TrUnb G s t (S ++ [v]) T0 _ _›
    obtain ⟨hS', hpost, tc⟩ := ‹_ = Sa ∧ UPost G t S v _ _ _ _ _ ∧ TrUnb G s t (S ++ [v]) _ _ _›
    simp +zetaDelta only at hpost tc
    exact ⟨hS', uloop_child_post hinv hpost, tu_child tu tc⟩
  case vc3.step.isTrue.isFalse =>
    -- the depth guard fails: impossible
    have hsplit := ‹_ = _ ++ _ :: _›
    have hblk := ‹_ = true›
    obtain ⟨-, hB, -, -, pre, -, -, -⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ = T0 ∧ _ = Sa ∧ UPre G t S v u d b0 B0 ∧ _›
    obtain ⟨-, hinv, -⟩ := ‹_ = Sa ∧ ULoop G t S v u b0 B0 _ _ _ ∧ TrUnb G s t (S ++ [v]) T0 _ _›
    have hd := ‹¬ d + 1 < n›
    simp +zetaDelta only at hsplit hblk
    rw [hB] at hsplit
    exact absurd (uloop_child_pre pre hinv (mem_of_eq_append_cons hsplit) hblk).depth hd
  case vc4.step.isFalse =>
    -- an entry that is already unblocked
    obtain ⟨hS, hinv, tu⟩ := ‹_ = Sa ∧ ULoop G t S v u b0 B0 _ _ _ ∧ TrUnb G s t (S ++ [v]) T0 _ _›
    have hblk := ‹¬ _ = true›
    simp +zetaDelta only at hblk ⊢
    exact ⟨hS, uloop_skip hinv (by simpa using hblk), tu⟩
  case vc5.pre =>
    -- u is unblocked, its B-list emptied, and the unblock event emitted
    obtain ⟨hb, hB, hT, hS, pre, -, hstk, hblk⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ = T0 ∧ _ = Sa ∧ UPre G t S v u d b0 B0 ∧ _›
    simp +zetaDelta only
    rw [hb, hB]
    refine ⟨hS, uloop_init pre, ?_⟩
    rw [Array.toList_push, hT]
    exact tu_init pre hstk hblk
  case vc6.post.success =>
    -- all entries processed
    obtain ⟨-, hB, -, -, -, -, -, -⟩ := ‹_ = b0 ∧ _ = B0 ∧ _ = T0 ∧ _ = Sa ∧ UPre G t S v u d b0 B0 ∧ _›
    obtain ⟨hS, hinv, tu⟩ := ‹_ = Sa ∧ ULoop G t S v u b0 B0 _ _ _ ∧ TrUnb G s t (S ++ [v]) T0 _ _›
    simp +zetaDelta only at hinv
    rw [hB] at hinv
    exact ⟨hS, uloop_final hinv, tu⟩
termination_by n - d

/-! ## Outputs of a segment -/

section outputs

/-- an output of the events after e0 sits at a position after e0 -/
theorem output_pos {T0 E : List (Ev n)} {e0 : Ev n} {p : List (Fin n)} (hp : p ∈ outputs E) : ∃ q σ, T0.length < q ∧ q < (T0 ++ e0 :: E).length ∧ (T0 ++ e0 :: E)[q]? = some (.output σ p) := by
  unfold outputs at hp
  obtain ⟨e, he, hep⟩ := List.mem_filterMap.mp hp
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
  cases e with
  | output σ p' =>
    simp only [Option.some.injEq] at hep
    subst hep
    refine ⟨T0.length + (i + 1), σ, by omega, by simp; omega, ?_⟩
    rw [List.getElem?_append_right (by omega), show T0.length + (i + 1) - T0.length = i + 1 by omega, List.getElem?_cons_succ, List.getElem?_eq_getElem hi, hei]
  | _ => simp at hep

/-- an output at a position after e0 belongs to the outputs of the events after e0 -/
theorem output_mem {T0 E : List (Ev n)} {e0 : Ev n} {q σ : Nat} {p : List (Fin n)} (h1 : T0.length < q) (hq : (T0 ++ e0 :: E)[q]? = some (.output σ p)) : p ∈ outputs E := by
  rw [List.getElem?_append_right (by omega)] at hq
  obtain ⟨j, hj⟩ : ∃ j, q - T0.length = j + 1 := ⟨q - T0.length - 1, by omega⟩
  rw [hj, List.getElem?_cons_succ] at hq
  unfold outputs
  exact List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hq, rfl⟩

theorem outputs_unb {E : List (Ev n)} (h : ∀ e ∈ E, ∃ σ u L, e = .unblock σ u L) : outputs E = [] := by
  unfold outputs
  rw [List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨σ, u, L, rfl⟩ := h e he
  rfl

end outputs

/-! ## The trace invariant of `search` -/

/-- what the trace facts of `search v h` need at its entry (T0 is the trace before the call) -/
structure TrPre (S0 : Array (Fin n)) (bl0 : Vector Bool n) (T0 : List (Ev n)) : Prop where
  stk : stk T0 T0.length = S0.toList
  blk : ∀ z, blk T0 T0.length z = bl0[z]

/-- the trace part of the loop invariant of `search v h`; T is the current trace, N the outputs so far, bl the blocked flags -/
structure TrLoop (G : Graph n) (s t : Fin n) (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (T0 : List (Ev n)) (N : List (List (Fin n))) (bl : Vector Bool n) (T : List (Ev n)) : Prop where
  ext : ∃ σ E, T = T0 ++ Ev.enter σ v h :: E ∧ outputs E = N
  stk0 : stk T T0.length = S0.toList
  stk_now : stk T T.length = (S0.push v).toList
  blk_now : ∀ z, blk T T.length z = bl[z]
  isOpen : ∀ q, T0.length < q → q ≤ T.length → (stk T q).take (S0.size + 1) = (S0.push v).toList
  ev0 : EvOK G s t T T0.length
  seg : ∀ q, T0.length < q → q < T.length → PosOK G s t T q

/-- what `search v h` guarantees about the trace: T0 before the call, T after it, N its outputs, bl the blocked flags at exit -/
structure TrCall (G : Graph n) (s t : Fin n) (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (T0 : List (Ev n)) (N : List (List (Fin n))) (bl : Vector Bool n) (T : List (Ev n)) : Prop where
  ext : ∃ σ E, T = T0 ++ Ev.enter σ v h :: E ∧ outputs E = N
  stk_now : stk T T.length = S0.toList
  blk_now : ∀ z, blk T T.length z = bl[z]
  seg : ∀ q, T0.length ≤ q → q < T.length → PosOK G s t T q
  call : CallOK G s t T T0.length (T.length - 1)

section steps
variable {G : Graph n} {s t : Fin n} {h : Nat} {v : Fin n} {S0 : Array (Fin n)} {bl0 : Vector Bool n} {B0 : Vector (List (Fin n)) n} {T0 : List (Ev n)}

theorem TrLoop.len {N : List (List (Fin n))} {bl : Vector Bool n} {T : List (Ev n)} (tl : TrLoop G s t h v S0 T0 N bl T) : T0.length < T.length := by
  obtain ⟨σ, E, hE, -⟩ := tl.ext; rw [hE]; simp

theorem TrLoop.enter {N : List (List (Fin n))} {bl : Vector Bool n} {T : List (Ev n)} (tl : TrLoop G s t h v S0 T0 N bl T) : ∃ σ, T[T0.length]? = some (.enter σ v h) := by
  obtain ⟨σ, E, hE, -⟩ := tl.ext; exact ⟨σ, by rw [hE]; simp⟩

/-- the entry: push v, block it, and the enter event -/
theorem tl_init (pre : SearchPre G s t h v S0 bl0 B0) (tp : TrPre S0 bl0 T0) {σ : Nat} : TrLoop G s t h v S0 T0 [] (bl0.set v.1 true v.2) (T0 ++ [.enter σ v h]) where
  ext := ⟨σ, [], rfl, rfl⟩
  stk0 := by rw [Trace.stk_append (Nat.le_refl _)]; exact tp.stk
  stk_now := by rw [List.length_append, List.length_singleton, Trace.stk_snoc_enter, tp.stk]; simp
  blk_now := fun z => by
    rw [List.length_append, List.length_singleton, Trace.blk_snoc_enter, tp.blk z]
    by_cases hz : v = z
    · subst hz; simp
    · rw [vget_set_ne _ _ (Ne.symm hz)]; simp [hz]
  isOpen := by
    intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rw [show q = T0.length + 1 by omega, Trace.stk_snoc_enter, tp.stk, List.take_of_length_le (by simp)]
    simp
  ev0 := by
    simp only [EvOK, List.getElem?_concat_length]
    rw [Trace.stk_append (Nat.le_refl _), tp.stk]
    simp only [Trace.blk_append (Nat.le_refl _), tp.blk]
    exact ⟨pre.length.symm, pre.v_not_mem, fun hvt => pre.t_not_mem (by simp [hvt]), pre.free, pre.stack⟩
  seg := by intro q h1 h2; simp at h2; omega

/-- the closing edge (v, t): the output S0 ++ [v, t] -/
theorem tl_output (pre : SearchPre G s t h v S0 bl0 B0) {pref : List (Fin n)} {found : Bool} {bl : Vector Bool n} {B : Vector (List (Fin n)) n} {N : List (List (Fin n))} {T : List (Ev n)}
    (hinv : LoopInv G s t h v S0 bl0 pref found bl B N) (tl : TrLoop G s t h v S0 T0 N bl T) {σ : Nat} :
    TrLoop G s t h v S0 T0 (N ++ [S0.toList ++ [v, t]]) bl (T ++ [.output σ (S0.toList ++ [v, t])]) := by
  have hlen0 := tl.len
  have hstk := Trace.stk_snoc_other (T := T) (e := .output σ (S0.toList ++ [v, t])) (by intros; simp) (by intros; simp)
  refine { ext := ?_, stk0 := ?_, stk_now := ?_, blk_now := ?_, isOpen := ?_, ev0 := ?_, seg := ?_ }
  · obtain ⟨σ0, E, hE, hN⟩ := tl.ext
    exact ⟨σ0, E ++ [.output σ (S0.toList ++ [v, t])], by rw [hE]; simp, by rw [outputs_append, hN]; simp [outputs]⟩
  · rw [Trace.stk_append (by omega)]; exact tl.stk0
  · rw [List.length_append, List.length_singleton, hstk, tl.stk_now]
  · intro z; rw [List.length_append, List.length_singleton, Trace.blk_snoc_other (by intros; simp) (by intros; simp), tl.blk_now z]
  · intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rcases Nat.lt_or_ge q (T.length + 1) with hq | hq
    · rw [Trace.stk_append (by omega)]; exact tl.isOpen q h1 (by omega)
    · rw [show q = T.length + 1 by omega, hstk, tl.stk_now, List.take_of_length_le (by simp)]
  · exact tl.ev0.append (by omega)
  · intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rcases Nat.lt_or_ge q T.length with hq | hq
    · exact (tl.seg q h1 hq).append hq
    · -- the output event
      rw [show q = T.length by omega]
      have hq' : (T ++ [Ev.output σ (S0.toList ++ [v, t])])[T.length]? = some (.output σ (S0.toList ++ [v, t])) := by simp
      refine ⟨?_, fun σ' v' h' he => (by rw [hq'] at he; cases he), fun σ' v' f he => (by rw [hq'] at he; cases he), fun σ' u L he => (by rw [hq'] at he; cases he)⟩
      simp only [EvOK, hq']
      rw [Trace.stk_append (Nat.le_refl _), tl.stk_now]
      simp only [Trace.blk_append (Nat.le_refl _), tl.blk_now]
      refine ⟨by simp, ?_, fun x hx => hinv.inv.stack x (by simpa using hx)⟩
      have := nodup_snoc pre.stack.2.1 pre.stack.2.2.1
      simpa using this

theorem tl_child_pre {N : List (List (Fin n))} {bl : Vector Bool n} {T : List (Ev n)} (tl : TrLoop G s t h v S0 T0 N bl T) : TrPre (S0.push v) bl T :=
  ⟨tl.stk_now, tl.blk_now⟩

/-- back from a child call at w: its trace is appended -/
theorem tl_child_post {N Nc : List (List (Fin n))} {bl bl' : Vector Bool n} {T T' : List (Ev n)} {w : Fin n}
    (tl : TrLoop G s t h v S0 T0 N bl T) (tc : TrCall G s t (h + 1) w (S0.push v) T Nc bl' T') :
    TrLoop G s t h v S0 T0 (N ++ Nc) bl' T' := by
  have hlen0 := tl.len
  obtain ⟨σc, Ec, hEc, hNc⟩ := tc.ext
  have hT'len : T'.length = T.length + 1 + Ec.length := by rw [hEc]; simp; omega
  have hT'e : T'[T.length]? = some (.enter σc w (h + 1)) := by rw [hEc]; simp
  have hfr := tc.call.frame
  refine { ext := ?_, stk0 := ?_, stk_now := tc.stk_now, blk_now := tc.blk_now, isOpen := ?_, ev0 := ?_, seg := ?_ }
  · obtain ⟨σ0, E, hE, hN⟩ := tl.ext
    refine ⟨σ0, E ++ Ev.enter σc w (h + 1) :: Ec, by rw [hEc, hE]; simp, ?_⟩
    rw [outputs_append, hN, ← hNc]; simp [outputs]
  · rw [hEc, Trace.stk_append (by omega)]; exact tl.stk0
  · intro q h1 h2
    rcases Nat.lt_or_ge T.length q with hq | hq
    · rcases Nat.lt_or_ge q T'.length with hq' | hq'
      · -- inside the child's frame: its stack starts with S0.push v
        have hp := hfr.prefix (q := q) hq (by omega)
        have he1 : stk T' (T.length + 1) = (S0.push v).toList ++ [w] := by
          rw [Trace.stk_succ_enter hT'e, hEc, Trace.stk_append (Nat.le_refl _), tl.stk_now]
        have he0 : (stk T' T.length).length = S0.size + 1 := by
          rw [hEc, Trace.stk_append (Nat.le_refl _), tl.stk_now]; simp
        rw [he1, he0] at hp
        have := congrArg (List.take (S0.size + 1)) hp
        rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' (by simp)] at this
        exact this
      · rw [show q = T'.length by omega, tc.stk_now, List.take_of_length_le (by simp)]
    · rw [hEc, Trace.stk_append hq]; exact tl.isOpen q h1 hq
  · rw [hEc]; exact tl.ev0.append (by omega)
  · intro q h1 h2
    rcases Nat.lt_or_ge q T.length with hq | hq
    · rw [hEc]; exact (tl.seg q h1 hq).append hq
    · exact tc.seg q hq h2

theorem le_length_of_take_eq {l l' : List (Fin n)} {m : Nat} (h : l.take m = l') (hl' : l'.length = m) : m ≤ l.length := by
  have := congrArg List.length h
  rw [List.length_take] at this
  omega

/-- the exit of `search v h` after its loop and the tail Etl (the UNBLOCK chain, or nothing): the call's facts and the
    segment's -/
theorem tl_exit {N : List (List (Fin n))} {bl : Vector Bool n} {T : List (Ev n)} (tl : TrLoop G s t h v S0 T0 N bl T)
    {Etl : List (Ev n)} {σx : Nat} {f : Bool} {bf : Vector Bool n} {Bf : Vector (List (Fin n)) n}
    (hunb : ∀ e ∈ Etl, ∃ σ u L, e = .unblock σ u L)
    (hstk : ∀ q, T.length ≤ q → q ≤ T.length + Etl.length → stk (T ++ Etl) q = (S0.push v).toList)
    (hev : ∀ q, T.length ≤ q → q < T.length + Etl.length → EvOK G s t (T ++ Etl) q)
    (hblk : ∀ z, blk (T ++ Etl) (T.length + Etl.length) z = bf[z])
    (hpost : SearchPost G s t h v S0 bl0 f bf Bf N) (hchain : Etl ≠ [] → f = true) :
    TrCall G s t h v S0 T0 N bf (T ++ Etl ++ [.exit σx v f]) := by
  have hlen0 := tl.len
  have hTE : (T ++ Etl).length = T.length + Etl.length := List.length_append
  have hlen : (T ++ Etl ++ [Ev.exit σx v f]).length = T.length + Etl.length + 1 := by simp; omega
  have hassoc : T ++ Etl ++ [Ev.exit σx v f] = T ++ (Etl ++ [Ev.exit σx v f]) := List.append_assoc _ _ _
  have hx : (T ++ Etl ++ [Ev.exit σx v f])[T.length + Etl.length]? = some (.exit σx v f) := by rw [← hTE]; simp
  have hstkx : stk (T ++ Etl ++ [Ev.exit σx v f]) (T.length + Etl.length) = (S0.push v).toList := by
    rw [Trace.stk_append (by simp), hstk _ (by omega) (Nat.le_refl _)]
  have hstkf : stk (T ++ Etl ++ [Ev.exit σx v f]) (T.length + Etl.length + 1) = S0.toList := by
    rw [← hTE, Trace.stk_snoc_exit, hTE, hstk _ (by omega) (Nat.le_refl _)]; simp
  have hblkf : ∀ z, blk (T ++ Etl ++ [Ev.exit σx v f]) (T.length + Etl.length + 1) z = bf[z] := by
    intro z; rw [← hTE, Trace.blk_snoc_other (by intros; simp) (by intros; simp), hTE, hblk z]
  obtain ⟨σ0, hent⟩ := tl.enter
  have hent' : (T ++ Etl ++ [Ev.exit σx v f])[T0.length]? = some (.enter σ0 v h) := by rw [hassoc, List.getElem?_append_left hlen0]; exact hent
  have hstk0 : stk (T ++ Etl ++ [Ev.exit σx v f]) T0.length = S0.toList := by rw [hassoc, Trace.stk_append (by omega)]; exact tl.stk0
  have hstk1 : stk (T ++ Etl ++ [Ev.exit σx v f]) (T0.length + 1) = (S0.push v).toList := by rw [Trace.stk_succ_enter hent', hstk0]; simp
  have hfr : Frame (T ++ Etl ++ [Ev.exit σx v f]) T0.length (T.length + Etl.length) := by
    refine ⟨by omega, ⟨σ0, v, h, hent'⟩, ⟨σx, v, f, hx⟩, by rw [hstkf, hstk0], ?_⟩
    intro q h1 h2
    rw [hstk0]
    rcases Nat.lt_or_ge T.length q with hq | hq
    · rw [Trace.stk_append (by simp; omega), hstk q (by omega) h2]; simp
    · rw [hassoc, Trace.stk_append hq]
      have := le_length_of_take_eq (tl.isOpen q h1 hq) (by simp)
      simp at this ⊢; omega
  -- the tail consists of unblock events
  have hat : ∀ r, T.length ≤ r → r < T.length + Etl.length → ∃ σ u L, (T ++ Etl ++ [Ev.exit σx v f])[r]? = some (.unblock σ u L) := by
    intro r h1 h2
    have hri : r - T.length < Etl.length := by omega
    obtain ⟨σ, u, L, he⟩ := hunb Etl[r - T.length] (List.getElem_mem hri)
    refine ⟨σ, u, L, ?_⟩
    rw [hassoc, List.getElem?_append_right h1, List.getElem?_append_left hri, List.getElem?_eq_getElem hri, he]
  -- the outputs of the call are the outputs of its loop
  obtain ⟨σe, E, hE, hN⟩ := tl.ext
  have hTf : T ++ Etl ++ [Ev.exit σx v f] = T0 ++ Ev.enter σe v h :: (E ++ Etl ++ [Ev.exit σx v f]) := by rw [hE]; simp
  have houts : outputs (E ++ Etl ++ [Ev.exit σx v f]) = N := by rw [outputs_append, outputs_append, hN, outputs_unb hunb]; simp [outputs]
  have hout_iff : (∃ q σ' P, T0.length < q ∧ q < T.length + Etl.length ∧ (T ++ Etl ++ [Ev.exit σx v f])[q]? = some (.output σ' P)) ↔ N ≠ [] := by
    constructor
    · rintro ⟨q, σ', P, h1, h2, hq⟩
      rw [hTf] at hq
      have := output_mem h1 hq
      rw [houts] at this
      exact List.ne_nil_of_mem this
    · intro hne
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil N hne
      rw [← hN] at hp
      obtain ⟨q, σ', h1, h2, hq⟩ := output_pos (T0 := T0) (e0 := Ev.enter σe v h) hp
      rw [← hE] at h2 hq
      exact ⟨q, σ', p, h1, by omega, by rw [hassoc, List.getElem?_append_left h2]; exact hq⟩
  have hcall : CallOK G s t (T ++ Etl ++ [Ev.exit σx v f]) T0.length (T.length + Etl.length) := by
    refine ⟨hfr, ?_, ?_⟩
    · intro σ' v' f' hx'
      rw [hx] at hx'
      simp only [Option.some.injEq, Ev.exit.injEq] at hx'
      rw [← hx'.2.2, hpost.ret, hout_iff]
    · intro p hp hpre
      rw [hstk1] at hpre
      have hmem := hpost.complete p hp (by simpa using hpre)
      rw [← hN] at hmem
      obtain ⟨q, σ', h1, h2, hq⟩ := output_pos (T0 := T0) (e0 := Ev.enter σe v h) hmem
      rw [← hE] at h2 hq
      exact ⟨q, σ', h1, by omega, by rw [hassoc, List.getElem?_append_left h2]; exact hq⟩
  refine { ext := ⟨σe, E ++ Etl ++ [Ev.exit σx v f], hTf, houts⟩, stk_now := by rw [hlen]; exact hstkf, blk_now := by rw [hlen]; exact hblkf, seg := ?_, call := by rw [hlen, Nat.add_sub_cancel]; exact hcall }
  intro q h1 h2
  rw [hlen] at h2
  rcases Nat.eq_or_lt_of_le h1 with hq | hq
  · -- the entry
    subst hq
    refine ⟨by rw [hassoc]; exact tl.ev0.append (by omega), fun σ' v' h' _ => ⟨_, hcall⟩, fun σ' v' f' he => ?_, fun σ' u L he => ?_⟩
    · rw [hent'] at he; cases he
    · rw [hent'] at he; cases he
  rcases Nat.lt_or_ge q T.length with hq' | hq'
  · rw [hassoc]; exact (tl.seg q hq hq').append hq'
  rcases Nat.lt_or_ge q (T.length + Etl.length) with hq'' | hq''
  · -- an event of the UNBLOCK chain: its facts, and the chain it belongs to
    obtain ⟨σq, uq, Lq, hqe⟩ := hat q hq' hq''
    have hf : f = true := hchain (fun h0 => by subst h0; simp at hq''; omega)
    refine ⟨(hev q hq' hq'').append (by rw [hTE]; exact hq''), fun σ' v' h' he => (by rw [hqe] at he; cases he), fun σ' v' f' he => (by rw [hqe] at he; cases he), fun σ' u L _ => ⟨T0.length, T.length + Etl.length, ?_⟩⟩
    refine ⟨hfr, ⟨by omega, hq''⟩, ?_, ⟨σx, v, by rw [hx, hf]⟩, fun r h1 h2 => hat r (by omega) h2⟩
    rw [hstk1, Trace.stk_append (by rw [hTE]; omega), hstk q hq' (by omega)]
  · -- the exit
    rw [show q = T.length + Etl.length by omega]
    refine ⟨?_, fun σ' v' h' he => (by rw [hx] at he; cases he), fun σ' v' f' _ => ⟨T0.length, hfr⟩, fun σ' u L he => (by rw [hx] at he; cases he)⟩
    simp only [EvOK, hx, hstkx]
    simp

/-- the exit of a failed call: nothing between the loop and the exit -/
theorem tl_exit_nil {N : List (List (Fin n))} {bl : Vector Bool n} {Bf : Vector (List (Fin n)) n} {T : List (Ev n)} (tl : TrLoop G s t h v S0 T0 N bl T)
    {σx : Nat} {f : Bool} (hpost : SearchPost G s t h v S0 bl0 f bl Bf N) :
    TrCall G s t h v S0 T0 N bl (T ++ [.exit σx v f]) := by
  have := tl_exit (Etl := []) (σx := σx) tl (by simp) (fun q h1 h2 => by simp at h2 ⊢; rw [show q = T.length by omega]; simpa using tl.stk_now)
    (fun q h1 h2 => by simp at h2; omega) (fun z => by simp only [List.append_nil, List.length_nil, Nat.add_zero]; exact tl.blk_now z) hpost (fun h' => absurd rfl h')
  simpa using this

end steps

/-! ## The trace spec of `search` -/

/-- spec of `search v h` with its trace facts; induction on n - h -/
theorem search_spec_tr (G : Graph n) (s t : Fin n) (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (bl0 : Vector Bool n) (B0 : Vector (List (Fin n)) n) (T0 : List (Ev n)) :
    ⦃fun st => ⌜st.S = S0 ∧ st.blocked = bl0 ∧ st.B = B0 ∧ st.trace.toList = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0⌝⦄
    search G t v h
    ⦃⇓ r st => ⌜st.S = S0 ∧ ∃ N, SearchPost G s t h v S0 bl0 r st.blocked st.B N ∧ TrCall G s t h v S0 T0 N st.blocked st.trace.toList⌝⦄ := by
  -- spec of the recursive call; vacuous unless h + 1 < n
  have ih : ∀ w (S1 : Array (Fin n)) (bl1 : Vector Bool n) (B1 : Vector (List (Fin n)) n) (T1 : List (Ev n)),
      ⦃fun st => ⌜st.S = S1 ∧ st.blocked = bl1 ∧ st.B = B1 ∧ st.trace.toList = T1 ∧ SearchPre G s t (h + 1) w S1 bl1 B1 ∧ TrPre S1 bl1 T1⌝⦄
      search G t w (h + 1)
      ⦃⇓ r st => ⌜st.S = S1 ∧ ∃ N, SearchPost G s t (h + 1) w S1 bl1 r st.blocked st.B N ∧ TrCall G s t (h + 1) w S1 T1 N st.blocked st.trace.toList⌝⦄ := by
    intro w S1 bl1 B1 T1
    by_cases hh : h + 1 < n
    · exact search_spec_tr G s t (h + 1) w S1 bl1 B1 T1
    · intro st hP
      exact absurd hP.2.2.2.2.1.depth hh
  have hub := unblock_spec_tr G s t S0.toList v (S0.push v) v 0
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.isBlocked, M.setBlocked, M.blist, M.setBlist, M.stack, ih, hub] invariants
  · ⇓⟨xs, found⟩ st => ⌜st.S = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 xs.prefix found st.blocked st.B N ∧ TrLoop G s t h v S0 T0 N st.blocked st.trace.toList⌝
  · ⇓⟨xs, _⟩ st => ⌜st.S = S0.push v ∧ ∃ N Bs, LoopInv G s t h v S0 bl0 (G.succ v) false st.blocked Bs N ∧ FailInv v Bs xs.prefix st.B ∧ TrLoop G s t h v S0 T0 N st.blocked st.trace.toList⌝
  case vc1.step.isTrue =>
    -- closing edge (v, t): output S0 ++ [v, t]
    obtain ⟨-, -, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    have hmem := mem_of_eq_append_cons hsplit
    have hcur := ‹_ = t›
    simp +zetaDelta only
    subst hcur
    refine ⟨hS, N ++ [S0.toList ++ [v, _]], loop_output pre hinv hmem (fun hG => not_mem_of_nodup_split (hG v) hsplit), ?_⟩
    rw [Array.toList_push, hS, push_append]
    exact tl_output pre hinv tl
  case vc2.step.isFalse.isTrue.isTrue.pre =>
    -- recursive call: its precondition
    obtain ⟨-, -, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have hnt := ‹¬_ = t›
    have hfree := ‹(!_) = true›
    simp +zetaDelta only at hfree ⊢
    rw [hS]
    exact ⟨trivial, trivial, trivial, trivial, loop_child_pre pre hinv hmem hnt (by simpa using hfree), tl_child_pre tl⟩
  case vc3.step.isFalse.isTrue.isTrue.post.success =>
    -- recursive call: back in the loop
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    obtain ⟨hS', Nc, hpost, tc⟩ := ‹_ ∧ ∃ N, SearchPost G s t (h + 1) _ _ _ _ _ _ N ∧ TrCall G s t (h + 1) _ _ _ N _ _›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    simp +zetaDelta only at hS' hpost tc ⊢
    rw [hS] at hS' hpost tc
    exact ⟨hS', N ++ Nc, loop_child_post hinv (fun hG => not_mem_of_nodup_split (hG v) hsplit) hpost, tl_child_post tl tc⟩
  case vc4.step.isFalse.isTrue.isFalse =>
    -- the depth guard fails: impossible
    obtain ⟨-, -, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    obtain ⟨-, N, hinv, -⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have hnt := ‹¬_ = t›
    have hfree := ‹(!_) = true›
    have hh := ‹¬ h + 1 < n›
    simp +zetaDelta only at hfree
    exact absurd (loop_child_pre pre hinv hmem hnt (by simpa using hfree)).depth hh
  case vc5.step.isFalse.isFalse =>
    -- blocked successor
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    have hblk := ‹¬(!_) = true›
    simp +zetaDelta only at hblk ⊢
    exact ⟨hS, N, loop_blocked hinv (by simpa using hblk), tl⟩
  case vc6.pre =>
    -- entry: push v, block it, the enter event
    obtain ⟨hS, hb, hB, hT, pre, tp⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    simp +zetaDelta only
    rw [hS, hb, hB]
    refine ⟨rfl, [], loop_init pre, ?_⟩
    rw [Array.toList_push, hT]
    exact tl_init pre tp
  case vc7.post.success.isTrue.pre =>
    -- fruitful: the precondition of UNBLOCK(v)
    obtain ⟨-, -, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    have hf := ‹_ = true›
    subst hf
    exact ⟨trivial, trivial, trivial, hS, loop_upre pre hinv, by simp, by rw [tl.stk_now]; simp, tl.blk_now⟩
  case vc8.post.success.isTrue.post.success =>
    -- fruitful: after UNBLOCK(v), exit and pop
    obtain ⟨-, -, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    obtain ⟨-, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    obtain ⟨hS', hpost, tu⟩ := ‹_ = S0.push v ∧ UPost G t S0.toList v v _ _ _ _ ∧ TrUnb G s t (S0.toList ++ [v]) _ _ _›
    have hf := ‹_ = true›
    subst hf
    have hpf := post_found pre hinv hpost
    obtain ⟨Etl, hEtl, hunb⟩ := tu.ext
    simp +zetaDelta only
    rw [hS', Array.toList_push, hEtl]
    refine ⟨by simp, N, hpf, ?_⟩
    rw [hEtl] at tu
    refine tl_exit tl hunb (fun q h1 h2 => ?_) (fun q h1 h2 => tu.ev q h1 (by rw [List.length_append]; exact h2)) (fun z => ?_) hpf (fun _ => rfl)
    · rw [tu.stk q h1 (by rw [List.length_append]; exact h2)]; simp
    · have := tu.blk_now z; rw [List.length_append] at this; exact this
  case vc9.step.isTrue =>
    -- failed return: v goes on B[w]
    obtain ⟨hS, N, Bs, hinv, hf, tl⟩ := ‹_ = S0.push v ∧ ∃ N Bs, LoopInv G s t h v S0 bl0 _ _ _ Bs N ∧ FailInv v Bs _ _ ∧ TrLoop G s t h v S0 T0 N _ _›
    have hv := ‹¬ v ∈ _›
    simp +zetaDelta only at hv ⊢
    exact ⟨hS, N, Bs, hinv, fail_add hf hv, tl⟩
  case vc10.step.isFalse =>
    -- failed return: v is on B[w] already
    obtain ⟨hS, N, Bs, hinv, hf, tl⟩ := ‹_ = S0.push v ∧ ∃ N Bs, LoopInv G s t h v S0 bl0 _ _ _ Bs N ∧ FailInv v Bs _ _ ∧ TrLoop G s t h v S0 T0 N _ _›
    have hv := ‹¬¬ v ∈ _›
    simp +zetaDelta only at hv ⊢
    exact ⟨hS, N, Bs, hinv, fail_skip hf (by simpa using hv), tl⟩
  case vc11.post.success.isFalse.pre =>
    -- failed return: start of the loop over the successors
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t h v S0 bl0 _ _ _ _ N ∧ TrLoop G s t h v S0 T0 N _ _›
    have hf := ‹¬ _ = true›
    simp only [Bool.not_eq_true] at hf
    subst hf
    exact ⟨hS, N, _, hinv, fail_init _ hinv.inv.nodup, tl⟩
  case vc12.post.success.isFalse.post.success =>
    -- failed return: exit and pop
    obtain ⟨-, -, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = bl0 ∧ _ = B0 ∧ _ = T0 ∧ SearchPre G s t h v S0 bl0 B0 ∧ TrPre S0 bl0 T0›
    obtain ⟨hS, N, Bs, hinv, hf, tl⟩ := ‹_ = S0.push v ∧ ∃ N Bs, LoopInv G s t h v S0 bl0 _ _ _ Bs N ∧ FailInv v Bs _ _ ∧ TrLoop G s t h v S0 T0 N _ _›
    have hfound := ‹¬ _ = true›
    simp only [Bool.not_eq_true] at hfound
    subst hfound
    have hpf := post_fail pre hinv hf
    simp +zetaDelta only
    rw [hS, Array.toList_push]
    exact ⟨by simp, N, hpf, tl_exit_nil tl hpf⟩
termination_by n - h

/-! ## The run -/

theorem root_tr {σ : Nat} : TrPre (#[] : Array (Fin n)) (Vector.replicate n false) [Ev.start σ] where
  stk := by rw [show [Ev.start σ].length = 0 + 1 from rfl, Trace.stk_succ]; rfl
  blk := fun z => by rw [show [Ev.start σ].length = 0 + 1 from rfl, Trace.blk_succ]; simp [blk]

/-- the facts at every position of the run: the start event, the root call's segment, the term event -/
theorem johnson_runOK (G : Graph n) (s t : Fin n) (hst : s ≠ t) : RunOK G s t (johnson G s t) := by
  refine johnson_of_root (fun st => st.S = #[] ∧ st.blocked = Vector.replicate n false ∧ st.B = Vector.replicate n [] ∧ st.trace.toList = [Ev.start 0] ∧ SearchPre G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []) ∧ TrPre #[] (Vector.replicate n false) [Ev.start 0])
    (RunOK G s t) ⟨rfl, rfl, rfl, rfl, root_pre hst, root_tr⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  obtain ⟨-, N, -, tc⟩ := (StateM.triple_iff _ _ _).mp (search_spec_tr G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []) [Ev.start 0]) st hpre
  obtain ⟨σe, E, hE, -⟩ := tc.ext
  have hlen : (search G t s 0 |>.run st).2.trace.toList.length = 1 + (1 + E.length) := by rw [hE]; simp; omega
  intro q hq
  simp only [List.length_append, List.length_singleton] at hq
  rcases Nat.lt_or_ge q 1 with h0 | h0
  · -- the start event
    rw [show q = 0 by omega]
    have h0e : ((search G t s 0 |>.run st).2.trace.toList ++ [Ev.term (search G t s 0 |>.run st).2.steps])[0]? = some (.start 0) := by
      rw [List.getElem?_append_left (by rw [hlen]; omega), hE]; simp
    exact ⟨by unfold EvOK; rw [h0e], fun σ v h he => (by rw [h0e] at he; cases he), fun σ v f he => (by rw [h0e] at he; cases he), fun σ u L he => (by rw [h0e] at he; cases he)⟩
  rcases Nat.lt_or_ge q (search G t s 0 |>.run st).2.trace.toList.length with hq' | hq'
  · exact (tc.seg q (by simpa using h0) hq').append hq'
  · -- the term event
    rw [show q = (search G t s 0 |>.run st).2.trace.toList.length by omega]
    have hte : ((search G t s 0 |>.run st).2.trace.toList ++ [Ev.term (search G t s 0 |>.run st).2.steps])[(search G t s 0 |>.run st).2.trace.toList.length]? = some (.term (search G t s 0 |>.run st).2.steps) := by simp
    exact ⟨by unfold EvOK; rw [hte]; dsimp only; rw [Trace.stk_append (Nat.le_refl _), tc.stk_now], fun σ v h he => (by rw [hte] at he; cases he), fun σ v f he => (by rw [hte] at he; cases he), fun σ u L he => (by rw [hte] at he; cases he)⟩

end Johnson
