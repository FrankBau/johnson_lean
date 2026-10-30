/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.RunSearch

/-!
  The worst-case delay of Johnson's algorithm (Lemma 3 of Johnson 1975, for s-t paths): consecutive observable events (start,
  outputs, term) are at most 4n + 5m steps apart; hence the τ-th observable event comes after at most τ(4n + 5m) steps
  (Corollary 2).

  Per interval (a, c] between consecutive observable events, from the facts at every position of the run (`RunOK`):
  - every UNBLOCK chain in (a, c] belongs to a frame entered before a, as a fruitful frame contains an output (`chain_open`);
  - no vertex is unblocked twice (`unblock_once`, Johnson's Part 1): after the first unblock of u at q₁, u has a simple path W
    to t avoiding the stack; the first vertex of W entered afterwards has a frame that outputs (Call Completeness), and that
    frame closes before the chain of a second unblock, so the output would lie inside (a, c);
  - entries and unblocks of a vertex alternate (`balance`), so a vertex is entered at most twice, and at most once if it is
    on the stack at a;
  - failed exits are exits of frames entered in (a, c] (`fail_le`), and a B-list holds at most indeg(u) vertices.
  Charges: entry 1 + |succ|, failed exit |succ|, unblock 1 + |B[u]|, output |P|; with the scans owed at a this is at most
  3 + 4·outdeg(z) + indeg(z) per vertex z, plus the output at c, at most n: in total 4n + 5m (`interval_bound`).
-/

namespace Johnson

open Trace

variable {n : Nat}

/-! ## Sums (from the BS-DFS formalization, Bsdfs/DelaySum.lean) -/

section sums
variable {α β : Type}

/-- sum of f over a list -/
def lsum (L : List α) (f : α → Nat) : Nat := (L.map f).sum

@[simp] theorem lsum_nil (f : α → Nat) : lsum [] f = 0 := rfl
@[simp] theorem lsum_cons (a : α) (L : List α) (f : α → Nat) : lsum (a :: L) f = f a + lsum L f := by simp [lsum]

theorem lsum_append (L M : List α) (f : α → Nat) : lsum (L ++ M) f = lsum L f + lsum M f := by simp [lsum]

theorem lsum_add (L : List α) (f g : α → Nat) : lsum L (fun a => f a + g a) = lsum L f + lsum L g := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [lsum_cons, ih]; omega

theorem lsum_le {L : List α} {f g : α → Nat} (h : ∀ a ∈ L, f a ≤ g a) : lsum L f ≤ lsum L g := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons a L ih => simp only [lsum_cons]; exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem lsum_mul (L : List α) (c : Nat) (f : α → Nat) : lsum L (fun a => c * f a) = c * lsum L f := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [lsum_cons, ih, Nat.mul_add]

theorem lsum_zero (L : List α) : lsum L (fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem lsum_const (L : List α) (c : Nat) : lsum L (fun _ => c) = c * L.length := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [lsum_cons, ih, List.length_cons, Nat.mul_add, Nat.mul_one]; omega

/-- exchange of a double sum -/
theorem lsum_comm (L : List α) (M : List β) (g : α → β → Nat) : lsum L (fun a => lsum M (g a)) = lsum M (fun b => lsum L (fun a => g a b)) := by
  induction L with
  | nil => simp [lsum_zero]
  | cons a L ih => simp only [lsum_cons, ih, lsum_add]

theorem le_lsum {L : List α} {f : α → Nat} {a : α} (ha : a ∈ L) : f a ≤ lsum L f := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    simp only [lsum_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih ha; omega

theorem lsum_ite_eq_zero [DecidableEq α] {M : List α} {x : α} (hx : x ∉ M) (g : α → Nat) : lsum M (fun y => if y = x then g y else 0) = 0 := by
  induction M with
  | nil => rfl
  | cons y M ih =>
    simp only [List.mem_cons, not_or] at hx
    simp [Ne.symm hx.1, ih hx.2]

theorem lsum_ite_eq [DecidableEq α] {M : List α} (hM : M.Nodup) {x : α} (hx : x ∈ M) (g : α → Nat) : lsum M (fun y => if y = x then g y else 0) = g x := by
  induction M with
  | nil => simp at hx
  | cons y M ih =>
    rw [List.nodup_cons] at hM
    simp only [lsum_cons]
    by_cases hyx : y = x
    · subst hyx; simp [lsum_ite_eq_zero hM.1]
    · have : x ∈ M := by simp at hx; rcases hx with h | h; exact absurd h.symm hyx; exact h
      simp [hyx, ih hM.2 this]

/-- a sum over a list without repetitions, as an indicator sum over a larger list without repetitions -/
theorem lsum_eq_ind [DecidableEq α] {L M : List α} (hL : L.Nodup) (hM : M.Nodup) (hLM : ∀ a ∈ L, a ∈ M) (g : α → Nat) : lsum L g = lsum M (fun y => if y ∈ L then g y else 0) := by
  induction L with
  | nil => simp [lsum_zero]
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    have hsplit : (fun y => if y ∈ x :: L then g y else 0) = (fun y => (if y = x then g y else 0) + (if y ∈ L then g y else 0)) := by
      funext y
      by_cases hyx : y = x
      · subst hyx; simp [hL.1]
      · simp [hyx]
    rw [hsplit, lsum_add, lsum_ite_eq hM (hLM x (by simp)), ← ih hL.2 (fun a ha => hLM a (by simp [ha]))]
    simp

/-- a count as a sum of indicators -/
theorem lsum_countP (L : List α) (P : α → Bool) (c : Nat) : lsum L (fun q => if P q then c else 0) = c * L.countP P := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [lsum_cons, ih, List.countP_cons]
    split <;> simp [Nat.mul_add] <;> omega

end sums

/-- sum over all nodes -/
abbrev nsum (f : Fin n → Nat) : Nat := lsum (List.finRange n) f

/-! ## In-degrees -/

/-- the number of predecessors of u -/
def Graph.indeg (G : Graph n) (u : Fin n) : Nat := (List.finRange n).countP (fun x => decide (u ∈ G.succ x))

/-- a B-list: no duplicates, predecessors only, so at most indeg(u) entries -/
theorem length_le_indeg {G : Graph n} {u : Fin n} {L : List (Fin n)} (hnd : L.Nodup) (hL : ∀ x ∈ L, u ∈ G.succ x) : L.length ≤ G.indeg u := by
  unfold Graph.indeg
  rw [List.countP_eq_length_filter]
  exact hnd.length_le_of_subset (fun x hx => List.mem_filter.mpr ⟨List.mem_finRange x, by simpa using hL x hx⟩)

/-- the in-degrees sum to at most m -/
theorem Graph.indeg_sum (G : Graph n) : nsum G.indeg ≤ G.m := by
  have h1 : ∀ u, G.indeg u = nsum (fun x => if decide (u ∈ G.succ x) then 1 else 0) := by
    intro u
    unfold Graph.indeg
    simp only [nsum]
    rw [lsum_countP]; simp
  have h2 : ∀ x, nsum (fun u => if decide (u ∈ G.succ x) then 1 else 0) ≤ (G.succ x).length := by
    intro x
    simp only [nsum]
    rw [lsum_countP, Nat.one_mul, List.countP_eq_length_filter]
    exact List.Nodup.length_le_of_subset ((List.nodup_finRange n).filter _) (fun u hu => by simpa using (List.mem_filter.mp hu).2)
  have : nsum G.indeg = nsum (fun x => nsum (fun u => if decide (u ∈ G.succ x) then 1 else 0)) := by
    rw [show G.indeg = fun u => nsum (fun x => if decide (u ∈ G.succ x) then 1 else 0) from funext h1]
    exact lsum_comm _ _ _
  rw [this]
  exact lsum_le (fun x _ => h2 x)

/-! ## Facts per interval -/

section interval
variable {G : Graph n} {s t : Fin n} {T : List (Ev n)}

/-- unblock events do not change the stack -/
theorem Trace.stk_eq_of_unb : ∀ (d p : Nat), (∀ r, p ≤ r → r < p + d → ∃ σ u L, T[r]? = some (.unblock σ u L)) → stk T (p + d) = stk T p
  | 0, _, _ => rfl
  | d + 1, p, h => by
    obtain ⟨σ, u, L, hr⟩ := h (p + d) (by omega) (by omega)
    rw [show p + (d + 1) = p + d + 1 by omega, Trace.stk_succ_other (fun σ' v h' he => by rw [hr] at he; cases he) (fun σ' v f he => by rw [hr] at he; cases he)]
    exact Trace.stk_eq_of_unb d p (fun r h1 h2 => h r h1 (by omega))

/-- at its exit event the frame's own stack is back on top -/
theorem Trace.Frame.at_exit {e x : Nat} (h : Frame T e x) : stk T x = stk T (e + 1) := by
  have hex := h.1
  obtain ⟨σ, v, f, hx⟩ := h.2.2.1
  have hsz := h.2.2.2.1
  have h1 := Trace.stk_succ_exit hx
  have h2 := h.isOpen hex (Nat.le_refl x)
  have hlen : (stk T x).length = (stk T e).length + 1 := by
    rw [h1, List.length_dropLast] at hsz; omega
  have := h.prefix hex (Nat.le_refl x)
  rw [← hlen, List.take_length] at this
  exact this

/-- an observable event inside a frame is an output: the start sits at position 0, and at the term the stack is empty -/
theorem RunOK.obs_in_frame (hR : RunOK G s t T) {e x a : Nat} (hfr : Frame T e x) (h1 : e < a) (h2 : a ≤ x) (ha : isObs T a = true) : ∃ σ P, T[a]? = some (.output σ P) := by
  unfold isObs at ha
  cases hq : T[a]? with
  | none => rw [hq] at ha; cases ha
  | some ev =>
    rw [hq] at ha
    cases ev with
    | start σ => have := hR.ev hq; simp only [EvOK, hq] at this; omega
    | term σ =>
      have h0 := hR.ev hq
      simp only [EvOK, hq] at h0
      have := hfr.isOpen h1 h2
      rw [h0] at this; simp at this
    | output σ P => exact ⟨σ, P, rfl⟩
    | _ => simp [Ev.obs] at ha

/-- the UNBLOCK chain of an unblock event in (a, c] belongs to a frame entered before a: the frame is fruitful, so it contains an
    output, which lies before the chain and not in (a, c) -/
theorem RunOK.chain_open (hR : RunOK G s t T) {a c : Nat} (hC : Consec T a c) {q σ : Nat} {u : Fin n} {L : List (Fin n)} (hq2 : q ≤ c) (hq : T[q]? = some (.unblock σ u L)) :
    ∃ e x, ChainAt T q e x ∧ e < a := by
  obtain ⟨e, x, hch⟩ := hR.chain hq
  refine ⟨e, x, hch, ?_⟩
  obtain ⟨σx, vx, hxe⟩ := hch.exit
  obtain ⟨o, σo, P, ho1, ho2, hoe⟩ := ((hR.callOK hch.frame).ret σx vx true hxe).mp rfl
  have hoq : o < q := by
    refine Nat.lt_of_not_le fun hge => ?_
    obtain ⟨σ', u', L', hr⟩ := hch.all o hge ho2
    rw [hr] at hoe; cases hoe
  have hoa : o ≤ a := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := hC.between o hlt (by omega)
    simp [isObs, hoe, Ev.obs] at this
  omega

/-- Johnson's Part 1: a vertex unblocked at q₁ is not unblocked again at q₃ in the same interval -/
theorem RunOK.unblock_twice (hR : RunOK G s t T) {a c : Nat} (hC : Consec T a c) {u : Fin n} {q₁ q₃ : Nat} (h1 : a < q₁) (h3 : q₃ ≤ c) (h13 : q₁ < q₃)
    (hu1 : unblockAt T u q₁ = true) (hu3 : unblockAt T u q₃ = true) : False := by
  obtain ⟨σ₁, L₁, he1⟩ := Trace.unblockAt_iff.mp hu1
  obtain ⟨σ₃, L₃, he3⟩ := Trace.unblockAt_iff.mp hu3
  -- u got blocked again in between: an entry of u
  have hb1 : blk T (q₁ + 1) u = false := by rw [Trace.blk_succ_unblock he1]; simp
  obtain ⟨q₂, hq21, hq22, hen2⟩ := Trace.exists_enter_of_blk (by omega) hb1 (hR.unblock he3).1
  -- at q₁, u has a simple path W to t avoiding the stack below the top
  obtain ⟨-, -, -, huS, ⟨l, hwalk⟩⟩ := hR.unblock he1
  obtain ⟨W, hWh, hWl, hWe, hWnd, hWX, -⟩ := hwalk.path
  have huW : u ∈ W := List.mem_of_head? hWh
  have hWS : ∀ z ∈ W, z ∉ (stk T q₁).dropLast := by
    intro z hz
    cases W with
    | nil => simp at hz
    | cons w W' =>
      simp only [List.head?_cons, Option.some.injEq] at hWh
      subst hWh
      rcases List.mem_cons.mp hz with rfl | hz
      · exact huS
      · exact hWX z (by simpa using hz)
  -- the chain at q₁ runs to its exit x₁, which pops the top
  obtain ⟨e₁, x₁, hch1⟩ := hR.chain he1
  obtain ⟨σx₁, vx₁, hx₁⟩ := hch1.exit
  obtain ⟨-, hl12⟩ := hch1.lt
  have hstkx : stk T x₁ = stk T q₁ := by
    have := Trace.stk_eq_of_unb (T := T) (x₁ - q₁) q₁ (fun r h1 h2 => hch1.all r h1 (by omega))
    rwa [show q₁ + (x₁ - q₁) = x₁ by omega] at this
  have hstkx1 : stk T (x₁ + 1) = (stk T q₁).dropLast := by rw [Trace.stk_succ_exit hx₁, hstkx]
  -- the entry of u comes after the chain
  have hq2x : x₁ < q₂ := by
    refine Nat.lt_of_not_le fun hle => ?_
    obtain ⟨σ', h', he2⟩ := Trace.enterAt_iff.mp hen2
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [heq, hx₁] at he2; cases he2
    · obtain ⟨σ'', u', L', hr⟩ := hch1.all q₂ (by omega) hlt
      rw [hr] at he2; cases he2
  -- the first entry of a vertex of W after x₁
  obtain ⟨qP, hP1, hP2, ⟨z, hzW, hzP⟩, hfirst⟩ := Trace.exists_first (P := fun q => ∃ z ∈ W, enterAt T z q = true) (lo := x₁) q₂ hq2x ⟨u, huW, hen2⟩
  -- no vertex of W is on the stack at qP
  have hoff : ∀ z' ∈ W, z' ∉ stk T qP := by
    intro z' hz'
    refine Trace.not_mem_stk_of_no_enter (p₁ := x₁ + 1) (by omega) (by rw [hstkx1]; exact hWS z' hz') (fun q hq1 hq2 => ?_)
    cases hc : enterAt T z' q
    · rfl
    · exact absurd ⟨z', hz', hc⟩ (hfirst q (by omega) hq2)
  -- the suffix of W from z continues the stack at qP to a simple s-t path
  obtain ⟨σP, hP, hePe⟩ := Trace.enterAt_iff.mp hzP
  obtain ⟨-, -, hzt, -, hstkP⟩ := hR.enter hePe
  obtain ⟨A, R, rfl⟩ := List.append_of_mem hzW
  have hRl : R.getLast? = some t := by
    cases R with
    | nil => simp at hWl; exact absurd hWl hzt
    | cons r R => rw [List.getLast?_append] at hWl; simpa using hWl
  have hRe : G.Edges (z :: R) := Graph.Edges.of_append_right (A := A) ((Graph.edges_iff_zip G _).mpr (by simpa [Graph.edges_iff_zip] using hWe))
  have hRnd : (z :: R).Nodup := (List.nodup_append.mp hWnd).2.1
  have hp : G.SimplePath s t (stk T qP ++ z :: R) :=
    StackPath.append_path hstkP hRl hRe hRnd (fun y hy => hoff y (by simp [hy]))
  -- Call Completeness of the frame of z: it outputs this path
  obtain ⟨xP, hfrP⟩ := hR.frame_of_enter hePe
  obtain ⟨qo, σo, hqo1, hqo2, hqoe⟩ := (hR.callOK hfrP).complete _ hp (by rw [Trace.stk_succ_enter hePe]; exact ⟨R, by simp⟩)
  -- the frame of z closes before q₃: it nests in the frame of the chain at q₃, which is the top there
  obtain ⟨e₃, x₃, hch3, he3a⟩ := hR.chain_open hC h3 he3
  obtain ⟨-, hl32⟩ := hch3.lt
  have hxP : xP < q₃ := by
    refine Nat.lt_of_not_le fun hle => ?_
    have o1 := hfrP.isOpen (q := q₃) (by omega) hle
    have o2 := hch3.frame.isOpen (q := qP) (by omega) (by omega)
    have o3 := hch3.frame.push
    rw [hch3.top] at o1
    omega
  -- so the output at qo lies inside (a, c)
  have := hC.between qo (by omega) (by omega)
  simp [isObs, hqoe, Ev.obs] at this

/-- no vertex is unblocked twice between consecutive observable events -/
theorem RunOK.unblock_once (hR : RunOK G s t T) {a c : Nat} (hC : Consec T a c) (u : Fin n) : cnt (fun q => unblockAt T u q = true) a c ≤ 1 := by
  apply Trace.cnt_le_one
  intro q₁ q₃ h11 h12 h31 h32 hu1 hu3
  rcases Nat.lt_trichotomy q₁ q₃ with hlt | heq | hgt
  · exact (hR.unblock_twice hC h11 h32 hlt hu1 hu3).elim
  · exact heq
  · exact (hR.unblock_twice hC h31 h12 hgt hu3 hu1).elim

/-- entries and unblocks of z alternate: on (lo, lo + d], the entries plus [z blocked after lo] are the unblocks plus [z blocked after lo + d] -/
theorem RunOK.balance (hR : RunOK G s t T) (z : Fin n) (lo : Nat) : ∀ d,
    cnt (fun q => enterAt T z q = true) lo (lo + d) + (if blk T (lo + 1) z = true then 1 else 0) = cnt (fun q => unblockAt T z q = true) lo (lo + d) + (if blk T (lo + d + 1) z = true then 1 else 0)
  | 0 => by simp [cnt]
  | d + 1 => by
    have ih := RunOK.balance hR z lo d
    have hp : lo ≤ lo + d := by omega
    rw [show lo + (d + 1) = lo + d + 1 by omega, Trace.cnt_succ _ hp, Trace.cnt_succ _ hp]
    generalize hP : lo + d + 1 = p at ih ⊢
    cases hq : T[p]? with
    | none =>
      have e1 : enterAt T z p = false := by simp [enterAt, hq]
      have e2 : unblockAt T z p = false := by simp [unblockAt, hq]
      have e3 : blk T (p + 1) z = blk T p z := by rw [Trace.blk_succ, hq]
      simp only [e1, e2, e3]
      simpa using ih
    | some ev =>
      cases ev with
      | enter σ v h =>
        have e3 := Trace.blk_succ_enter hq z
        have e2 : unblockAt T z p = false := by simp [unblockAt, hq]
        by_cases hvz : v = z
        · subst hvz
          have hb : blk T p v = false := (hR.enter hq).2.2.2.1
          have e1 : enterAt T v p = true := by simp [enterAt, hq]
          simp only [e1, e2, e3, hb] at ih ⊢
          simp at ih ⊢
          omega
        · have e1 : enterAt T z p = false := by simp [enterAt, hq, hvz]
          simp only [e1, e2, e3, hvz]
          simpa using ih
      | unblock σ u L =>
        have e3 := Trace.blk_succ_unblock hq z
        have e1 : enterAt T z p = false := by simp [enterAt, hq]
        by_cases huz : u = z
        · subst huz
          have hb : blk T p u = true := (hR.unblock hq).1
          have e2 : unblockAt T u p = true := by simp [unblockAt, hq]
          simp only [e1, e2, e3, hb] at ih ⊢
          simp at ih ⊢
          omega
        · have e2 : unblockAt T z p = false := by simp [unblockAt, hq, huz]
          simp only [e1, e2, e3, huz]
          simpa using ih
      | _ =>
        have e1 : enterAt T z p = false := by simp [enterAt, hq]
        have e2 : unblockAt T z p = false := by simp [unblockAt, hq]
        have e3 : blk T (p + 1) z = blk T p z := by rw [Trace.blk_succ, hq]
        simp only [e1, e2, e3]
        simpa using ih

/-- a vertex is entered at most once more than it is unblocked, and not more often if it is blocked right after a -/
theorem RunOK.enter_le (hR : RunOK G s t T) (z : Fin n) {a c : Nat} (hac : a ≤ c) :
    cnt (fun q => enterAt T z q = true) a c + (if blk T (a + 1) z = true then 1 else 0) ≤ cnt (fun q => unblockAt T z q = true) a c + 1 := by
  have h := hR.balance z a (c - a)
  rw [show a + (c - a) = c by omega] at h
  have hb : (if blk T (c + 1) z = true then 1 else 0) ≤ 1 := by split <;> omega
  omega

/-- every failed exit in (a, c] is the exit of a frame entered in (a, c] at the same vertex -/
theorem RunOK.fail_le (hR : RunOK G s t T) {a c : Nat} (hC : Consec T a c) (z : Fin n) : cnt (fun q => failAt T z q = true) a c ≤ cnt (fun q => enterAt T z q = true) a c := by
  classical
  let f : Nat → Nat := fun r => if h : ∃ e, Frame T e r then Classical.choose h else 0
  have hf : ∀ r, (∃ e, Frame T e r) → Frame T (f r) r := by
    intro r hr; simp only [f, dite_eq_left hr]; exact Classical.choose_spec hr
  apply Trace.cnt_le_of_inj _ _ f
  · intro r h1 h2 hfail
    obtain ⟨σ, hr⟩ := Trace.failAt_iff.mp hfail
    have hfr := hf r (hR.frame_of_exit hr)
    refine ⟨?_, by have := hfr.1; omega, ?_⟩
    · -- the frame is entered after a: otherwise a lies inside it, a is an output, and the frame would be fruitful
      refine Nat.lt_of_not_le fun hle => ?_
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · obtain ⟨σ', v', h', he⟩ := hfr.2.1
        have := hC.obs_a
        rw [← heq] at this
        simp [isObs, he, Ev.obs] at this
      · obtain ⟨σo, P, hao⟩ := hR.obs_in_frame hfr hlt (by omega) hC.obs_a
        have := ((hR.callOK hfr).ret σ z false hr).mpr ⟨a, σo, P, hlt, h1, hao⟩
        cases this
    · -- the frame's vertex is z
      obtain ⟨σ', v', h', he⟩ := hfr.2.1
      have htop := hR.exit hr
      rw [hfr.at_exit, Trace.stk_succ_enter he] at htop
      simp at htop
      subst htop
      exact Trace.enterAt_iff.mpr ⟨σ', h', he⟩
  · intro r₁ r₂ _ _ _ _ hf₁ hf₂ heq
    obtain ⟨σ₁, hr₁⟩ := Trace.failAt_iff.mp hf₁
    obtain ⟨σ₂, hr₂⟩ := Trace.failAt_iff.mp hf₂
    have h₁ := hf r₁ (hR.frame_of_exit hr₁)
    have h₂ := hf r₂ (hR.frame_of_exit hr₂)
    rw [heq] at h₁
    exact h₁.exit_unique h₂

end interval

/-! ## The charges of an interval, by vertices -/

section regroup
variable {G : Graph n} {s t : Fin n} {T : List (Ev n)}

/-- cost of the event at position q -/
def posCost (G : Graph n) (T : List (Ev n)) (q : Nat) : Nat := match T[q]? with | some e => G.evCost e | none => 0

/-- output cost at position q -/
def outCost (T : List (Ev n)) (q : Nat) : Nat := match T[q]? with | some (.output _ P) => P.length | _ => 0

theorem cost_drop_take (G : Graph n) (T : List (Ev n)) : ∀ (j i : Nat), i + j ≤ T.length → G.cost ((T.drop i).take j) = lsum (List.range' i j) (posCost G T)
  | 0, i, _ => by simp
  | j + 1, i, h => by
    have hi : i < T.length := by omega
    have e1 : (T.drop i).take (j + 1) = T[i] :: (T.drop (i + 1)).take j := by
      rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
    rw [e1, Graph.cost_cons, cost_drop_take G T j (i + 1) (by omega), List.range'_succ, lsum_cons]
    simp [posCost, hi]

/-- the charge bound of position q at the vertex z: entry 1 + |succ z|, failed exit |succ z|, unblock 1 + indeg z -/
def chargeAt (G : Graph n) (T : List (Ev n)) (q : Nat) (z : Fin n) : Nat :=
  ((if enterAt T z q = true then 1 + (G.succ z).length else 0) + (if failAt T z q = true then (G.succ z).length else 0)) + (if unblockAt T z q = true then 1 + G.indeg z else 0)

/-- the charge of a position, bounded by its vertex, plus an output's length -/
theorem RunOK.posCost_le (hR : RunOK G s t T) (q : Nat) : posCost G T q ≤ nsum (chargeAt G T q) + outCost T q := by
  unfold posCost outCost
  cases hq : T[q]? with
  | none => simp
  | some e =>
    cases e with
    | enter σ v h =>
      have h1 : chargeAt G T q v ≤ nsum (chargeAt G T q) := le_lsum (List.mem_finRange v)
      have h2 : 1 + (G.succ v).length ≤ chargeAt G T q v := by
        unfold chargeAt
        have : enterAt T v q = true := by simp [enterAt, hq]
        rw [ite_eq_left this]
        omega
      simp only [Graph.evCost_enter]
      omega
    | exit σ v f =>
      cases f with
      | false =>
        have h1 : chargeAt G T q v ≤ nsum (chargeAt G T q) := le_lsum (List.mem_finRange v)
        have h2 : (G.succ v).length ≤ chargeAt G T q v := by
          unfold chargeAt
          have : failAt T v q = true := by simp [failAt, hq]
          rw [ite_eq_left this]
          omega
        simp only [Graph.evCost_exit_false]
        omega
      | true => simp
    | unblock σ u L =>
      obtain ⟨-, hnd, hL, -, -⟩ := hR.unblock hq
      have hlen := length_le_indeg hnd hL
      have h1 : chargeAt G T q u ≤ nsum (chargeAt G T q) := le_lsum (List.mem_finRange u)
      have h2 : 1 + G.indeg u ≤ chargeAt G T q u := by
        unfold chargeAt
        have : unblockAt T u q = true := by simp [unblockAt, hq]
        rw [ite_eq_left this]
        omega
      simp only [Graph.evCost_unblock]
      omega
    | output σ P => simp
    | _ => simp

/-- the cost of a segment, regrouped by vertices -/
theorem RunOK.cost_le (hR : RunOK G s t T) (lo hi : Nat) :
    lsum (List.range' (lo + 1) (hi - lo)) (posCost G T) ≤ nsum (fun z => ((1 + (G.succ z).length) * cnt (fun q => enterAt T z q = true) lo hi + (G.succ z).length * cnt (fun q => failAt T z q = true) lo hi) + (1 + G.indeg z) * cnt (fun q => unblockAt T z q = true) lo hi) + lsum (List.range' (lo + 1) (hi - lo)) (outCost T) := by
  refine Nat.le_trans (lsum_le (fun q _ => hR.posCost_le q)) (Nat.le_of_eq ?_)
  rw [lsum_add]
  congr 1
  simp only [nsum]
  rw [lsum_comm]
  congr 1
  funext z
  simp only [chargeAt]
  rw [lsum_add, lsum_add, lsum_countP, lsum_countP, lsum_countP]
  simp [cnt]

/-- only the event at c can be an output in (a, c], and an output has at most n nodes -/
theorem RunOK.out_le (hR : RunOK G s t T) {a c : Nat} (hC : Consec T a c) : lsum (List.range' (a + 1) (c - a)) (outCost T) ≤ n := by
  have hsplit : List.range' (a + 1) (c - a) = List.range' (a + 1) (c - a - 1) ++ [c] := by
    have := hC.lt
    obtain ⟨d, hd⟩ : ∃ d, c - a = d + 1 := ⟨c - a - 1, by omega⟩
    rw [hd, Nat.add_sub_cancel, List.range'_concat, show a + 1 + 1 * d = c by omega]
  have h0 : lsum (List.range' (a + 1) (c - a - 1)) (outCost T) = 0 := by
    have : ∀ q ∈ List.range' (a + 1) (c - a - 1), outCost T q = 0 := by
      intro q hq
      simp only [List.mem_range'_1] at hq
      have := hC.between q (by omega) (by omega)
      unfold outCost
      cases hq' : T[q]? with
      | none => rfl
      | some e => cases e with
        | output σ P => simp [isObs, hq', Ev.obs] at this
        | _ => rfl
    have := lsum_le (L := List.range' (a + 1) (c - a - 1)) (f := outCost T) (g := fun _ => 0) (fun q hq => Nat.le_of_eq (this q hq))
    rw [lsum_zero] at this; omega
  have hc : outCost T c ≤ n := by
    unfold outCost
    cases hq' : T[c]? with
    | none => simp
    | some e => cases e with
      | output σ P =>
        obtain ⟨-, hnd, -⟩ := hR.output hq'
        simpa using nodup_length_le P hnd
      | _ => simp
  rw [hsplit, lsum_append]
  simp [h0]; exact hc

/-- the scans owed at an observable event a: the out-degrees of the stack at a -/
theorem RunOK.owed_le (hR : RunOK G s t T) {a : Nat} (ha : a < T.length) : G.owed T[a] ≤ nsum (fun z => if z ∈ stk T a then (G.succ z).length else 0) := by
  cases he : T[a] with
  | output σ P =>
    have hq : T[a]? = some (.output σ P) := by rw [List.getElem?_eq_getElem ha, he]
    obtain ⟨hP, hnd, -⟩ := hR.output hq
    have hstnd : (stk T a).Nodup := by rw [hP] at hnd; exact (List.nodup_append.mp hnd).1
    have hd : P.dropLast = stk T a := by rw [hP, List.dropLast_concat]
    rw [Graph.owed_output, hd]
    have e : G.outSum (stk T a) = lsum (stk T a) (fun v => (G.succ v).length) := rfl
    rw [e, lsum_eq_ind hstnd (List.nodup_finRange n) (fun x _ => List.mem_finRange x)]
    exact Nat.le_refl _
  | _ => simp [Graph.owed]

end regroup

/-! ## The bound -/

section bound
variable {G : Graph n} {s t : Fin n} {T : List (Ev n)}

/-- the charges per vertex: at most 3 + 4·outdeg(z) + indeg(z) -/
theorem vertex_bound {d i E F U S : Nat} (hE : E ≤ 2) (hES : E + S ≤ 2) (hF : F ≤ E) (hU : U ≤ 1) :
    ((1 + d) * E + d * F) + (1 + i) * U + d * S ≤ 3 + 4 * d + i := by
  have h1 : d * F ≤ d * E := Nat.mul_le_mul_left d hF
  have h2 : d * E + d * S ≤ d * 2 := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left d hES
  have h3 : d * E ≤ d * 2 := Nat.mul_le_mul_left d hE
  have h4 : i * U ≤ i := by have := Nat.mul_le_mul_left i hU; simpa using this
  have e1 : (1 + d) * E = E + d * E := by rw [Nat.add_mul, Nat.one_mul]
  have e2 : (1 + i) * U = U + i * U := by rw [Nat.add_mul, Nat.one_mul]
  rw [e1, e2]
  omega

/-- the cost of an interval and the scans owed at its start: at most 4n + 5m -/
theorem RunOK.interval_bound (hR : RunOK G s t T) {a c : Nat} (hC : Consec T a c) :
    G.cost ((T.drop (a + 1)).take (c - a)) + G.owed (T[a]'(by have := hC.lt; have := hC.bound; omega)) ≤ 4 * n + 5 * G.m := by
  have ha : a < T.length := by have := hC.lt; have := hC.bound; omega
  rw [cost_drop_take G T (c - a) (a + 1) (by have := hC.bound; have := hC.lt; omega)]
  have hcost := hR.cost_le a c
  have hout := hR.out_le hC
  have howed := hR.owed_le ha
  -- the stack at a is blocked right after a
  have hspine : ∀ z, z ∈ stk T a → blk T (a + 1) z = true := by
    intro z hz
    have hobs := hC.obs_a
    unfold isObs at hobs
    cases hq : T[a]? with
    | none => rw [hq] at hobs; cases hobs
    | some ev =>
      cases ev with
      | output σ P =>
        have := (hR.output hq).2.2 z hz
        rw [Trace.blk_succ_other (fun σ' v h' he => by rw [hq] at he; cases he) (fun σ' u L he => by rw [hq] at he; cases he)]
        exact this
      | start σ =>
        have := hR.ev hq; simp only [EvOK, hq] at this; subst this; simp [stk] at hz
      | term σ =>
        have := hR.ev hq; simp only [EvOK, hq] at this; rw [this] at hz; simp at hz
      | _ => rw [hq] at hobs; simp [Ev.obs] at hobs
  -- per vertex
  have hper : ∀ z : Fin n, ((1 + (G.succ z).length) * cnt (fun q => enterAt T z q = true) a c + (G.succ z).length * cnt (fun q => failAt T z q = true) a c) + (1 + G.indeg z) * cnt (fun q => unblockAt T z q = true) a c + (if z ∈ stk T a then (G.succ z).length else 0) ≤ 3 + 4 * (G.succ z).length + G.indeg z := by
    intro z
    have hU := hR.unblock_once hC z
    have hEU := hR.enter_le z (Nat.le_of_lt hC.lt)
    have hF := hR.fail_le hC z
    by_cases hz : z ∈ stk T a
    · have hb := hspine z hz
      simp only [hb, ite_true] at hEU
      have := vertex_bound (d := (G.succ z).length) (i := G.indeg z) (S := 1) (by omega) (by omega) hF hU
      simp only [hz, ite_true]
      simpa using this
    · have := vertex_bound (d := (G.succ z).length) (i := G.indeg z) (S := 0) (E := cnt (fun q => enterAt T z q = true) a c) (by split at hEU <;> omega) (by split at hEU <;> omega) hF hU
      simp only [hz, ite_false]
      simpa using this
  have hsum : nsum (fun z => ((1 + (G.succ z).length) * cnt (fun q => enterAt T z q = true) a c + (G.succ z).length * cnt (fun q => failAt T z q = true) a c) + (1 + G.indeg z) * cnt (fun q => unblockAt T z q = true) a c) + nsum (fun z => if z ∈ stk T a then (G.succ z).length else 0) ≤ 3 * n + 4 * G.m + G.m := by
    simp only [nsum]
    rw [← lsum_add]
    refine Nat.le_trans (lsum_le (fun z _ => hper z)) ?_
    rw [lsum_add, lsum_add, lsum_const, lsum_mul]
    have hm : lsum (List.finRange n) (fun z => (G.succ z).length) = G.m := rfl
    have hi : lsum (List.finRange n) G.indeg ≤ G.m := G.indeg_sum
    rw [hm, List.length_finRange]
    omega
  omega

end bound

/-! ## Consecutive observable events (from the BS-DFS formalization, Bsdfs/DelaySum.lean) -/

section consec

theorem filterMap_head_pos {α β : Type} (f : α → Option β) : ∀ (l : List α) (w : β) (F : List β), l.filterMap f = w :: F → ∃ j, ∃ hj : j < l.length, f l[j] = some w ∧ ∀ q (hq : q < l.length), q < j → f l[q] = none
  | [], _, _, h => by simp at h
  | x :: l, w, F, h => by
    cases hx : f x with
    | some b =>
      rw [List.filterMap_cons_some hx] at h
      obtain ⟨rfl, -⟩ := List.cons.inj h
      exact ⟨0, by simp, by simpa using hx, fun q _ hq => absurd hq (Nat.not_lt_zero _)⟩
    | none =>
      rw [List.filterMap_cons_none hx] at h
      obtain ⟨j, hj, hjw, hbefore⟩ := filterMap_head_pos f l w F h
      refine ⟨j + 1, by simp; omega, by simpa using hjw, fun q hq hqj => ?_⟩
      cases q with
      | zero => simpa using hx
      | succ q => simpa using hbefore q (by simp at hq; omega) (by omega)

/-- consecutive elements of l.filterMap f come from positions i < j with nothing in between -/
theorem filterMap_zip {α β : Type} (f : α → Option β) : ∀ (l : List α) (u w : β), (u, w) ∈ (l.filterMap f).zip (l.filterMap f).tail →
    ∃ i j, ∃ hij : i < j, ∃ hj : j < l.length, f (l[i]'(Nat.lt_trans hij hj)) = some u ∧ f l[j] = some w ∧ ∀ q (hq : q < l.length), i < q → q < j → f l[q] = none
  | [], _, _, h => by simp at h
  | x :: l, u, w, h => by
    cases hx : f x with
    | none =>
      rw [List.filterMap_cons_none hx] at h
      obtain ⟨i, j, hij, hj, hu, hw, hbetween⟩ := filterMap_zip f l u w h
      refine ⟨i + 1, j + 1, by omega, by simp; omega, by simpa using hu, by simpa using hw, fun q hq h1 h2 => ?_⟩
      cases q with
      | zero => omega
      | succ q => simpa using hbetween q (by simp at hq; omega) (by omega) (by omega)
    | some b =>
      rw [List.filterMap_cons_some hx] at h
      cases hF : l.filterMap f with
      | nil => rw [hF] at h; simp at h
      | cons w₀ F =>
        rw [hF] at h
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨hub, hww⟩ | h
        · obtain ⟨j, hj, hjw, hbefore⟩ := filterMap_head_pos f l w₀ F hF
          refine ⟨0, j + 1, by omega, by simp; omega, by simpa [hub] using hx, by simpa [hww] using hjw, fun q hq h1 h2 => ?_⟩
          cases q with
          | zero => omega
          | succ q => simpa using hbefore q (by simp at hq; omega) (by omega)
        · have h' : (u, w) ∈ (l.filterMap f).zip (l.filterMap f).tail := by rw [hF]; simpa using h
          obtain ⟨i, j, hij, hj, hu, hw, hbetween⟩ := filterMap_zip f l u w h'
          refine ⟨i + 1, j + 1, by omega, by simp; omega, by simpa using hu, by simpa using hw, fun q hq h1 h2 => ?_⟩
          cases q with
          | zero => omega
          | succ q => simpa using hbetween q (by simp at hq; omega) (by omega) (by omega)

theorem obsSteps_eq (tr : List (Ev n)) : obsSteps tr = tr.filterMap Ev.obs := by
  unfold obsSteps
  congr 1

/-- consecutive entries of obsSteps are the stamps of consecutive observable events -/
theorem obs_consec (tr : List (Ev n)) {u w : Nat} (h : (u, w) ∈ (obsSteps tr).zip (obsSteps tr).tail) : ∃ a c, Consec tr a c ∧ (∃ ha : a < tr.length, tr[a].obs = some u) ∧ ∃ hc : c < tr.length, tr[c].obs = some w := by
  rw [obsSteps_eq] at h
  obtain ⟨a, c, hac, hc, hu, hw, hbetween⟩ := filterMap_zip Ev.obs tr u w h
  refine ⟨a, c, ⟨hac, hc, ?_, ?_, ?_⟩, ⟨Nat.lt_trans hac hc, hu⟩, ⟨hc, hw⟩⟩
  · simp [isObs, List.getElem?_eq_getElem (Nat.lt_trans hac hc), hu]
  · simp [isObs, List.getElem?_eq_getElem hc, hw]
  · intro q h1 h2
    simp [isObs, List.getElem?_eq_getElem (Nat.lt_trans h2 hc), hbetween q (Nat.lt_trans h2 hc) h1 h2]

end consec

/-! ## The theorems -/

variable (G : Graph n) (s t : Fin n)

/-- worst-case delay (Johnson's Lemma 3): consecutive observable events (start, outputs, term) are at most 4n + 5m steps apart -/
theorem johnson_worst_case_delay (hst : s ≠ t) : ∀ x ∈ (obsSteps (johnson G s t)).zip (obsSteps (johnson G s t)).tail, x.2 - x.1 ≤ 4 * n + 5 * G.m := by
  intro ⟨u, w⟩ hx
  obtain ⟨a, c, hC, ⟨ha, hu⟩, ⟨hc, hw⟩⟩ := obs_consec _ hx
  have htally := tally G s t hC.lt hc hu hw
  have hbound := (johnson_runOK G s t hst).interval_bound hC
  simp only
  omega

/-- the run starts with the start event at step 0 -/
theorem johnson_head (hst : s ≠ t) : (johnson G s t).head? = some (.start 0) := by
  refine johnson_of_root (fun st => st.S = #[] ∧ st.blocked = Vector.replicate n false ∧ st.B = Vector.replicate n [] ∧ st.trace.toList = [Ev.start 0] ∧ SearchPre G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []) ∧ TrPre #[] (Vector.replicate n false) [Ev.start 0])
    (fun T => T.head? = some (.start 0)) ⟨rfl, rfl, rfl, rfl, root_pre hst, root_tr⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  obtain ⟨-, N, -, tc⟩ := (StateM.triple_iff _ _ _).mp (search_spec_tr G s t 0 s #[] (Vector.replicate n false) (Vector.replicate n []) [Ev.start 0]) st hpre
  obtain ⟨σe, E, hE, -⟩ := tc.ext
  simp [hE]

theorem zip_tail_mem {α : Type} (L : List α) (i : Nat) (hi : i + 1 < L.length) : (L[i]'(by omega), L[i + 1]) ∈ L.zip L.tail := by
  have h : i < (L.zip L.tail).length := by simp; omega
  have := List.getElem_mem h
  simpa [List.getElem_zip, List.getElem_tail] using this

/-- total time (Johnson's Corollary 2): the τ-th observable event happens after at most τ(4n + 5m) steps -/
theorem johnson_total_time (hst : s ≠ t) : ∀ τ (hτ : τ < (obsSteps (johnson G s t)).length), (obsSteps (johnson G s t))[τ] ≤ τ * (4 * n + 5 * G.m) := by
  have h0 : (obsSteps (johnson G s t)).head? = some 0 := by
    have hh := johnson_head G s t hst
    cases hT : johnson G s t with
    | nil => rw [hT] at hh; simp at hh
    | cons e rest => rw [hT] at hh; simp at hh; subst hh; simp [obsSteps]
  intro τ
  induction τ with
  | zero =>
    intro hτ
    have h0' : (obsSteps (johnson G s t))[0]? = some 0 := by rw [← List.head?_eq_getElem?]; exact h0
    rw [List.getElem?_eq_getElem hτ] at h0'
    simp at h0'
    omega
  | succ τ ih =>
    intro hτ
    have hprev := ih (by omega)
    have hmem := zip_tail_mem (obsSteps (johnson G s t)) τ hτ
    have hd := johnson_worst_case_delay G s t hst _ hmem
    simp only at hd
    rw [Nat.succ_mul]
    omega

end Johnson
