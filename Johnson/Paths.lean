/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Basic

/-!
  Paths and walks: the graph part of the proofs.  Copied from the BS-DFS formalization (Bsdfs/Sound.lean, Bsdfs/Paths.lean)
  and adapted to simple paths without a length bound.  `G.Reach X t x` says that some walk from x to t has all its nodes
  after x outside X.
-/

namespace Johnson

variable {n : Nat}

/-! ## Outputs -/

@[simp] theorem outputs_nil : outputs ([] : List (Ev n)) = [] := rfl

@[simp] theorem outputs_cons (e : Ev n) (l : List (Ev n)) : outputs (e :: l) = (match e with | .output _ p => [p] | _ => []) ++ outputs l := by
  cases e <;> rfl

@[simp] theorem outputs_append (l₁ l₂ : List (Ev n)) : outputs (l₁ ++ l₂) = outputs l₁ ++ outputs l₂ := List.filterMap_append

/-- no event of the trace is an `abort` -/
def NoAbort (tr : Array (Ev n)) : Prop := ∀ e ∈ tr.toList, e.isAbort = false

@[simp] theorem noAbort_push {tr : Array (Ev n)} {e : Ev n} : NoAbort (tr.push e) ↔ NoAbort tr ∧ e.isAbort = false := by
  simp [NoAbort, or_imp, forall_and]

/-! ## Paths as node lists -/

/-- an edge of l ++ [b] is an edge of l or the new last edge -/
theorem mem_zip_tail_snoc {α : Type} {l : List α} {b : α} {e : α × α} (he : e ∈ (l ++ [b]).zip (l ++ [b]).tail) : e ∈ l.zip l.tail ∨ (l.getLast? = some e.1 ∧ e.2 = b) := by
  induction l with
  | nil => simp at he
  | cons x l ih =>
    cases l with
    | nil => simp at he; simp [he]
    | cons y l =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he ih ⊢
      rcases he with he | he
      · exact Or.inl (Or.inl he)
      · rcases ih he with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (by simpa [List.getLast?_cons_cons] using h)

/-- L is a simple path from s with edges in G that avoids t (the stack invariant) -/
def StackPath (G : Graph n) (s t : Fin n) (L : List (Fin n)) : Prop :=
  L.head? = some s ∧ L.Nodup ∧ t ∉ L ∧ ∀ e ∈ L.zip L.tail, e.2 ∈ G.succ e.1

theorem nodup_snoc {α : Type} {L : List α} {w : α} (hnd : L.Nodup) (hw : w ∉ L) : (L ++ [w]).Nodup :=
  List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact hw ha⟩

/-- the edges of L ++ [v] ++ [w]: those of L ++ [v] and (v, w) -/
theorem edges_snoc {G : Graph n} {L : List (Fin n)} {v w : Fin n} (hedge : ∀ e ∈ (L ++ [v]).zip (L ++ [v]).tail, e.2 ∈ G.succ e.1) (hw : w ∈ G.succ v) :
    ∀ e ∈ (L ++ [v] ++ [w]).zip (L ++ [v] ++ [w]).tail, e.2 ∈ G.succ e.1 := by
  intro e he
  rcases mem_zip_tail_snoc he with h | ⟨h1, h2⟩
  · exact hedge e h
  · simp at h1; subst h1; rw [h2]; exact hw

theorem StackPath.snoc {G : Graph n} {s t v w : Fin n} {L : List (Fin n)} (hL : StackPath G s t (L ++ [v])) (hw : w ∈ G.succ v) (hwL : w ∉ L ++ [v]) (hwt : w ≠ t) : StackPath G s t (L ++ [v] ++ [w]) := by
  obtain ⟨hhead, hnd, hts, hedge⟩ := hL
  refine ⟨?_, nodup_snoc hnd hwL, ?_, edges_snoc hedge hw⟩
  · cases L <;> simp_all
  · simp only [List.mem_append, List.mem_singleton, not_or] at hts ⊢; exact ⟨⟨hts.1, hts.2⟩, fun h => hwt h.symm⟩

/-- a stack path closed by an edge to t is a simple s-t path -/
theorem StackPath.simple {G : Graph n} {s t v : Fin n} {L : List (Fin n)} (hL : StackPath G s t (L ++ [v])) (ht : t ∈ G.succ v) : G.SimplePath s t (L ++ [v] ++ [t]) := by
  obtain ⟨hhead, hnd, hts, hedge⟩ := hL
  refine ⟨?_, by simp, nodup_snoc hnd hts, edges_snoc hedge ht⟩
  cases L <;> simp_all

theorem StackPath.v_not_mem {G : Graph n} {s t v : Fin n} {L : List (Fin n)} (hL : StackPath G s t (L ++ [v])) : v ∉ L := by
  have := (List.nodup_append.mp hL.2.1).2.2
  exact fun hv => this v hv v (by simp) rfl

/-! ## Walks -/

/-- consecutive entries of W are edges of G -/
def Graph.Edges (G : Graph n) : List (Fin n) → Prop
  | x :: y :: rest => y ∈ G.succ x ∧ G.Edges (y :: rest)
  | _ => True

/-- a walk from x to t with l edges whose nodes after x avoid X -/
inductive Graph.Walk (G : Graph n) (X : List (Fin n)) (t : Fin n) : Fin n → Nat → Prop
  | refl : G.Walk X t t 0
  | step {x y : Fin n} {l : Nat} : y ∈ G.succ x → y ∉ X → G.Walk X t y l → G.Walk X t x (l + 1)

/-- some walk from x to t has all its nodes after x outside X -/
def Graph.Reach (G : Graph n) (X : List (Fin n)) (t x : Fin n) : Prop := ∃ l, G.Walk X t x l

theorem Graph.Walk.mono {G : Graph n} {X Y : List (Fin n)} {t x : Fin n} {l : Nat} (hXY : ∀ z, z ∈ X → z ∈ Y) (hw : G.Walk Y t x l) : G.Walk X t x l := by
  induction hw with
  | refl => exact .refl
  | step hxy hy _ ih => exact .step hxy (fun h => hy (hXY _ h)) ih

theorem Graph.Reach.mono {G : Graph n} {X Y : List (Fin n)} {t x : Fin n} (hXY : ∀ z, z ∈ X → z ∈ Y) (h : G.Reach Y t x) : G.Reach X t x := by
  obtain ⟨l, hw⟩ := h
  exact ⟨l, hw.mono hXY⟩

theorem Graph.Reach.step {G : Graph n} {X : List (Fin n)} {t x y : Fin n} (hxy : y ∈ G.succ x) (hy : y ∉ X) (h : G.Reach X t y) : G.Reach X t x := by
  obtain ⟨l, hw⟩ := h
  exact ⟨l + 1, .step hxy hy hw⟩

theorem Graph.edges_cons_cons {G : Graph n} {x y : Fin n} {rest : List (Fin n)} : G.Edges (x :: y :: rest) ↔ y ∈ G.succ x ∧ G.Edges (y :: rest) := Iff.rfl

theorem Graph.edges_iff_zip (G : Graph n) (W : List (Fin n)) : G.Edges W ↔ ∀ e ∈ W.zip W.tail, e.2 ∈ G.succ e.1 := by
  induction W with
  | nil => simp [Graph.Edges]
  | cons x W ih =>
    cases W with
    | nil => simp [Graph.Edges]
    | cons y W =>
      simp only [Graph.edges_cons_cons, ih, List.tail_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]

theorem Graph.Edges.of_append_right {G : Graph n} {A B : List (Fin n)} (h : G.Edges (A ++ B)) : G.Edges B := by
  induction A with
  | nil => simpa using h
  | cons a A ih =>
    apply ih
    cases A with
    | nil => cases B with
      | nil => trivial
      | cons b B => exact h.2
    | cons a' A => exact h.2

theorem Graph.Edges.append_cons {G : Graph n} {A B : List (Fin n)} {v : Fin n} (hA : G.Edges (A ++ [v])) (hB : G.Edges (v :: B)) : G.Edges (A ++ v :: B) := by
  induction A with
  | nil => simpa using hB
  | cons a A ih =>
    cases A with
    | nil => exact ⟨hA.1, hB⟩
    | cons a' A => exact ⟨hA.1, ih hA.2⟩

theorem Graph.edges_of_stack {G : Graph n} {s t : Fin n} {L : List (Fin n)} (h : StackPath G s t L) : G.Edges L := (Graph.edges_iff_zip G L).mpr h.2.2.2

/-- a list path gives a walk -/
theorem Graph.walk_of_list {G : Graph n} {X : List (Fin n)} {t : Fin n} : ∀ (R : List (Fin n)) (y : Fin n), R.head? = some y → R.getLast? = some t → G.Edges R → (∀ z ∈ R.tail, z ∉ X) → G.Walk X t y (R.length - 1)
  | [], _, h, _, _, _ => by simp at h
  | [x], y, h1, h2, _, _ => by simp at h1 h2; subst h1; subst h2; exact .refl
  | x :: z :: R, y, h1, h2, he, hX => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have hz : z ∉ X := hX z (by simp)
    have ih := Graph.walk_of_list (X := X) (z :: R) z rfl (by simpa using h2) he.2 (fun w hw => hX w (by simp at hw ⊢; exact Or.inr hw))
    simpa using Graph.Walk.step he.1 hz ih

/-- shortcut: a walk contains a simple path with the same ends, no longer, avoiding the same nodes -/
theorem Graph.Walk.path {G : Graph n} {X : List (Fin n)} {t x : Fin n} {l : Nat} (hw : G.Walk X t x l) : ∃ R : List (Fin n), R.head? = some x ∧ R.getLast? = some t ∧ G.Edges R ∧ R.Nodup ∧ (∀ z ∈ R.tail, z ∉ X) ∧ R.length ≤ l + 1 := by
  induction hw with
  | refl => exact ⟨[t], rfl, rfl, trivial, by simp, by simp, by simp⟩
  | @step x y l hxy hy _ ih =>
    obtain ⟨R, h1, h2, he, hnd, hX, hlen⟩ := ih
    cases R with
    | nil => simp at h1
    | cons y' R =>
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      by_cases hx : x ∈ y' :: R
      · obtain ⟨A, B, hAB⟩ := List.append_of_mem hx
        refine ⟨x :: B, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hAB] at h2; simpa using h2
        · rw [hAB] at he; exact he.of_append_right
        · rw [hAB] at hnd; exact (List.nodup_append.mp hnd).2.1
        · intro z hz
          simp only [List.tail_cons] at hz
          cases A with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hAB
            obtain ⟨-, rfl⟩ := hAB
            exact hX z (by simpa using hz)
          | cons a A =>
            simp only [List.cons_append, List.cons.injEq] at hAB
            obtain ⟨-, rfl⟩ := hAB
            exact hX z (by simp [hz])
        · have : (y' :: R).length = A.length + 1 + B.length := by rw [hAB]; simp; omega
          simp at this hlen ⊢; omega
      · refine ⟨x :: y' :: R, rfl, by simpa using h2, ⟨hxy, he⟩, List.nodup_cons.mpr ⟨hx, hnd⟩, ?_, by simp at hlen ⊢; omega⟩
        intro z hz
        simp only [List.tail_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hy
        · exact hX z (by simpa using hz)

/-! ## Simple paths with a given prefix -/

theorem eq_of_prefix_snoc {α : Type} {L p : List α} {a c : α} (ha : (L ++ [a]) <+: p) (hc : (L ++ [c]) <+: p) : a = c := by
  have h1 := ha.getElem (i := L.length) (by simp)
  have h2 := hc.getElem (i := L.length) (by simp)
  simp at h1 h2
  exact h1.trans h2.symm

theorem eq_of_prefix_pair {α : Type} {L p : List α} {v a c : α} (ha : (L ++ [v, a]) <+: p) (hc : (L ++ [v, c]) <+: p) : a = c := by
  have e1 : L ++ [v, a] = (L ++ [v]) ++ [a] := by simp
  have e2 : L ++ [v, c] = (L ++ [v]) ++ [c] := by simp
  rw [e1] at ha; rw [e2] at hc
  exact eq_of_prefix_snoc ha hc

theorem prefix_of_pair {α : Type} {L p : List α} {v w : α} (h : (L ++ [v, w]) <+: p) : (L ++ [v]) <+: p :=
  List.IsPrefix.trans ⟨[w], by simp⟩ h

theorem head_append_cons {α : Type} {L R : List α} {v : α} : (L ++ v :: R).head? = (L ++ [v]).head? := by
  cases L <;> simp

theorem prefix_of_head {α : Type} {s : α} {p : List α} (h : p.head? = some s) : [s] <+: p := by
  cases p with
  | nil => simp at h
  | cons a p => simp at h; subst h; exact ⟨p, rfl⟩

theorem nodup_length_le (l : List (Fin n)) (h : l.Nodup) : l.length ≤ n := by
  have := h.length_le_of_subset (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa using this

/-- a simple path with prefix L ++ [v] continues with an edge (v, w) -/
theorem Graph.SimplePath.cont {G : Graph n} {s t v : Fin n} {L p : List (Fin n)} (hp : G.SimplePath s t p) (hpre : (L ++ [v]) <+: p) (ht : t ∉ L ++ [v]) : ∃ w rest, p = L ++ [v, w] ++ rest ∧ w ∈ G.succ v := by
  obtain ⟨R, rfl⟩ := hpre
  obtain ⟨-, hlast, -, hedge⟩ := hp
  cases R with
  | nil => simp at hlast; exact absurd (by simp [hlast]) ht
  | cons w rest =>
    refine ⟨w, rest, by simp, ?_⟩
    rw [← Graph.edges_iff_zip] at hedge
    have : G.Edges ([v, w] ++ rest) := Graph.Edges.of_append_right (A := L) (by simpa using hedge)
    exact this.1

theorem Graph.SimplePath.eq_of_prefix_t {G : Graph n} {s t v : Fin n} {L p : List (Fin n)} (hp : G.SimplePath s t p) (hpre : (L ++ [v, t]) <+: p) : p = L ++ [v, t] := by
  obtain ⟨R, rfl⟩ := hpre
  obtain ⟨-, hlast, hnd, -⟩ := hp
  cases R with
  | nil => simp
  | cons r R =>
    exfalso
    have h' : (r :: R).getLast? = some t := by
      rw [List.getLast?_append] at hlast
      cases h : (r :: R).getLast? with
      | none => simp at h
      | some a => rw [h] at hlast; simpa using hlast
    exact (List.nodup_append.mp hnd).2.2 t (by simp) t (List.mem_of_getLast? h') rfl

theorem Graph.SimplePath.not_prefix_of_mem {G : Graph n} {s t v w : Fin n} {L p : List (Fin n)} (hp : G.SimplePath s t p) (hw : w ∈ L ++ [v]) : ¬ (L ++ [v, w]) <+: p := by
  rintro ⟨R, rfl⟩
  obtain ⟨-, -, hnd, -⟩ := hp
  have : (L ++ [v] ++ [w]).Nodup := (List.nodup_append.mp (by simpa using hnd)).1
  rw [List.nodup_append] at this
  exact this.2.2 w hw w (by simp) rfl

/-- the suffix of a simple path from the last node of a prefix is a walk avoiding the prefix -/
theorem Graph.SimplePath.suffix_walk {G : Graph n} {s t v : Fin n} {L p : List (Fin n)} (hp : G.SimplePath s t p) (hpre : (L ++ [v]) <+: p) : G.Walk (L ++ [v]) t v (p.length - L.length - 1) := by
  obtain ⟨R, rfl⟩ := hpre
  obtain ⟨-, hlast, hnd, hedge⟩ := hp
  rw [← Graph.edges_iff_zip] at hedge
  have hnd' : (L ++ [v] ++ R).Nodup := by simpa using hnd
  have hw := Graph.walk_of_list (G := G) (X := L ++ [v]) (t := t) (v :: R) v rfl ?_ (Graph.Edges.of_append_right (A := L) (by simpa using hedge)) ?_
  · simpa using hw
  · rw [List.append_assoc, List.getLast?_append] at hlast
    cases h : (v :: R).getLast? with
    | none => simp at h
    | some a => simp only [List.singleton_append] at hlast; rw [h] at hlast; simpa using hlast
  · intro z hz hzL
    simp only [List.tail_cons] at hz
    exact (List.nodup_append.mp hnd').2.2 z hzL z hz rfl

/-- a stack path continued by a simple path that avoids it is a simple s-t path -/
theorem StackPath.append_path {G : Graph n} {s t v : Fin n} {L R : List (Fin n)} (hL : StackPath G s t (L ++ [v])) (hRl : R.getLast? = some t) (hRe : G.Edges (v :: R)) (hRnd : (v :: R).Nodup) (hRX : ∀ z ∈ R, z ∉ L) :
    G.SimplePath s t (L ++ v :: R) := by
  have hLv : (L ++ [v]).Nodup := hL.2.1
  have hvL := hL.v_not_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [head_append_cons]; exact hL.1
  · rw [List.getLast?_append]
    cases h : (v :: R).getLast? with
    | none => simp at h
    | some a =>
      cases R with
      | nil => simp at hRl
      | cons r R => simp only [List.getLast?_cons_cons] at h; rw [hRl] at h; cases h; simp
  · refine List.nodup_append.mpr ⟨(List.nodup_append.mp hLv).1, hRnd, ?_⟩
    intro a ha c hc hac
    subst hac
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hvL ha
    · exact hRX a hc ha
  · rw [← Graph.edges_iff_zip]; exact Graph.Edges.append_cons (Graph.edges_of_stack hL) hRe

end Johnson
