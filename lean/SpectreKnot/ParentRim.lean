/-
The parent's rim, read from Table 3: position `p` of the rim of `compose T child` is edge `k` of child `c`'s rim
(`ownGo`). Its properties, for any side lengths: the positions are distinct edges, they are exactly the children's
rim edges that the composition leaves unglued, and consecutive positions meet at a parent rim vertex in the sense of
`Gluing.Rot` (a table check, `consec_ok`).
-/
import SpectreKnot.ComposeTiles

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### Rims made of pieces -/

section Own

variable (L : Nat → Nat → Nat)

/-- The total length of the pieces. -/
def totL : List (Nat × Nat) → Nat
  | [] => 0
  | (c, j) :: rest => L c j + totL rest

/-- Position `p` of a rim made of the pieces `pcs`, each a side `j` of a child `c` traversed backwards: the edge
`(c, k)` of the child there. -/
def ownGo : List (Nat × Nat) → Nat → Nat × Nat
  | [], _ => (0, 0)
  | (c, j) :: rest, p => if p < L c j then (c, pos (L c) j + L c j - 1 - p) else ownGo rest (p - L c j)

/-- `Consec pcs a b`: the piece `b` comes right after the piece `a` in `pcs`. -/
inductive Consec : List (Nat × Nat) → Nat × Nat → Nat × Nat → Prop
  | here {a b : Nat × Nat} {rest : List (Nat × Nat)} : Consec (a :: b :: rest) a b
  | there {x a b : Nat × Nat} {rest : List (Nat × Nat)} : Consec rest a b → Consec (x :: rest) a b

variable {L}

/-- Both pieces of a consecutive pair are in the list. -/
theorem Consec.mem {l : List (Nat × Nat)} {a b : Nat × Nat} (consec : Consec l a b) : a ∈ l ∧ b ∈ l := by
  induction consec with
  | here => exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
  | there _ ih => exact ⟨List.mem_cons_of_mem _ ih.1, List.mem_cons_of_mem _ ih.2⟩

/-- Two lists of pieces, one after the other, have the sum of their lengths. -/
theorem totL_append (l₁ l₂ : List (Nat × Nat)) : totL L (l₁ ++ l₂) = totL L l₁ + totL L l₂ := by
  induction l₁ with
  | nil => simp [totL]
  | cons x l ih => obtain ⟨c, j⟩ := x; simp only [List.cons_append, totL, ih]; omega

/-- A position in two lists of pieces, one after the other: in the first list if it is below the first's length,
otherwise in the second, counted from the second's start. -/
theorem ownGo_append (l₁ l₂ : List (Nat × Nat)) (p : Nat) :
    ownGo L (l₁ ++ l₂) p = if p < totL L l₁ then ownGo L l₁ p else ownGo L l₂ (p - totL L l₁) := by
  induction l₁ generalizing p with
  | nil => simp [totL]
  | cons x l ih =>
    obtain ⟨c, j⟩ := x
    simp only [List.cons_append, ownGo, totL]
    by_cases in_head : p < L c j
    · have in_l₁ : p < L c j + totL L l := by omega -- in the first piece, so within `l₁`
      simp [in_head, in_l₁]
    · rw [ih]
      by_cases in_rest : p - L c j < totL L l
      · have in_l₁ : p < L c j + totL L l := by omega -- past the first piece, but within `l₁`
        simp [in_head, in_rest, in_l₁]
      · have past_l₁ : ¬ p < L c j + totL L l := by omega -- past the whole of `l₁`
        simp only [in_head, in_rest, past_l₁, if_false]
        congr 1; omega

/-- Every position below the total length is an edge `pos j + o` of a listed side `(c, j)`, with `o` inside the
side. -/
theorem ownGo_mem : ∀ (pcs : List (Nat × Nat)) (p : Nat), p < totL L pcs →
    ∃ c j o, (c, j) ∈ pcs ∧ o < L c j ∧ ownGo L pcs p = (c, pos (L c) j + o) := by
  intro pcs
  induction pcs with
  | nil => intro p p_lt; simp [totL] at p_lt
  | cons x rest ih =>
    obtain ⟨c, j⟩ := x
    intro p p_lt
    simp only [totL] at p_lt
    simp only [ownGo]
    by_cases in_head : p < L c j
    · -- in the first piece, counted from the end of its side
      rw [if_pos in_head]
      exact ⟨c, j, L c j - 1 - p, List.mem_cons_self, by omega, by congr 1; omega⟩
    · -- in a later piece
      rw [if_neg in_head]
      obtain ⟨c', j', o, mem, o_lt, at_p⟩ := ih (p - L c j) (by omega)
      exact ⟨c', j', o, List.mem_cons_of_mem _ mem, o_lt, at_p⟩

/-- Every edge of every listed side is at some position. -/
theorem ownGo_surj : ∀ (pcs : List (Nat × Nat)) {c j o : Nat}, (c, j) ∈ pcs → o < L c j →
    ∃ p, p < totL L pcs ∧ ownGo L pcs p = (c, pos (L c) j + o) := by
  intro pcs
  induction pcs with
  | nil => intro c j o mem; simp at mem
  | cons x rest ih =>
    obtain ⟨c', j'⟩ := x
    intro c j o mem o_lt
    rcases List.mem_cons.mp mem with is_head | in_rest
    · -- the first piece: counted from the end of its side
      simp only [Prod.mk.injEq] at is_head
      obtain ⟨rfl, rfl⟩ := is_head
      refine ⟨L c j - 1 - o, by simp only [totL]; omega, ?_⟩
      simp only [ownGo]
      rw [if_pos (by omega)]
      congr 1; omega
    · -- a later piece: after the first
      obtain ⟨p, p_lt, at_p⟩ := ih in_rest o_lt
      refine ⟨L c' j' + p, by simp only [totL]; omega, ?_⟩
      simp only [ownGo]
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      exact at_p

/-- Positions in a side are distinct from those in another side of the same child. -/
theorem side_pos_inj {f : Nat → Nat} (len_pos : ∀ i, i < 6 → 1 ≤ f i) {j j' o o' : Nat} (j_lt : j < 6)
    (j_lt' : j' < 6) (o_lt : o < f j) (o_lt' : o' < f j') (same_pos : pos f j + o = pos f j' + o') :
    j = j' ∧ o = o' := by
  -- the side lookup at the position finds `j`
  have side_j := sideIdx_eq f len_pos j_lt o_lt
  -- and at the same position it finds `j'`
  have side_j' := sideIdx_eq f len_pos j_lt' o_lt'
  rw [same_pos] at side_j
  rw [side_j] at side_j'
  subst side_j'
  exact ⟨rfl, by omega⟩

/-- On a list of distinct sides, different positions are different edges. -/
theorem ownGo_inj (len_pos : ∀ c j, j < 6 → 1 ≤ L c j) : ∀ (pcs : List (Nat × Nat)), pcs.Nodup →
    (∀ x ∈ pcs, x.2 < 6) → ∀ p p', p < totL L pcs → p' < totL L pcs → ownGo L pcs p = ownGo L pcs p' → p = p' := by
  intro pcs
  induction pcs with
  | nil => intro _ _ p p' p_lt; simp [totL] at p_lt
  | cons x rest ih =>
    obtain ⟨c, j⟩ := x
    intro nodup sides_lt p p' p_lt p_lt' same_edge
    rw [List.nodup_cons] at nodup
    simp only [totL] at p_lt p_lt'
    simp only [ownGo] at same_edge
    -- the first piece is an actual side
    have j_lt : j < 6 := sides_lt (c, j) List.mem_cons_self
    -- and so are the later pieces
    have rest_lt : ∀ x ∈ rest, x.2 < 6 := fun x mem => sides_lt x (List.mem_cons_of_mem _ mem)
    -- an edge of the first piece is not an edge of a later piece
    have sep : ∀ q q', q < L c j → q' < totL L rest → (c, pos (L c) j + L c j - 1 - q) ≠ ownGo L rest q' := by
      intro q q' q_lt q_lt' same
      obtain ⟨c₂, j₂, o₂, mem, o₂_lt, at_q'⟩ := ownGo_mem rest q' q_lt'
      rw [at_q'] at same
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, same_pos⟩ := same
      -- the same edge of the same child: the same side, which the list would then hold twice
      have same_side := side_pos_inj (len_pos c) j_lt (rest_lt _ mem) (show L c j - 1 - q < L c j by omega) o₂_lt
        (by rw [← same_pos]; omega)
      exact nodup.1 (same_side.1 ▸ mem)
    by_cases in_head : p < L c j <;> by_cases in_head' : p' < L c j
    · -- both in the first piece
      rw [if_pos in_head, if_pos in_head'] at same_edge
      simp only [Prod.mk.injEq] at same_edge
      omega
    · rw [if_pos in_head, if_neg in_head'] at same_edge
      exact absurd same_edge (sep p (p' - L c j) in_head (by omega))
    · rw [if_neg in_head, if_pos in_head'] at same_edge
      exact absurd same_edge.symm (sep p' (p - L c j) in_head' (by omega))
    · rw [if_neg in_head, if_neg in_head'] at same_edge
      -- both in later pieces: by induction
      have := ih nodup.2 rest_lt (p - L c j) (p' - L c j) (by omega) (by omega) same_edge
      omega

/-- Position 0 is the last edge of the first piece's side (sides are traversed backwards). -/
theorem ownGo_zero {c j : Nat} {rest : List (Nat × Nat)} (len_pos : 1 ≤ L c j) :
    ownGo L ((c, j) :: rest) 0 = (c, pos (L c) j + L c j - 1) := by
  simp only [ownGo]; rw [if_pos (show 0 < L c j by omega)]; rfl

/-- The last position is the first edge of the last piece's side. -/
theorem ownGo_last {c j : Nat} (len_pos : 1 ≤ L c j) : ∀ (pcs : List (Nat × Nat)),
    ownGo L (pcs ++ [(c, j)]) (totL L (pcs ++ [(c, j)]) - 1) = (c, pos (L c) j) := by
  intro pcs
  -- the last piece adds its side's length
  have total : totL L (pcs ++ [(c, j)]) = totL L pcs + L c j := by rw [totL_append]; simp [totL]
  rw [ownGo_append, total, if_neg (show ¬ (totL L pcs + L c j - 1 < totL L pcs) by omega),
    show totL L pcs + L c j - 1 - totL L pcs = L c j - 1 by omega]
  simp only [ownGo]
  rw [if_pos (show L c j - 1 < L c j by omega)]
  congr 1; omega

/-- Going back one position: inside a piece, the next edge of the same side (in the children's sense); at the start
of a piece, the first edge of the previous piece. -/
theorem ownGo_pred (len_pos : ∀ c j, 1 ≤ L c j) : ∀ (pcs : List (Nat × Nat)) (p : Nat), 0 < p → p < totL L pcs →
    (∃ c j o, (c, j) ∈ pcs ∧ o + 1 < L c j ∧ ownGo L pcs p = (c, pos (L c) j + o) ∧
      ownGo L pcs (p - 1) = (c, pos (L c) j + o + 1)) ∨
    (∃ c j c' j', Consec pcs (c', j') (c, j) ∧ ownGo L pcs p = (c, pos (L c) j + L c j - 1) ∧
      ownGo L pcs (p - 1) = (c', pos (L c') j')) := by
  intro pcs
  induction pcs with
  | nil => intro p _ p_lt; simp [totL] at p_lt
  | cons x rest ih =>
    obtain ⟨c, j⟩ := x
    intro p p_pos p_lt
    simp only [totL] at p_lt
    by_cases in_head : p < L c j
    · -- inside the first piece
      left
      refine ⟨c, j, L c j - 1 - p, List.mem_cons_self, by omega, ?_, ?_⟩
      · simp only [ownGo]; rw [if_pos in_head]; congr 1; omega
      · simp only [ownGo]; rw [if_pos (by omega)]; congr 1; omega
    · by_cases at_start : p = L c j
      · -- at the start of the second piece: the step back is into the first
        right
        subst at_start
        cases rest with
        | nil => simp [totL] at p_lt
        | cons y rest' =>
          obtain ⟨c₂, j₂⟩ := y
          refine ⟨c₂, j₂, c, j, .here, ?_, ?_⟩
          · simp only [ownGo]
            rw [if_neg (show ¬ (L c j < L c j) by omega), Nat.sub_self,
              if_pos (show 0 < L c₂ j₂ from len_pos c₂ j₂)]
            rfl
          · simp only [ownGo]; rw [if_pos (by omega)]; congr 1; omega
      · -- further on: by induction, in the rest of the list
        -- a positive position in the rest of the list
        have past_pos : 0 < p - L c j := by omega
        rcases ih (p - L c j) past_pos (by omega) with
          ⟨c', j', o, mem, o_lt, at_p, at_prev⟩ | ⟨c', j', c'', j'', consec, at_p, at_prev⟩
        · left
          refine ⟨c', j', o, List.mem_cons_of_mem _ mem, o_lt, ?_, ?_⟩
          · simp only [ownGo]; rw [if_neg in_head]; exact at_p
          · simp only [ownGo]; rw [if_neg (by omega), show p - 1 - L c j = p - L c j - 1 by omega]; exact at_prev
        · right
          refine ⟨c', j', c'', j'', .there consec, ?_, ?_⟩
          · simp only [ownGo]; rw [if_neg in_head]; exact at_p
          · simp only [ownGo]; rw [if_neg (by omega), show p - 1 - L c j = p - L c j - 1 by omega]; exact at_prev

end Own

/-! ### Table 3 as a rim, and Table 2 at the vertices -/

/-- The parent's rim pieces, in order (Table 3 flattened). -/
def pcs (T : Kind) : List (Nat × Nat) := (pside T).flatMap id

/-- Turning about vertex `v` of child `c` by Table 2 alone: while the side starting at the vertex is glued to side
`j₂` of a sibling `c₂`, go on to the vertex where that side ends, vertex `j₂ + 1` of `c₂`. -/
def tabRot (T : Kind) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, (c, v) =>
    match adjAt T c v with
    | none => some (c, v)
    | some (c₂, j₂) => tabRot T f (c₂, (j₂ + 1) % 6)

/-- Consecutive pieces `a`, `b` of the parent's rim meet at a parent rim vertex: turning about the vertex where side
`b` ends (in the children's sense, where the parent's side runs into piece `a`) reaches the vertex where side `a`
begins. -/
def consecOk (T : Kind) : List (Nat × Nat) → Bool
  | a :: b :: rest => tabRot T 30 (b.1, (b.2 + 1) % 6) == some a && consecOk T (b :: rest)
  | _ => true

/-- The checks on Tables 2 and 3 that make Table 3 the rim of the glued children. -/
def rimTablesOk (T : Kind) : Bool :=
  ((pcs T).all fun x => decide (x.1 < nk T) && decide (x.2 < 6) && (adjAt T x.1 x.2).isNone) &&
  decide (pcs T).Nodup &&
  ((List.range (nk T)).all fun c => (List.range 6).all fun j => (adjAt T c j).isSome || (pcs T).contains (c, j)) &&
  consecOk T (pcs T) &&
  match (pcs T).head?, (pcs T).getLast? with
  | some a, some b => tabRot T 30 (a.1, (a.2 + 1) % 6) == some b
  | _, _ => false

/-- The table checks pass for all nine kinds. -/
theorem rimTablesOk_all : ∀ T, rimTablesOk T = true := by intro T; cases T <;> decide

/-- The check `consecOk` is sound: for consecutive pieces `a`, `b` of a checked list, turning about the vertex where
side `b` ends reaches the vertex where side `a` begins. -/
theorem consecOk_sound {T : Kind} : ∀ {l : List (Nat × Nat)} {a b : Nat × Nat}, consecOk T l = true →
    Consec l a b → tabRot T 30 (b.1, (b.2 + 1) % 6) = some a := by
  intro l a b ok consec
  induction consec with
  | here => simp only [consecOk, Bool.and_eq_true, beq_iff_eq] at ok; exact ok.1
  | @there x a b rest rest_consec ih =>
    apply ih
    cases rest with
    | nil => cases rest_consec
    | cons y rest => simp only [consecOk, Bool.and_eq_true] at ok; exact ok.2

section Facts

variable (T : Kind)

/-- Each piece of Table 3 is a side of an actual child, and Table 2 puts that side on the parent's rim. -/
theorem pcs_valid : ∀ x ∈ pcs T, x.1 < nk T ∧ x.2 < 6 ∧ adjAt T x.1 x.2 = none := by
  intro x mem
  -- the table checks for this kind
  have ok := rimTablesOk_all T
  simp only [rimTablesOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at ok
  exact ⟨(ok.1.1.1.1 x mem).1.1, (ok.1.1.1.1 x mem).1.2, (ok.1.1.1.1 x mem).2⟩

/-- Table 3 lists no side twice. -/
theorem pcs_nodup : (pcs T).Nodup := by
  -- the table checks for this kind
  have ok := rimTablesOk_all T
  simp only [rimTablesOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ok.1.1.1.2

/-- Every side of a child that Table 2 puts on the parent's rim is listed in Table 3. -/
theorem pcs_cover {c j : Nat} (c_lt : c < nk T) (j_lt : j < 6) (on_rim : adjAt T c j = none) : (c, j) ∈ pcs T := by
  -- the table checks for this kind
  have ok := rimTablesOk_all T
  simp only [rimTablesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Option.isSome_iff_exists, List.contains_iff_mem] at ok
  rcases ok.1.1.2 c c_lt j j_lt with ⟨x, glued⟩ | mem
  · rw [on_rim] at glued; contradiction
  · exact mem

/-- Consecutive pieces of Table 3 meet at a vertex: turning about the vertex where side `b` ends reaches the vertex
where side `a` begins. -/
theorem pcs_consec {a b : Nat × Nat} (consec : Consec (pcs T) a b) : tabRot T 30 (b.1, (b.2 + 1) % 6) = some a := by
  -- the table checks for this kind
  have ok := rimTablesOk_all T
  simp only [rimTablesOk, Bool.and_eq_true] at ok
  exact consecOk_sound ok.1.2 consec

/-- Table 3 is not empty. -/
theorem pcs_ne : pcs T ≠ [] := by cases T <;> decide

/-- The parent's rim closes up: the last piece of Table 3 meets the first, as consecutive pieces do. -/
theorem pcs_wrap : tabRot T 30 (((pcs T).head (pcs_ne T)).1, (((pcs T).head (pcs_ne T)).2 + 1) % 6) =
    some ((pcs T).getLast (pcs_ne T)) := by
  -- the table checks for this kind
  have ok := rimTablesOk_all T
  simp only [rimTablesOk, Bool.and_eq_true] at ok
  -- the last check: the wrap-around, in terms of `head?` and `getLast?`
  have wrap_ok := ok.2
  rw [List.head?_eq_some_head (pcs_ne T), List.getLast?_eq_some_getLast (pcs_ne T)] at wrap_ok
  simpa using wrap_ok

end Facts

/-! ### The rim of the composition `Comp.ofLens` -/

section Rot

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- With positive side lengths `f`, the position after the last edge of side `j` is vertex `j + 1` (vertex 0 after
side 5). -/
theorem nxt_last {f : Nat → Nat} (len_pos : ∀ i, 1 ≤ f i) {j : Nat} (j_lt : j < 6) :
    nxt (pos f 6) (pos f j + f j - 1) = pos f ((j + 1) % 6) := by
  -- side `j` has an edge
  have len_j := len_pos j
  rcases (show j = 5 ∨ j < 5 by omega) with rfl | j_lt5
  · -- the last side
    -- its last edge is the last on the rim, so the next position wraps round to 0
    have wraps : pos f 5 + f 5 - 1 + 1 = pos f 6 := by
      rw [show pos f 6 = pos f 5 + f 5 from pos_succ f 5]; omega
    simp only [nxt]; rw [if_pos wraps]; rfl
  · -- an earlier side: no wrap-around
    -- vertex `j + 1` is before the end of the rim
    have before_end := pos_lt_of_pos f (fun i _ => len_pos i) (show j + 1 < 6 by omega) (Nat.le_refl 6)
    -- and is where side `j` ends
    have pos_next : pos f (j + 1) = pos f j + f j := pos_succ f j
    -- side `j + 1` has an edge
    have len_next := len_pos (j + 1)
    simp only [nxt]
    rw [if_neg (show ¬ (pos f j + f j - 1 + 1 = pos f 6) by omega), Nat.mod_eq_of_lt (show j + 1 < 6 by omega)]
    omega

/-- An edge of a side that Table 2 puts on the parent's rim is unglued in the composition. -/
theorem ofLens_mate_none (len_pos : ∀ c j, 1 ≤ L c j) {c j o : Nat} (c_lt : c < nk T) (j_lt : j < 6)
    (o_lt : o < L c j) (on_rim : adjAt T c j = none) :
    (Comp.ofLens T L d ω).toGluing.mate c (pos (L c) j + o) = none := by
  show (Comp.ofLens T L d ω).mate c (pos (L c) j + o) = none
  rw [ofLens_mate (fun c _ j _ => len_pos c j) c_lt j_lt o_lt, on_rim]; rfl

/-- Turning about a vertex of a child, in the composition, follows Table 2. -/
theorem rot_tab (len_pos : ∀ c j, 1 ≤ L c j) : ∀ f c v c' v', tabRot T f (c, v) = some (c', v') → c < nk T → v < 6 →
    (Comp.ofLens T L d ω).toGluing.Rot (c, pos (L c) v) (c', pos (L c') v') := by
  intro f
  induction f with
  | zero => intro c v c' v' found; simp [tabRot] at found
  | succ f ih =>
    intro c v c' v' found c_lt v_lt
    simp only [tabRot] at found
    cases adj_eq : adjAt T c v with
    | none =>
      -- side `v` is on the parent's rim: turning stops here
      rw [adj_eq] at found
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      -- the first edge of the side is unglued
      have unglued := ofLens_mate_none (d := d) (ω := ω) len_pos c_lt v_lt (show 0 < L c v from len_pos c v) adj_eq
      rw [Nat.add_zero] at unglued
      exact .stop unglued
    | some p =>
      -- side `v` is glued to side `j₂` of `c₂`: turn on from the end of that side
      obtain ⟨c₂, j₂⟩ := p
      rw [adj_eq] at found
      obtain ⟨c₂_lt, j₂_lt, _, _⟩ := adj_valid c_lt v_lt adj_eq
      -- the first edge of side `v` is glued to the last edge of side `j₂` of `c₂`
      have mate_eq : (Comp.ofLens T L d ω).toGluing.mate c (pos (L c) v) =
          some (c₂, pos (L c₂) j₂ + L c₂ j₂ - 1) := by
        show (Comp.ofLens T L d ω).mate c (pos (L c) v) = _
        -- Table 2's gluing, at offset 0
        have mate_formula :=
          ofLens_mate (d := d) (ω := ω) (fun c _ j _ => len_pos c j) c_lt v_lt (show 0 < L c v from len_pos c v)
        rw [Nat.add_zero, adj_eq] at mate_formula
        rw [mate_formula]; rfl
      refine .step mate_eq ?_
      rw [ofLens_E c₂_lt, nxt_last (len_pos c₂) j₂_lt]
      exact ih _ _ _ _ found c₂_lt (Nat.mod_lt _ (by omega))

variable (T L)

/-- The parent's rim length. -/
abbrev rimN : Nat := totL L (pcs T)

variable {T L}

/-- Each parent rim position is an edge of a listed side, which Table 2 puts on the parent's rim. -/
theorem own_valid {p : Nat} (p_lt : p < rimN T L) :
    ∃ c j o, (c, j) ∈ pcs T ∧ c < nk T ∧ j < 6 ∧ adjAt T c j = none ∧ o < L c j ∧
      ownGo L (pcs T) p = (c, pos (L c) j + o) := by
  obtain ⟨c, j, o, mem, o_lt, at_p⟩ := ownGo_mem (pcs T) p p_lt
  obtain ⟨c_lt, j_lt, on_rim⟩ := pcs_valid T _ mem
  exact ⟨c, j, o, mem, c_lt, j_lt, on_rim, o_lt, at_p⟩

/-- Every parent rim position is a rim edge of the composition. -/
theorem own_mate (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (ownGo L (pcs T) p).1 < nk T ∧ (ownGo L (pcs T) p).2 < pos (L (ownGo L (pcs T) p).1) 6 ∧
    (Comp.ofLens T L d ω).toGluing.mate (ownGo L (pcs T) p).1 (ownGo L (pcs T) p).2 = none := by
  obtain ⟨c, j, o, _, c_lt, j_lt, on_rim, o_lt, at_p⟩ := own_valid p_lt
  rw [at_p]
  dsimp only
  refine ⟨c_lt, ?_, ofLens_mate_none len_pos c_lt j_lt o_lt on_rim⟩
  -- side `j` ends where side `j + 1` starts
  have := pos_lt_of_pos (L c) (fun i _ => len_pos c i) (show j < j + 1 by omega) (show j + 1 ≤ 6 by omega)
  -- and ends no later than the rim
  have side_end := pos_mono (L c) (show j + 1 ≤ 6 by omega)
  rw [pos_succ] at side_end; omega

/-- Every rim edge of the composition is a parent rim position. -/
theorem own_surj (len_pos : ∀ c j, 1 ≤ L c j) {c k : Nat} (c_lt : c < nk T) (k_lt : k < pos (L c) 6)
    (unglued : (Comp.ofLens T L d ω).toGluing.mate c k = none) :
    ∃ p, p < rimN T L ∧ ownGo L (pcs T) p = (c, k) := by
  obtain ⟨j, o, j_lt, o_lt, rfl⟩ := decomp (L c) 6 (Nat.le_refl _) k k_lt
  -- an unglued edge lies on a side that Table 2 puts on the parent's rim
  have on_rim : adjAt T c j = none := by
    -- Table 2's gluing at this edge
    have mate_formula := ofLens_mate (d := d) (ω := ω) (fun c _ j _ => len_pos c j) c_lt j_lt o_lt
    cases adj_eq : adjAt T c j with
    | none => rfl
    | some q => rw [adj_eq] at mate_formula; exact absurd (unglued.symm.trans mate_formula) (by simp)
  exact ownGo_surj (pcs T) (pcs_cover T c_lt j_lt on_rim) o_lt

/-- Different parent rim positions are different edges. -/
theorem own_inj (len_pos : ∀ c j, 1 ≤ L c j) {p p' : Nat} (p_lt : p < rimN T L) (p_lt' : p' < rimN T L)
    (same_edge : ownGo L (pcs T) p = ownGo L (pcs T) p') : p = p' :=
  ownGo_inj (fun c j _ => len_pos c j) (pcs T) (pcs_nodup T) (fun x mem => (pcs_valid T x mem).2.1) p p' p_lt p_lt'
    same_edge

/-- **The parent's rim, read from Table 3, is consistent with turning about its vertices**: from the end of the edge
at position `p` (in the children's sense), turning about the vertex reaches the edge at position `p - 1`. -/
theorem own_rot (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.Rot ((ownGo L (pcs T) p).1,
      nxt ((Comp.ofLens T L d ω).toGluing.E (ownGo L (pcs T) p).1) (ownGo L (pcs T) p).2)
      (ownGo L (pcs T) (prv (rimN T L) p)) := by
  by_cases p_zero : p = 0
  · -- position 0: the step back wraps round to the last position, and Table 3's wrap check applies
    subst p_zero
    -- Table 3 is not empty
    have nonempty := pcs_ne T
    -- Table 3 is its last piece after the others
    have split_last := List.dropLast_concat_getLast nonempty
    obtain ⟨c_lt, j_lt, _⟩ := pcs_valid T _ (List.head_mem nonempty)
    obtain ⟨c_lt_last, j_lt_last, _⟩ := pcs_valid T _ (List.getLast_mem nonempty)
    -- position 0 is the last edge of the first piece's side
    have at_zero : ownGo L (pcs T) 0 = (((pcs T).head nonempty).1,
        pos (L ((pcs T).head nonempty).1) ((pcs T).head nonempty).2 +
          L ((pcs T).head nonempty).1 ((pcs T).head nonempty).2 - 1) := by
      conv => lhs; rw [← List.cons_head_tail nonempty]
      exact ownGo_zero (len_pos _ _)
    -- the last position is the first edge of the last piece's side
    have at_last : ownGo L (pcs T) (prv (rimN T L) 0) = (((pcs T).getLast nonempty).1,
        pos (L ((pcs T).getLast nonempty).1) ((pcs T).getLast nonempty).2) := by
      simp only [prv, rimN, if_true]
      conv => lhs; rw [← split_last]
      exact ownGo_last (len_pos _ _) _
    rw [at_zero, at_last, ofLens_E c_lt, nxt_last (len_pos _) j_lt]
    exact rot_tab len_pos 30 _ _ _ _ (pcs_wrap T) c_lt (Nat.mod_lt _ (by omega))
  · -- a later position
    -- the step back is to `p - 1`
    have prv_eq : prv (rimN T L) p = p - 1 := by simp only [prv]; rw [if_neg p_zero]
    rw [prv_eq]
    rcases ownGo_pred len_pos (pcs T) p (by omega) p_lt with
      ⟨c, j, o, mem, o_lt, at_p, at_prev⟩ | ⟨c, j, c', j', consec, at_p, at_prev⟩
    · -- inside a piece: the next edge of the same side, and that side is on the parent's rim
      obtain ⟨c_lt, j_lt, on_rim⟩ := pcs_valid T _ mem
      rw [at_p, at_prev, ofLens_E c_lt]
      -- side `j` ends no later than the rim
      have side_end := pos_mono (L c) (show j + 1 ≤ 6 by omega)
      rw [pos_succ] at side_end
      -- so the next position does not wrap round
      have nxt_eq : nxt (pos (L c) 6) (pos (L c) j + o) = pos (L c) j + (o + 1) := by
        simp only [nxt]; rw [if_neg (by omega)]; omega
      rw [nxt_eq, ← Nat.add_assoc]
      -- the next edge is unglued, so turning stops at once
      have unglued := ofLens_mate_none (d := d) (ω := ω) len_pos c_lt j_lt o_lt on_rim
      rw [← Nat.add_assoc] at unglued
      exact .stop unglued
    · -- at the start of a piece: turning about the vertex leads to the previous piece, by Table 3's check
      -- the piece is in Table 3
      have mem : (c, j) ∈ pcs T := (Consec.mem consec).2
      obtain ⟨c_lt, j_lt, _⟩ := pcs_valid T _ mem
      rw [at_p, at_prev, ofLens_E c_lt, nxt_last (len_pos _) j_lt]
      exact rot_tab len_pos 30 _ _ _ _ (pcs_consec T consec) c_lt (Nat.mod_lt _ (by omega))

end Rot

end SpectreKnot.Statement
