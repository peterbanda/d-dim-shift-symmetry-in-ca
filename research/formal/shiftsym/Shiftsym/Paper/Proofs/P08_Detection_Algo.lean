/-
Group 08 (paper §9, Detection): lemmas about the frozen algorithm model
(`compareTail`, `walkOrbit`, `orbitWalk`, `subgroupTestAux`, `detect`).
Helper module of `P08_Detection.lean`.
-/
import Shiftsym.Paper.S08_Detection
import Shiftsym.Lemmas.Lines
import Shiftsym.Lemmas.Completeness
import Shiftsym.Lemmas.FixedCount
import Shiftsym.Lemmas.Ineq

namespace ShiftSym.P08

open ShiftSym

section Walk

variable {n d : ℕ} {A : Type*} [DecidableEq A]

theorem compareTail_reads_le (st : Bool) (s : Config n d A) (a : A) (l : List (Lat n d)) :
    (compareTail st s a l).2 ≤ l.length := by
  induction l with
  | nil => simp [compareTail]
  | cons x xs ih =>
    simp only [compareTail]
    split_ifs <;> simp <;> omega

theorem compareTail_fst (st : Bool) (s : Config n d A) (a : A) (l : List (Lat n d)) :
    (compareTail st s a l).1 = true ↔ ∀ x ∈ l, s x = a := by
  induction l with
  | nil => simp [compareTail]
  | cons x xs ih =>
    simp only [compareTail]
    split_ifs with h1 h2
    · simp [ih, h1]
    · simp [h1]
    · simp [h1]

theorem compareTail_reads_of_pass (st : Bool) (s : Config n d A) (a : A) (l : List (Lat n d))
    (h : (compareTail st s a l).1 = true) : (compareTail st s a l).2 = l.length := by
  induction l with
  | nil => simp [compareTail]
  | cons x xs ih =>
    simp only [compareTail] at h ⊢
    split_ifs at h ⊢ with h1 h2 <;> simp_all

theorem compareTail_reads_false (s : Config n d A) (a : A) (l : List (Lat n d)) :
    (compareTail false s a l).2 = l.length := by
  induction l with
  | nil => simp [compareTail]
  | cons x xs ih =>
    simp only [compareTail]
    split_ifs <;> simp_all

theorem compareTail_congr (st : Bool) {s s' : Config n d A} (a : A) (l : List (Lat n d))
    (h : ∀ x ∈ l, s x = s' x) : compareTail st s a l = compareTail st s' a l := by
  induction l with
  | nil => simp [compareTail]
  | cons x xs ih =>
    have hx : s x = s' x := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [compareTail, hx, ih']

theorem walkOrbit_reads_le (st : Bool) (s : Config n d A) (l : List (Lat n d)) :
    (walkOrbit st s l).2 ≤ l.length := by
  cases l with
  | nil => simp [walkOrbit]
  | cons a rest =>
    have := compareTail_reads_le st s (s a) rest
    simp [walkOrbit]; omega

theorem walkOrbit_fst_cons (st : Bool) (s : Config n d A) (a : Lat n d) (rest : List (Lat n d)) :
    (walkOrbit st s (a :: rest)).1 = true ↔ ∀ x ∈ a :: rest, s x = s a := by
  simp [walkOrbit, compareTail_fst]

theorem walkOrbit_reads_of_pass (st : Bool) (s : Config n d A) (l : List (Lat n d))
    (h : (walkOrbit st s l).1 = true) : (walkOrbit st s l).2 = l.length := by
  cases l with
  | nil => simp [walkOrbit]
  | cons a rest =>
    simp only [walkOrbit] at h ⊢
    rw [compareTail_reads_of_pass st s (s a) rest h]; simp

theorem walkOrbit_reads_false (s : Config n d A) (l : List (Lat n d)) :
    (walkOrbit false s l).2 = l.length := by
  cases l with
  | nil => simp [walkOrbit]
  | cons a rest =>
    simp only [walkOrbit]; rw [compareTail_reads_false]; simp

theorem walkOrbit_congr (st : Bool) {s s' : Config n d A} (l : List (Lat n d))
    (h : ∀ x ∈ l, s x = s' x) : walkOrbit st s l = walkOrbit st s' l := by
  cases l with
  | nil => simp [walkOrbit]
  | cons a rest =>
    have ha : s a = s' a := h a (by simp)
    simp only [walkOrbit, ha]
    rw [compareTail_congr st (s' a) rest (fun y hy => h y (by simp [hy]))]

end Walk

section Orbit

variable {n d : ℕ}

theorem orbitWalk_length (p : ℕ) (w u : Lat n d) : (orbitWalk p w u).length = p := by
  simp [orbitWalk]

theorem mem_orbitWalk {p : ℕ} {w u x : Lat n d} :
    x ∈ orbitWalk p w u ↔ ∃ k < p, u + k • w = x := by
  simp [orbitWalk]

theorem orbitWalk_succ (q : ℕ) (w u : Lat n d) :
    orbitWalk (q + 1) w u = u :: (List.range q).map (fun k => u + (k + 1) • w) := by
  simp [orbitWalk, List.range_succ_eq_map, Function.comp_def]

theorem orbitWalk_nodup {p : ℕ} {w : Lat n d} (hw : addOrderOf w = p) (u : Lat n d) :
    (orbitWalk p w u).Nodup := by
  unfold orbitWalk
  refine List.Nodup.map_on ?_ (List.nodup_range)
  intro a ha b hb hab
  have hab' : a • w = b • w := add_left_cancel hab
  have ha' : a ∈ Set.Iio (addOrderOf w) := by
    rw [hw]; exact List.mem_range.mp ha
  have hb' : b ∈ Set.Iio (addOrderOf w) := by
    rw [hw]; exact List.mem_range.mp hb
  exact nsmul_injOn_Iio_addOrderOf ha' hb' hab'

theorem orbitWalk_card {p : ℕ} {w : Lat n d} (hw : addOrderOf w = p) (u : Lat n d) :
    (orbitWalk p w u).toFinset.card = p := by
  rw [List.toFinset_card_of_nodup (orbitWalk_nodup hw u), orbitWalk_length]

theorem self_mem_orbitWalk {p : ℕ} (hp : 0 < p) (w u : Lat n d) : u ∈ orbitWalk p w u :=
  mem_orbitWalk.mpr ⟨0, hp, by simp⟩

theorem add_nsmul_mem_orbitWalk {p : ℕ} (hp : 0 < p) {w : Lat n d} (hpw : p • w = 0)
    (u : Lat n d) (m : ℕ) : u + m • w ∈ orbitWalk p w u := by
  rw [mem_orbitWalk]
  refine ⟨m % p, Nat.mod_lt _ hp, ?_⟩
  conv_rhs => rw [← Nat.mod_add_div m p]
  rw [add_nsmul, mul_nsmul, hpw, nsmul_zero, add_zero]

theorem orbitWalk_subset {p : ℕ} (hp : 0 < p) {w : Lat n d} (hpw : p • w = 0)
    {u u' x : Lat n d} (hu' : u' ∈ orbitWalk p w u) (hx : x ∈ orbitWalk p w u') :
    x ∈ orbitWalk p w u := by
  obtain ⟨j, -, rfl⟩ := mem_orbitWalk.mp hu'
  obtain ⟨k, -, rfl⟩ := mem_orbitWalk.mp hx
  rw [add_assoc, ← add_nsmul]
  exact add_nsmul_mem_orbitWalk hp hpw u _

end Orbit

section Closed

variable {n d : ℕ}

/-- A visited list closed under the translation by `w`. -/
def Closed (w : Lat n d) (V : List (Lat n d)) : Prop := ∀ x ∈ V, x + w ∈ V

theorem closed_nil (w : Lat n d) : Closed w [] := by simp [Closed]

theorem Closed.add_nsmul_mem {w : Lat n d} {V : List (Lat n d)} (hV : Closed w V) {x : Lat n d}
    (hx : x ∈ V) (k : ℕ) : x + k • w ∈ V := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [succ_nsmul, ← add_assoc]; exact hV _ ih

theorem Closed.of_add_nsmul {p : ℕ} (hp : 0 < p) {w : Lat n d} (hpw : p • w = 0)
    {V : List (Lat n d)} (hV : Closed w V) {x : Lat n d} {k : ℕ} (hx : x + k • w ∈ V) :
    x ∈ V := by
  have h := hV.add_nsmul_mem hx ((p - 1) * k)
  have hk : k + (p - 1) * k = p * k := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have : x + k • w + ((p - 1) * k) • w = x := by
    rw [add_assoc, ← add_nsmul, hk, mul_nsmul, hpw, nsmul_zero, add_zero]
  rwa [this] at h

theorem orbit_not_mem {p : ℕ} (hp : 0 < p) {w : Lat n d} (hpw : p • w = 0)
    {V : List (Lat n d)} (hV : Closed w V) {u : Lat n d} (hu : u ∉ V) {x : Lat n d}
    (hx : x ∈ orbitWalk p w u) : x ∉ V := by
  obtain ⟨k, -, rfl⟩ := mem_orbitWalk.mp hx
  exact fun h => hu (hV.of_add_nsmul hp hpw h)

theorem Closed.append_orbit {p : ℕ} (hp : 0 < p) {w : Lat n d} (hpw : p • w = 0)
    {V : List (Lat n d)} (hV : Closed w V) (u : Lat n d) :
    Closed w (V ++ orbitWalk p w u) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (hV x h)
  · apply List.mem_append_right
    obtain ⟨k, -, rfl⟩ := mem_orbitWalk.mp h
    rw [add_assoc, ← succ_nsmul]
    exact add_nsmul_mem_orbitWalk hp hpw u _

theorem card_append_orbit [NeZero n] {p : ℕ} (hp : 0 < p) {w : Lat n d} (hw : addOrderOf w = p)
    {V : List (Lat n d)} (hV : Closed w V) {u : Lat n d} (hu : u ∉ V) :
    (V ++ orbitWalk p w u).toFinset.card = V.toFinset.card + p := by
  have hpw : p • w = 0 := hw ▸ addOrderOf_nsmul_eq_zero w
  rw [List.toFinset_append, Finset.card_union_of_disjoint, orbitWalk_card hw]
  rw [Finset.disjoint_left]
  intro x hxV hxO
  exact orbit_not_mem hp hpw hV hu (List.mem_toFinset.mp hxO) (List.mem_toFinset.mp hxV)

end Closed

section Test

variable {n d : ℕ} {A : Type*} [DecidableEq A]

theorem walkOrbit_orbit_fst (st : Bool) (s : Config n d A) {p : ℕ} (hp : 0 < p)
    (w u : Lat n d) :
    (walkOrbit st s (orbitWalk p w u)).1 = true ↔ ∀ x ∈ orbitWalk p w u, s x = s u := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [orbitWalk_succ]
  exact walkOrbit_fst_cons st s u _

theorem subgroupTestAux_cons_mem (st : Bool) (s : Config n d A) (p : ℕ) (w : Lat n d)
    {u : Lat n d} {us V : List (Lat n d)} (hu : u ∈ V) :
    subgroupTestAux st s p w (u :: us) V = subgroupTestAux st s p w us V := by
  simp [subgroupTestAux, hu]

theorem subgroupTestAux_cons_not_mem (st : Bool) (s : Config n d A) (p : ℕ) (w : Lat n d)
    {u : Lat n d} {us V : List (Lat n d)} (hu : u ∉ V) :
    subgroupTestAux st s p w (u :: us) V =
      if (walkOrbit st s (orbitWalk p w u)).1 then
        ((subgroupTestAux st s p w us (V ++ orbitWalk p w u)).1,
          (subgroupTestAux st s p w us (V ++ orbitWalk p w u)).2.1 + 1,
          (subgroupTestAux st s p w us (V ++ orbitWalk p w u)).2.2
            + (walkOrbit st s (orbitWalk p w u)).2)
      else (false, 1, (walkOrbit st s (orbitWalk p w u)).2) := by
  simp [subgroupTestAux, hu]

omit [DecidableEq A] in
/-- Mono property of an orbit is inherited by every cell of the orbit. -/
theorem mono_of_mem_orbit {s : Config n d A} {p : ℕ} (hp : 0 < p) {w : Lat n d}
    (hpw : p • w = 0) {u u' : Lat n d} (hmono : ∀ x ∈ orbitWalk p w u, s x = s u)
    (hu' : u' ∈ orbitWalk p w u) : ∀ x ∈ orbitWalk p w u', s x = s u' := by
  intro x hx
  rw [hmono x (orbitWalk_subset hp hpw hu' hx), hmono u' hu']

/-- **Pass characterization**: the traversal passes iff every orbit of a not yet
visited cell is monochromatic. -/
theorem subgroupTestAux_fst (st : Bool) (s : Config n d A) {p : ℕ} (hp : 0 < p)
    {w : Lat n d} (hpw : p • w = 0) :
    ∀ (us V : List (Lat n d)), Closed w V →
      ((subgroupTestAux st s p w us V).1 = true ↔
        ∀ u ∈ us, u ∉ V → ∀ x ∈ orbitWalk p w u, s x = s u)
  | [], V, _ => by simp [subgroupTestAux]
  | u :: us, V, hV => by
    by_cases hu : u ∈ V
    · rw [subgroupTestAux_cons_mem st s p w hu, subgroupTestAux_fst st s hp hpw us V hV]
      constructor
      · intro h u' hu' hu'V
        rcases List.mem_cons.mp hu' with rfl | h'
        · exact absurd hu hu'V
        · exact h u' h' hu'V
      · intro h u' hu' hu'V
        exact h u' (List.mem_cons_of_mem _ hu') hu'V
    · have ih := subgroupTestAux_fst st s hp hpw us (V ++ orbitWalk p w u)
        (hV.append_orbit hp hpw u)
      rw [subgroupTestAux_cons_not_mem st s p w hu]
      by_cases hwk : (walkOrbit st s (orbitWalk p w u)).1 = true
      · rw [if_pos hwk]
        simp only
        rw [ih]
        have hmono := (walkOrbit_orbit_fst st s hp w u).mp hwk
        constructor
        · intro h u' hu' hu'V
          rcases List.mem_cons.mp hu' with rfl | h'
          · exact hmono
          · by_cases hO : u' ∈ orbitWalk p w u
            · exact mono_of_mem_orbit hp hpw hmono hO
            · exact h u' h' (by simp [hu'V, hO])
        · intro h u' hu' hu'V
          exact h u' (List.mem_cons_of_mem _ hu') (fun hh => hu'V (List.mem_append_left _ hh))
      · rw [if_neg hwk]
        simp only [Bool.false_eq_true, false_iff]
        intro h
        exact hwk ((walkOrbit_orbit_fst st s hp w u).mpr (h u List.mem_cons_self hu))

/-- **Locality**: the traversal only depends on the configuration outside the
visited set. -/
theorem subgroupTestAux_congr (st : Bool) {s s' : Config n d A} {p : ℕ} (hp : 0 < p)
    {w : Lat n d} (hpw : p • w = 0) :
    ∀ (us V : List (Lat n d)), Closed w V → (∀ x, x ∉ V → s x = s' x) →
      subgroupTestAux st s p w us V = subgroupTestAux st s' p w us V
  | [], V, _, _ => by simp [subgroupTestAux]
  | u :: us, V, hV, hss => by
    by_cases hu : u ∈ V
    · rw [subgroupTestAux_cons_mem st s p w hu, subgroupTestAux_cons_mem st s' p w hu]
      exact subgroupTestAux_congr st hp hpw us V hV hss
    · rw [subgroupTestAux_cons_not_mem st s p w hu, subgroupTestAux_cons_not_mem st s' p w hu]
      have hwk : walkOrbit st s (orbitWalk p w u) = walkOrbit st s' (orbitWalk p w u) :=
        walkOrbit_congr st _ (fun x hx => hss x (orbit_not_mem hp hpw hV hu hx))
      have ih := subgroupTestAux_congr st hp hpw us (V ++ orbitWalk p w u)
        (hV.append_orbit hp hpw u)
        (fun x hx => hss x (fun h => hx (List.mem_append_left _ h)))
      rw [hwk, ih]

/-- Reads are at most `p` times the number of orbits visited. -/
theorem subgroupTestAux_reads_le_mul (st : Bool) (s : Config n d A) (p : ℕ) (w : Lat n d) :
    ∀ (us V : List (Lat n d)),
      (subgroupTestAux st s p w us V).2.2 ≤ p * (subgroupTestAux st s p w us V).2.1
  | [], V => by simp [subgroupTestAux]
  | u :: us, V => by
    by_cases hu : u ∈ V
    · rw [subgroupTestAux_cons_mem st s p w hu]
      exact subgroupTestAux_reads_le_mul st s p w us V
    · rw [subgroupTestAux_cons_not_mem st s p w hu]
      have h1 := walkOrbit_reads_le st s (orbitWalk p w u)
      rw [orbitWalk_length] at h1
      have ih := subgroupTestAux_reads_le_mul st s p w us (V ++ orbitWalk p w u)
      split_ifs
      · simp only; rw [Nat.mul_add, Nat.mul_one]; omega
      · simp only; omega

/-- **Disjoint walks**: reads plus visited cells never exceed `N`. -/
theorem subgroupTestAux_reads_add_card_le [NeZero n] (st : Bool) (s : Config n d A) {p : ℕ}
    (hp : 0 < p) {w : Lat n d} (hw : addOrderOf w = p) :
    ∀ (us V : List (Lat n d)), Closed w V →
      (subgroupTestAux st s p w us V).2.2 + V.toFinset.card ≤ Fintype.card (Lat n d)
  | [], V, _ => by simpa [subgroupTestAux] using Finset.card_le_univ V.toFinset
  | u :: us, V, hV => by
    have hpw : p • w = 0 := hw ▸ addOrderOf_nsmul_eq_zero w
    by_cases hu : u ∈ V
    · rw [subgroupTestAux_cons_mem st s p w hu]
      exact subgroupTestAux_reads_add_card_le st s hp hw us V hV
    · rw [subgroupTestAux_cons_not_mem st s p w hu]
      have h1 := walkOrbit_reads_le st s (orbitWalk p w u)
      rw [orbitWalk_length] at h1
      have hc := card_append_orbit hp hw hV hu
      have hle := Finset.card_le_univ (V ++ orbitWalk p w u).toFinset
      have ih := subgroupTestAux_reads_add_card_le st s hp hw us (V ++ orbitWalk p w u)
        (hV.append_orbit hp hpw u)
      split_ifs
      · simp only; omega
      · simp only; omega

/-- **All orbits pass**: then every cell outside the visited set is read once. -/
theorem subgroupTestAux_reads_of_pass [NeZero n] (st : Bool) (s : Config n d A) {p : ℕ}
    (hp : 0 < p) {w : Lat n d} (hw : addOrderOf w = p) :
    ∀ (us V : List (Lat n d)), Closed w V → (∀ x, x ∈ us ∨ x ∈ V) →
      (subgroupTestAux st s p w us V).1 = true →
      (subgroupTestAux st s p w us V).2.2 + V.toFinset.card = Fintype.card (Lat n d)
  | [], V, _, hcov, _ => by
    have : V.toFinset = Finset.univ := by
      ext x; simpa using (hcov x).resolve_left (by simp)
    simp [subgroupTestAux, this]
  | u :: us, V, hV, hcov, hpass => by
    have hpw : p • w = 0 := hw ▸ addOrderOf_nsmul_eq_zero w
    by_cases hu : u ∈ V
    · rw [subgroupTestAux_cons_mem st s p w hu] at hpass ⊢
      refine subgroupTestAux_reads_of_pass st s hp hw us V hV ?_ hpass
      intro x
      rcases hcov x with h | h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inr hu
        · exact Or.inl h'
      · exact Or.inr h
    · rw [subgroupTestAux_cons_not_mem st s p w hu] at hpass ⊢
      have hc := card_append_orbit hp hw hV hu
      split_ifs at hpass ⊢ with hwk
      · simp only at hpass ⊢
        have hr := walkOrbit_reads_of_pass st s _ hwk
        rw [orbitWalk_length] at hr
        have ih := subgroupTestAux_reads_of_pass st s hp hw us (V ++ orbitWalk p w u)
          (hV.append_orbit hp hpw u) ?_ hpass
        · omega
        · intro x
          rcases hcov x with h | h
          · rcases List.mem_cons.mp h with rfl | h'
            · exact Or.inr (List.mem_append_right _ (self_mem_orbitWalk hp w x))
            · exact Or.inl h'
          · exact Or.inr (List.mem_append_left _ h)

/-- Conservative reading: a failing traversal reads at least one full orbit. -/
theorem subgroupTestAux_reads_ge_of_fail (s : Config n d A) (p : ℕ) (w : Lat n d) :
    ∀ (us V : List (Lat n d)), (subgroupTestAux false s p w us V).1 = false →
      p ≤ (subgroupTestAux false s p w us V).2.2
  | [], V, h => by simp [subgroupTestAux] at h
  | u :: us, V, h => by
    by_cases hu : u ∈ V
    · rw [subgroupTestAux_cons_mem false s p w hu] at h ⊢
      exact subgroupTestAux_reads_ge_of_fail s p w us V h
    · rw [subgroupTestAux_cons_not_mem false s p w hu] at h ⊢
      have hr := walkOrbit_reads_false s (orbitWalk p w u)
      rw [orbitWalk_length] at hr
      split_ifs at h ⊢
      · simp only at h ⊢
        have := subgroupTestAux_reads_ge_of_fail s p w us (V ++ orbitWalk p w u) h
        omega
      · simp only; omega

end Test

section Indep

/-- **Independence**: for a function `f` of the configuration that ignores the cells of `B`,
the event "`B` is monochromatic" has weight `σ / σ^|B|` against `f`. -/
theorem sum_mono_indep {L : Type*} [Fintype L] [DecidableEq L] (σ : ℕ) (B : Finset L)
    (a0 : L) (ha0 : a0 ∈ B) (f : (L → Fin σ) → ℝ)
    (hf : ∀ s s' : L → Fin σ, (∀ x, x ∉ B → s x = s' x) → f s = f s') :
    (σ : ℝ) ^ B.card * ∑ s : L → Fin σ, (if ∀ x ∈ B, s x = s a0 then f s else 0)
      = σ * ∑ s : L → Fin σ, f s := by
  classical
  rcases Nat.eq_zero_or_pos σ with hσ | hσ
  · subst hσ
    have : IsEmpty (L → Fin 0) := ⟨fun s => (s a0).elim0⟩
    simp
  set e := Equiv.piEquivPiSubtypeProd (fun x => x ∈ B) (fun _ => Fin σ) with he
  have hsum : ∀ g : (L → Fin σ) → ℝ, ∑ s, g s = ∑ a, ∑ b, g (e.symm (a, b)) := by
    intro g
    rw [← Equiv.sum_comp e.symm g, Fintype.sum_prod_type]
  have hval : ∀ a b x, (e.symm (a, b)) x = if h : x ∈ B then a ⟨x, h⟩ else b ⟨x, h⟩ := by
    intro a b x; rfl
  set c0 : {x // x ∈ B} → Fin σ := fun _ => ⟨0, hσ⟩ with hc0
  set G : ({x // x ∈ B} → Fin σ) → ℝ := fun a => ∑ b, f (e.symm (a, b)) with hG
  have hGc : ∀ a, G a = G c0 := by
    intro a
    simp only [hG]
    refine Finset.sum_congr rfl (fun b _ => hf _ _ ?_)
    intro x hx
    rw [hval, hval, dif_neg hx, dif_neg hx]
  have hmono : ∀ a b, (∀ x ∈ B, (e.symm (a, b)) x = (e.symm (a, b)) a0) ↔
      ∀ x : {x // x ∈ B}, a x = a ⟨a0, ha0⟩ := by
    intro a b
    constructor
    · intro h x
      have := h x.1 x.2
      rwa [hval, hval, dif_pos x.2, dif_pos ha0] at this
    · intro h x hx
      rw [hval, hval, dif_pos hx, dif_pos ha0]
      exact h ⟨x, hx⟩
  have hcard : (Finset.univ.filter fun a : {x // x ∈ B} → Fin σ =>
      ∀ x, a x = a ⟨a0, ha0⟩).card = σ := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr (β := Fin σ)
      { toFun := fun a => a.1 ⟨a0, ha0⟩
        invFun := fun c => ⟨fun _ => c, fun _ => rfl⟩
        left_inv := fun a => Subtype.ext (funext fun x => (a.2 x).symm)
        right_inv := fun c => rfl }]
    simp
  have hcardB : Fintype.card ({x // x ∈ B} → Fin σ) = σ ^ B.card := by
    simp
  rw [hsum, hsum]
  have hL : ∀ a, (∑ b, if ∀ x ∈ B, (e.symm (a, b)) x = (e.symm (a, b)) a0
      then f (e.symm (a, b)) else 0)
      = if (∀ x : {x // x ∈ B}, a x = a ⟨a0, ha0⟩) then G c0 else 0 := by
    intro a
    by_cases h : ∀ x : {x // x ∈ B}, a x = a ⟨a0, ha0⟩
    · rw [if_pos h, ← hGc a]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [if_pos ((hmono a b).mpr h)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg (fun h' => h ((hmono a b).mp h'))]
  simp only [hL]
  have hR : ∀ a, (∑ b, f (e.symm (a, b))) = G c0 := fun a => hGc a
  simp only [hR]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.sum_const,
    hcard, Finset.card_univ, hcardB]
  simp only [nsmul_eq_mul]
  push_cast
  ring

end Indep

section Expect

variable {n d : ℕ}

theorem zpow_one_sub_mul_pow {σ : ℕ} (hσ : 0 < σ) (p : ℕ) :
    ((σ : ℝ) ^ ((1 : ℤ) - p)) * (σ : ℝ) ^ p = σ := by
  have hσ0 : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [← zpow_natCast, ← zpow_add₀ hσ0]
  simp

/-- **Exact orbit sum** (Proposition 9.2 (i), summed form): over all configurations,
the number of orbits visited sums to `σ^N · Σ_{i<k} Q^i`, `k` = number of orbits not yet
visited. -/
theorem sum_orbits_eq [NeZero n] (st : Bool) {σ : ℕ} (hσ : 0 < σ) {p : ℕ} (hp : 0 < p)
    {w : Lat n d} (hw : addOrderOf w = p) :
    ∀ (us V : List (Lat n d)) (k : ℕ), Closed w V → (∀ x, x ∈ us ∨ x ∈ V) →
      V.toFinset.card + p * k = Fintype.card (Lat n d) →
      ∑ s : Config n d (Fin σ), ((subgroupTestAux st s p w us V).2.1 : ℝ)
        = (σ : ℝ) ^ Fintype.card (Lat n d) *
            ∑ i ∈ Finset.range k, ((σ : ℝ) ^ ((1 : ℤ) - p)) ^ i
  | [], V, k, _, hcov, hk => by
    have hV : V.toFinset = Finset.univ := by
      ext x; simpa using (hcov x).resolve_left (by simp)
    rw [hV, Finset.card_univ] at hk
    have hk0 : k = 0 := by
      have : p * k = 0 := by omega
      rcases Nat.mul_eq_zero.mp this with h | h
      · omega
      · exact h
    subst hk0
    simp [subgroupTestAux]
  | u :: us, V, k, hV, hcov, hk => by
    have hpw : p • w = 0 := hw ▸ addOrderOf_nsmul_eq_zero w
    by_cases hu : u ∈ V
    · simp only [subgroupTestAux_cons_mem _ _ p w hu]
      refine sum_orbits_eq st hσ hp hw us V k hV ?_ hk
      intro x
      rcases hcov x with h | h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inr hu
        · exact Or.inl h'
      · exact Or.inr h
    · have hc := card_append_orbit hp hw hV hu
      have hle := Finset.card_le_univ (V ++ orbitWalk p w u).toFinset
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
        rcases k with _ | k'
        · omega
        · exact ⟨k', rfl⟩
      have hk' : (V ++ orbitWalk p w u).toFinset.card + p * k' = Fintype.card (Lat n d) := by
        rw [hc]; rw [Nat.mul_succ] at hk; omega
      have hV' := hV.append_orbit hp hpw u
      have hcov' : ∀ x, x ∈ us ∨ x ∈ V ++ orbitWalk p w u := by
        intro x
        rcases hcov x with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inr (List.mem_append_right _ (self_mem_orbitWalk hp w x))
          · exact Or.inl h'
        · exact Or.inr (List.mem_append_left _ h)
      have ih := sum_orbits_eq st hσ hp hw us (V ++ orbitWalk p w u) k' hV' hcov' hk'
      set c' : Config n d (Fin σ) → ℝ :=
        fun s => ((subgroupTestAux st s p w us (V ++ orbitWalk p w u)).2.1 : ℝ) with hc'
      have hstep : ∀ s : Config n d (Fin σ),
          ((subgroupTestAux st s p w (u :: us) V).2.1 : ℝ)
            = 1 + (if ∀ x ∈ (orbitWalk p w u).toFinset, s x = s u then c' s else 0) := by
        intro s
        rw [subgroupTestAux_cons_not_mem st s p w hu]
        have hiff : (walkOrbit st s (orbitWalk p w u)).1 = true ↔
            ∀ x ∈ (orbitWalk p w u).toFinset, s x = s u := by
          rw [walkOrbit_orbit_fst st s hp w u]; simp
        by_cases hwk : (walkOrbit st s (orbitWalk p w u)).1 = true
        · rw [if_pos hwk, if_pos (hiff.mp hwk)]; simp only [hc']; push_cast; ring
        · rw [if_neg hwk, if_neg (fun h => hwk (hiff.mpr h))]; simp
      simp only [hstep]
      rw [Finset.sum_add_distrib]
      have hind := sum_mono_indep σ (orbitWalk p w u).toFinset u
        (List.mem_toFinset.mpr (self_mem_orbitWalk hp w u)) c' (by
          intro s s' hss
          simp only [hc']
          rw [subgroupTestAux_congr st hp hpw us _ hV' (fun x hx => hss x (by
            intro hxO; exact hx (List.mem_append_right _ (List.mem_toFinset.mp hxO))))])
      rw [orbitWalk_card hw] at hind
      have hσ0 : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ.ne'
      have hσp : (σ : ℝ) ^ p ≠ 0 := pow_ne_zero _ hσ0
      have hX : (∑ s : Config n d (Fin σ),
          (if ∀ x ∈ (orbitWalk p w u).toFinset, s x = s u then c' s else 0))
          = ((σ : ℝ) ^ ((1 : ℤ) - p)) * ∑ s, c' s := by
        have hQ := zpow_one_sub_mul_pow hσ p
        apply mul_left_cancel₀ hσp
        calc (σ : ℝ) ^ p * (∑ s : Config n d (Fin σ),
              (if ∀ x ∈ (orbitWalk p w u).toFinset, s x = s u then c' s else 0))
            = σ * ∑ s, c' s := hind
          _ = (((σ : ℝ) ^ ((1 : ℤ) - p)) * (σ : ℝ) ^ p) * ∑ s, c' s := by rw [hQ]
          _ = (σ : ℝ) ^ p * (((σ : ℝ) ^ ((1 : ℤ) - p)) * ∑ s, c' s) := by ring
      rw [hX]
      have ih' : ∑ s, c' s = (σ : ℝ) ^ Fintype.card (Lat n d) *
          ∑ i ∈ Finset.range k', ((σ : ℝ) ^ ((1 : ℤ) - p)) ^ i := ih
      rw [ih']
      have h1 : ∑ _s : Config n d (Fin σ), (1 : ℝ) = (σ : ℝ) ^ Fintype.card (Lat n d) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have : Fintype.card (Config n d (Fin σ)) = σ ^ Fintype.card (Lat n d) := by
          simp only [Config, Fintype.card_fun, Fintype.card_fin]
        rw [this]; push_cast; rfl
      rw [h1]
      set Q : ℝ := (σ : ℝ) ^ ((1 : ℤ) - p) with hQdef
      have hgeom : ∑ i ∈ Finset.range k', Q ^ (i + 1) = Q * ∑ i ∈ Finset.range k', Q ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [Finset.sum_range_succ', hgeom]
      ring

end Expect

section Defect

variable {n d : ℕ}

/-- The single-defect configuration: symbol `1` at `x0`, symbol `0` elsewhere. -/
def defect {σ : ℕ} (hσ : 2 ≤ σ) (x0 : Lat n d) : Config n d (Fin σ) :=
  fun y => if y = x0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem card_filter_not_mem [NeZero n] (V : List (Lat n d)) :
    (Finset.univ.filter fun x => x ∉ V).card = Fintype.card (Lat n d) - V.toFinset.card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : Lat n d => x ∈ V)
  have hV : (Finset.univ.filter fun x : Lat n d => x ∈ V) = V.toFinset := by
    ext x; simp
  rw [hV, Finset.card_univ] at h
  omega

/-- **Single-defect sum**: summed over the defect position `x0` outside the visited
set, the reads of the traversal are at least `p² k (k-1) / 2`. -/
theorem sum_defect_reads_ge [NeZero n] (st : Bool) {σ : ℕ} (hσ : 2 ≤ σ) {p : ℕ} (hp : 0 < p)
    {w : Lat n d} (hw : addOrderOf w = p) :
    ∀ (us V : List (Lat n d)) (k : ℕ), Closed w V → (∀ x, x ∈ us ∨ x ∈ V) →
      V.toFinset.card + p * k = Fintype.card (Lat n d) →
      p * p * (k * (k - 1)) ≤ 2 * ∑ x0 ∈ Finset.univ.filter (fun x => x ∉ V),
        (subgroupTestAux st (defect hσ x0) p w us V).2.2
  | [], V, k, _, hcov, hk => by
    have hV : V.toFinset = Finset.univ := by
      ext x; simpa using (hcov x).resolve_left (by simp)
    rw [hV, Finset.card_univ] at hk
    have hk0 : k = 0 := by
      have : p * k = 0 := by omega
      rcases Nat.mul_eq_zero.mp this with h | h
      · omega
      · exact h
    subst hk0
    simp
  | u :: us, V, k, hV, hcov, hk => by
    have hpw : p • w = 0 := hw ▸ addOrderOf_nsmul_eq_zero w
    by_cases hu : u ∈ V
    · simp only [subgroupTestAux_cons_mem _ _ p w hu]
      refine sum_defect_reads_ge st hσ hp hw us V k hV ?_ hk
      intro x
      rcases hcov x with h | h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inr hu
        · exact Or.inl h'
      · exact Or.inr h
    · have hc := card_append_orbit hp hw hV hu
      have hle := Finset.card_le_univ (V ++ orbitWalk p w u).toFinset
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
        rcases k with _ | k'
        · omega
        · exact ⟨k', rfl⟩
      have hk' : (V ++ orbitWalk p w u).toFinset.card + p * k' = Fintype.card (Lat n d) := by
        rw [hc]; rw [Nat.mul_succ] at hk; omega
      have hV' := hV.append_orbit hp hpw u
      have hcov' : ∀ x, x ∈ us ∨ x ∈ V ++ orbitWalk p w u := by
        intro x
        rcases hcov x with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inr (List.mem_append_right _ (self_mem_orbitWalk hp w x))
          · exact Or.inl h'
        · exact Or.inr (List.mem_append_left _ h)
      have ih := sum_defect_reads_ge st hσ hp hw us (V ++ orbitWalk p w u) k' hV' hcov' hk'
      set T := Finset.univ.filter (fun x => x ∉ V) with hT
      set T' := Finset.univ.filter (fun x => x ∉ V ++ orbitWalk p w u) with hT'
      have hsub : T' ⊆ T := by
        intro x hx
        simp only [hT', hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact fun h => hx (List.mem_append_left _ h)
      have hcardT' : T'.card = p * k' := by
        rw [hT', card_filter_not_mem]; omega
      have hterm : ∀ x0 ∈ T', (subgroupTestAux st (defect hσ x0) p w (u :: us) V).2.2
          = (subgroupTestAux st (defect hσ x0) p w us (V ++ orbitWalk p w u)).2.2 + p := by
        intro x0 hx0
        simp only [hT', Finset.mem_filter, Finset.mem_univ, true_and] at hx0
        have hx0O : x0 ∉ orbitWalk p w u := fun h => hx0 (List.mem_append_right _ h)
        have hpass : (walkOrbit st (defect hσ x0) (orbitWalk p w u)).1 = true := by
          rw [walkOrbit_orbit_fst _ _ hp]
          intro x hx
          have hxx : x ≠ x0 := fun h => hx0O (h ▸ hx)
          have hux : u ≠ x0 := fun h => hx0O (h ▸ self_mem_orbitWalk hp w u)
          simp [defect, hxx, hux]
        have hr := walkOrbit_reads_of_pass st _ _ hpass
        rw [orbitWalk_length] at hr
        rw [subgroupTestAux_cons_not_mem _ _ p w hu, if_pos hpass]
        simp only; rw [hr]
      have h1 : ∑ x0 ∈ T', (subgroupTestAux st (defect hσ x0) p w (u :: us) V).2.2
          ≤ ∑ x0 ∈ T, (subgroupTestAux st (defect hσ x0) p w (u :: us) V).2.2 :=
        Finset.sum_le_sum_of_subset hsub
      have h2 : ∑ x0 ∈ T', (subgroupTestAux st (defect hσ x0) p w (u :: us) V).2.2
          = ∑ x0 ∈ T', (subgroupTestAux st (defect hσ x0) p w us (V ++ orbitWalk p w u)).2.2
            + p * (p * k') := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, hcardT',
          smul_eq_mul, Nat.mul_comm (p * k') p]
      have hkk : (k' + 1) * (k' + 1 - 1) = k' * (k' - 1) + 2 * k' := by
        rcases k' with _ | j
        · simp
        · simp only [Nat.add_sub_cancel]; ring
      calc p * p * ((k' + 1) * (k' + 1 - 1))
          = p * p * (k' * (k' - 1)) + 2 * (p * (p * k')) := by rw [hkk]; ring
        _ ≤ 2 * ∑ x0 ∈ T', (subgroupTestAux st (defect hσ x0) p w us
              (V ++ orbitWalk p w u)).2.2 + 2 * (p * (p * k')) := by omega
        _ = 2 * ∑ x0 ∈ T', (subgroupTestAux st (defect hσ x0) p w (u :: us) V).2.2 := by
              rw [h2]; ring
        _ ≤ 2 * ∑ x0 ∈ T, (subgroupTestAux st (defect hσ x0) p w (u :: us) V).2.2 := by omega

end Defect

section Detect

variable {n d : ℕ} {A : Type*} [DecidableEq A]

theorem detect_fst (st : Bool) (s : Config n d A) (ord : ℕ × Lat n d → List (Lat n d)) :
    ∀ sched : List (ℕ × Lat n d), (detect st s ord sched).1 = true ↔
      ∃ e ∈ sched, (subgroupTest st s (ord e) e.1 e.2).1 = true
  | [] => by simp [detect]
  | e :: rest => by
    simp only [detect]
    by_cases h : (subgroupTest st s (ord e) e.1 e.2).1 = true
    · rw [if_pos h]; simp only [true_iff]; exact ⟨e, List.mem_cons_self, h⟩
    · rw [if_neg h]; simp only
      rw [detect_fst st s ord rest]
      constructor
      · rintro ⟨e', he', h'⟩; exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
      · rintro ⟨e', he', h'⟩
        rcases List.mem_cons.mp he' with rfl | h''
        · exact absurd h' h
        · exact ⟨e', h'', h'⟩

theorem detect_reads_le_sum (st : Bool) (s : Config n d A) (ord : ℕ × Lat n d → List (Lat n d)) :
    ∀ sched : List (ℕ × Lat n d), (detect st s ord sched).2 ≤
      (sched.map fun e => (subgroupTest st s (ord e) e.1 e.2).2.2).sum
  | [] => by simp [detect]
  | e :: rest => by
    simp only [detect, List.map_cons, List.sum_cons]
    have ih := detect_reads_le_sum st s ord rest
    split_ifs
    · simp only; omega
    · simp only; omega

theorem detect_reads_eq_sum_of_fail (st : Bool) (s : Config n d A)
    (ord : ℕ × Lat n d → List (Lat n d)) :
    ∀ sched : List (ℕ × Lat n d), (∀ e ∈ sched, (subgroupTest st s (ord e) e.1 e.2).1 = false) →
      (detect st s ord sched).2 =
        (sched.map fun e => (subgroupTest st s (ord e) e.1 e.2).2.2).sum
  | [], _ => by simp [detect]
  | e :: rest, h => by
    simp only [detect, List.map_cons, List.sum_cons]
    have he := h e List.mem_cons_self
    have ih := detect_reads_eq_sum_of_fail st s ord rest
      (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    rw [if_neg (by rw [he]; simp)]
    simp only; rw [ih]

theorem detect_reads_cons_of_pass (st : Bool) (s : Config n d A)
    (ord : ℕ × Lat n d → List (Lat n d)) (e : ℕ × Lat n d) (rest : List (ℕ × Lat n d))
    (h : (subgroupTest st s (ord e) e.1 e.2).1 = true) :
    (detect st s ord (e :: rest)).2 = (subgroupTest st s (ord e) e.1 e.2).2.2 := by
  simp only [detect]; rw [if_pos h]

end Detect

section SubgroupTest

variable {n d : ℕ} {A : Type*} [DecidableEq A]

/-- A traversal order covers every cell. -/
theorem cov_of_traversal {ord : List (Lat n d)} (hord : IsTraversalOrder ord) :
    ∀ x, x ∈ ord ∨ x ∈ ([] : List (Lat n d)) := fun x => Or.inl (hord.2 x)

theorem subgroupTest_fst (st : Bool) (s : Config n d A) {ord : List (Lat n d)}
    (hord : IsTraversalOrder ord) {p : ℕ} (hp : 2 ≤ p) {w : Lat n d} (hpw : p • w = 0) :
    (subgroupTest st s ord p w).1 = true ↔ ∀ x, s (x + w) = s x := by
  unfold subgroupTest
  rw [subgroupTestAux_fst st s (by omega) hpw ord [] (closed_nil w)]
  constructor
  · intro h x
    have := h x (hord.2 x) (by simp) (x + 1 • w) (mem_orbitWalk.mpr ⟨1, by omega, rfl⟩)
    simpa using this
  · intro h u _ _ x hx
    obtain ⟨k, -, rfl⟩ := mem_orbitWalk.mp hx
    clear hx
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, ← add_assoc, h, ih]

theorem subgroupTest_reads_le [NeZero n] (st : Bool) (s : Config n d A) (ord : List (Lat n d))
    {p : ℕ} (hp : 0 < p) {w : Lat n d} (hw : addOrderOf w = p) :
    (subgroupTest st s ord p w).2.2 ≤ Fintype.card (Lat n d) := by
  have := subgroupTestAux_reads_add_card_le st s hp hw ord [] (closed_nil w)
  unfold subgroupTest; simpa using this

theorem subgroupTest_reads_le_mul (st : Bool) (s : Config n d A) (ord : List (Lat n d))
    (p : ℕ) (w : Lat n d) :
    (subgroupTest st s ord p w).2.2 ≤ p * (subgroupTest st s ord p w).2.1 :=
  subgroupTestAux_reads_le_mul st s p w ord []

theorem subgroupTest_reads_of_pass [NeZero n] (st : Bool) (s : Config n d A)
    {ord : List (Lat n d)} (hord : IsTraversalOrder ord) {p : ℕ} (hp : 0 < p) {w : Lat n d}
    (hw : addOrderOf w = p) (h : (subgroupTest st s ord p w).1 = true) :
    (subgroupTest st s ord p w).2.2 = Fintype.card (Lat n d) := by
  have := subgroupTestAux_reads_of_pass st s hp hw ord [] (closed_nil w)
    (cov_of_traversal hord) h
  unfold subgroupTest; simpa using this

theorem subgroupTest_reads_ge_of_fail (s : Config n d A) (ord : List (Lat n d)) (p : ℕ)
    (w : Lat n d) (h : (subgroupTest false s ord p w).1 = false) :
    p ≤ (subgroupTest false s ord p w).2.2 :=
  subgroupTestAux_reads_ge_of_fail s p w ord [] h

theorem card_div_mul [NeZero n] {p : ℕ} {w : Lat n d} (hw : addOrderOf w = p) :
    p * (Fintype.card (Lat n d) / p) = Fintype.card (Lat n d) :=
  Nat.mul_div_cancel' (hw ▸ addOrderOf_dvd_card)

/-- **Proposition 9.2 (i), summed form** for one subgroup test. -/
theorem subgroupTest_sum_orbits [NeZero n] (st : Bool) {σ : ℕ} (hσ : 0 < σ)
    {ord : List (Lat n d)} (hord : IsTraversalOrder ord) {p : ℕ} (hp : 0 < p) {w : Lat n d}
    (hw : addOrderOf w = p) :
    ∑ s : Config n d (Fin σ), ((subgroupTest st s ord p w).2.1 : ℝ)
      = (σ : ℝ) ^ Fintype.card (Lat n d) *
          ∑ i ∈ Finset.range (Fintype.card (Lat n d) / p), ((σ : ℝ) ^ ((1 : ℤ) - p)) ^ i :=
  sum_orbits_eq st hσ hp hw ord [] _ (closed_nil w) (cov_of_traversal hord)
    (by simpa using card_div_mul hw)

/-- **Single-defect sum** for one subgroup test. -/
theorem subgroupTest_sum_defect [NeZero n] (st : Bool) {σ : ℕ} (hσ : 2 ≤ σ)
    {ord : List (Lat n d)} (hord : IsTraversalOrder ord) {p : ℕ} (hp : 0 < p) {w : Lat n d}
    (hw : addOrderOf w = p) :
    p * p * ((Fintype.card (Lat n d) / p) * (Fintype.card (Lat n d) / p - 1)) ≤
      2 * ∑ x0 : Lat n d, (subgroupTest st (defect hσ x0) ord p w).2.2 := by
  have := sum_defect_reads_ge st hσ hp hw ord [] _ (closed_nil w) (cov_of_traversal hord)
    (by simpa using card_div_mul hw)
  simpa [subgroupTest] using this

end SubgroupTest

section Schedule

variable {n d : ℕ}

theorem schedule_nodup {sched : List (ℕ × Lat n d)} (h : IsSchedule sched) : sched.Nodup :=
  List.Nodup.of_map _ h.2.1

theorem schedule_mem_primeFactors (hn : n ≠ 0) {sched : List (ℕ × Lat n d)}
    (h : IsSchedule sched) {e : ℕ × Lat n d} (he : e ∈ sched) : e.1 ∈ n.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨(h.1 e he).1, (h.1 e he).2.1, hn⟩

/-- The entries of a schedule with prime `p` are in bijection with the order-`p`
subgroups, so there are `[d 1]_p` of them. -/
theorem schedule_filter_card [NeZero n] {sched : List (ℕ × Lat n d)} (h : IsSchedule sched)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (sched.toFinset.filter fun e => e.1 = p).card = gaussBinom p d 1 := by
  classical
  rw [← card_orderP_subgroups (d := d) hp hpn]
  set T := sched.toFinset.filter fun e => e.1 = p with hT
  have hmemT : ∀ e, e ∈ T ↔ e ∈ sched ∧ e.1 = p := by
    intro e; simp [hT]
  let f : {e // e ∈ T} → {C : AddSubgroup (Lat n d) // Nat.card C = p} := fun e =>
    ⟨AddSubgroup.zmultiples e.1.2, by
      rw [Nat.card_zmultiples]
      have he := (hmemT e.1).mp e.2
      rw [(h.1 e.1 he.1).2.2, he.2]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro e e' hee'
      have h1 : AddSubgroup.zmultiples e.1.2 = AddSubgroup.zmultiples e'.1.2 :=
        congrArg Subtype.val hee'
      exact Subtype.ext (List.inj_on_of_nodup_map h.2.1 ((hmemT e.1).mp e.2).1
        ((hmemT e'.1).mp e'.2).1 h1)
    · intro C
      have : Fact p.Prime := ⟨hp⟩
      have hcyc : IsAddCyclic C.1 := isAddCyclic_of_prime_card C.2
      obtain ⟨e, he, hC⟩ := h.2.2 C.1 ⟨p, hp, hpn, hcyc, C.2⟩
      have he1 : e.1 = p := by
        rw [← (h.1 e he).2.2, ← Nat.card_zmultiples, hC, C.2]
      exact ⟨⟨e, (hmemT e).mpr ⟨he, he1⟩⟩, Subtype.ext hC⟩
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Weighted count over a schedule: `Σ_{entries} g(p) = Σ_{p ∣ n} [d 1]_p g(p)`. -/
theorem schedule_sum [NeZero n] {sched : List (ℕ × Lat n d)} (h : IsSchedule sched)
    {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ e ∈ sched.toFinset, g e.1 = ∑ p ∈ n.primeFactors, gaussBinom p d 1 • g p := by
  classical
  have hmaps : ∀ e ∈ sched.toFinset, e.1 ∈ n.primeFactors := fun e he =>
    schedule_mem_primeFactors (NeZero.ne n) h (List.mem_toFinset.mp he)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' := Nat.mem_primeFactors.mp hp
  rw [← schedule_filter_card h hp'.1 hp'.2.1, ← Finset.sum_const]
  exact Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2])

theorem schedule_card [NeZero n] {sched : List (ℕ × Lat n d)} (h : IsSchedule sched) :
    sched.toFinset.card = sopfD n d := by
  have := schedule_sum h (fun _ => (1 : ℕ))
  simpa [sopfD] using this

theorem schedule_length [NeZero n] {sched : List (ℕ × Lat n d)} (h : IsSchedule sched) :
    sched.length = sopfD n d := by
  rw [← List.toFinset_card_of_nodup (schedule_nodup h), schedule_card h]

theorem schedule_filter_length [NeZero n] {sched : List (ℕ × Lat n d)} (h : IsSchedule sched)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (sched.filter fun e => decide (e.1 = p)).length = gaussBinom p d 1 := by
  rw [← List.toFinset_card_of_nodup ((schedule_nodup h).filter _), List.toFinset_filter]
  simpa using schedule_filter_card h hp hpn

theorem schedule_exists [NeZero n] : ∃ sched : List (ℕ × Lat n d), IsSchedule sched := by
  classical
  let _ : Fintype (AddSubgroup (Lat n d)) := Fintype.ofFinite _
  set S := Finset.univ.filter (fun C : AddSubgroup (Lat n d) => IsPrimeOrderCyclic C) with hS
  have hgen : ∀ C : AddSubgroup (Lat n d), ∃ g : Lat n d,
      IsPrimeOrderCyclic C → AddSubgroup.zmultiples g = C := by
    intro C
    by_cases hC : IsPrimeOrderCyclic C
    · obtain ⟨p, -, -, hcyc, -⟩ := hC
      obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hcyc
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hC⟩
  choose gen hgen using hgen
  refine ⟨S.toList.map (fun C : AddSubgroup (Lat n d) => (Nat.card C, gen C)), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨C, hCS, rfl⟩ := List.mem_map.mp he
    have hC : IsPrimeOrderCyclic C := (Finset.mem_filter.mp (Finset.mem_toList.mp hCS)).2
    obtain ⟨p, hp, hpn, -, hcard⟩ := hC
    refine ⟨hcard ▸ hp, hcard ▸ hpn, ?_⟩
    simp only
    rw [← Nat.card_zmultiples, hgen C ⟨p, hp, hpn, by
      have : Fact p.Prime := ⟨hp⟩; exact isAddCyclic_of_prime_card hcard, hcard⟩]
  · rw [List.map_map]
    have : ∀ C ∈ S.toList,
        ((fun e : ℕ × Lat n d => AddSubgroup.zmultiples e.2) ∘
          fun C : AddSubgroup (Lat n d) => (Nat.card C, gen C)) C
          = C := by
      intro C hC
      exact hgen C (Finset.mem_filter.mp (Finset.mem_toList.mp hC)).2
    rw [List.map_congr_left this, List.map_id']
    exact Finset.nodup_toList S
  · intro C hC
    refine ⟨(Nat.card C, gen C), List.mem_map.mpr ⟨C, ?_, rfl⟩, hgen C hC⟩
    exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩)

theorem traversal_exists [NeZero n] : ∃ ord : List (Lat n d), IsTraversalOrder ord :=
  ⟨Finset.univ.toList, Finset.nodup_toList _, fun u => Finset.mem_toList.mpr (Finset.mem_univ u)⟩

end Schedule

section Correct

variable {n d : ℕ}

/-- Lemma 3.4 in subgroup form (the correctness sentence of §9). -/
theorem completeness_iff [NeZero n] {σ : ℕ} (s : Config n d (Fin σ)) :
    IsShiftSymmetric s ↔
      ∃ C : AddSubgroup (Lat n d), IsPrimeOrderCyclic C ∧ s ∈ fixedBy (Fin σ) C := by
  rw [isShiftSymmetric_iff_prime_order]
  constructor
  · rintro ⟨v, hp, hpn, hfix⟩
    refine ⟨AddSubgroup.zmultiples v,
      ⟨addOrderOf v, hp, hpn, inferInstance, Nat.card_zmultiples v⟩, ?_⟩
    intro h hh
    have hle : AddSubgroup.zmultiples v ≤ stab s :=
      AddSubgroup.zmultiples_le.mpr (mem_stab.mpr hfix)
    exact mem_stab.mp (hle hh)
  · rintro ⟨C, ⟨p, hp, hpn, -, hcard⟩, hs⟩
    have : Nontrivial C := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]; exact hp.one_lt
    obtain ⟨g, hg⟩ := exists_ne (0 : C)
    have hord : addOrderOf g.1 = p :=
      addOrderOf_eq_of_mem_card_prime hp hcard g.2 (fun h => hg (Subtype.ext h))
    exact ⟨g.1, hord ▸ hp, hord ▸ hpn, hs g.1 g.2⟩

theorem entry_ne_zero {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {e : ℕ × Lat n d} (he : e ∈ sched) : e.2 ≠ 0 := by
  intro h0
  have hw := (hs.1 e he).2.2
  rw [h0, addOrderOf_zero] at hw
  exact (hs.1 e he).1.one_lt.ne hw

theorem entry_nsmul {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {e : ℕ × Lat n d} (he : e ∈ sched) : e.1 • e.2 = 0 :=
  (hs.1 e he).2.2 ▸ addOrderOf_nsmul_eq_zero e.2

/-- The test of a schedule entry passes iff the configuration is invariant under the
entry's generator. -/
theorem entry_test_iff {A : Type*} [DecidableEq A] {sched : List (ℕ × Lat n d)}
    (hs : IsSchedule sched) {ord : ℕ × Lat n d → List (Lat n d)}
    (hord : ∀ e ∈ sched, IsTraversalOrder (ord e)) (st : Bool) (s : Config n d A)
    {e : ℕ × Lat n d} (he : e ∈ sched) :
    (subgroupTest st s (ord e) e.1 e.2).1 = true ↔ shift e.2 s = s := by
  rw [subgroupTest_fst st s (hord e he) (hs.1 e he).1.two_le (entry_nsmul hs he)]
  constructor
  · intro h; exact funext fun x => h x
  · intro h x; exact congrFun h x

/-- **The algorithm is correct.** -/
theorem detect_correct [NeZero n] {σ : ℕ} {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {ord : ℕ × Lat n d → List (Lat n d)} (hord : ∀ e ∈ sched, IsTraversalOrder (ord e))
    (st : Bool) (s : Config n d (Fin σ)) :
    (detect st s ord sched).1 = true ↔ IsShiftSymmetric s := by
  rw [detect_fst]
  constructor
  · rintro ⟨e, he, hpass⟩
    exact ⟨e.2, entry_ne_zero hs he, (entry_test_iff hs hord st s he).mp hpass⟩
  · intro hsym
    obtain ⟨C, hC, hfix⟩ := (completeness_iff s).mp hsym
    obtain ⟨e, he, hgen⟩ := hs.2.2 C hC
    refine ⟨e, he, (entry_test_iff hs hord st s he).mpr ?_⟩
    exact hfix e.2 (hgen ▸ AddSubgroup.mem_zmultiples e.2)

/-- Union bound for prime `n`: at most `[d 1]_n σ^(N/n)` configurations are
shift-symmetric. -/
theorem card_sym_le [NeZero n] {σ : ℕ} (hn : n.Prime) :
    Nat.card {s : Config n d (Fin σ) // IsShiftSymmetric s}
      ≤ gaussBinom n d 1 * σ ^ (n ^ d / n) := by
  classical
  let _ : Fintype {C : AddSubgroup (Lat n d) // Nat.card C = n} := Fintype.ofFinite _
  have hcyc : ∀ C : {C : AddSubgroup (Lat n d) // Nat.card C = n}, IsAddCyclic C.1 := by
    intro C
    have : Fact n.Prime := ⟨hn⟩
    exact isAddCyclic_of_prime_card C.2
  let F : (Σ C : {C : AddSubgroup (Lat n d) // Nat.card C = n}, fixedBy (Fin σ) C.1) →
      {s : Config n d (Fin σ) // IsShiftSymmetric s} := fun x =>
    ⟨x.2.1, (completeness_iff _).mpr ⟨x.1.1, ⟨n, hn, dvd_refl n, hcyc x.1, x.1.2⟩, x.2.2⟩⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨s, hs⟩
    obtain ⟨C, ⟨p, hp, hpn, -, hcard⟩, hfix⟩ := (completeness_iff s).mp hs
    have hpn' : p = n := (Nat.prime_dvd_prime_iff_eq hp hn).mp hpn
    exact ⟨⟨⟨C, hpn' ▸ hcard⟩, ⟨s, hfix⟩⟩, rfl⟩
  have h1 := Nat.card_le_card_of_surjective F hsurj
  rw [Nat.card_sigma] at h1
  have hterm : ∀ C : {C : AddSubgroup (Lat n d) // Nat.card C = n},
      Nat.card (fixedBy (Fin σ) C.1) = σ ^ (n ^ d / n) := by
    intro C
    rw [card_fixedBy_div, C.2, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp only [hterm, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  rwa [← Nat.card_eq_fintype_card, card_orderP_subgroups hn (dvd_refl n)] at h1

end Correct

end ShiftSym.P08
