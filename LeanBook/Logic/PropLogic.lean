#check Prop

-- これは命題
#check (1 + 1 = 3 : Prop)

-- これは命題ではなく、命題への関数
#check (fun n => n + 3 = 39 : Nat -> Prop)

#check True

#check False

/--Trueは何も主張していないので、何もなくても示せる-/
example : True := by trivial

example (P : Prop) (h : P) : P := by
  exact h

example (P Q R : Prop) : (P -> Q -> R) = (P -> (Q -> R)) := by
  rfl

#eval True -> True

#eval True -> False

#eval False -> True

#eval False -> False

/-- いわゆるモーダスレスポンス (三段論法) -/
example (P Q : Prop) (h : P -> Q) (hp : P) : Q := by
  -- P -> Qが成り立つので、Qを示すにはPを示せばよい
  apply h

  -- Pの成立はわかっているので、照明終わり
  apply hp

example (P Q : Prop) (h : P -> Q) (hp : P) : Q := by
  exact h hp

/-- 含意の導入 -/
example (P Q : Prop) (hq : Q) : P -> Q := by
  -- P -> Qを示したいのでPであると仮定する
  intro hp

  -- 後はQを示せばよいが、これは仮定されていたのであった
  exact hq

#eval ¬ True

#eval ¬ False

/-- Pと仮定すると矛盾する、ということは ¬ P と等しい-/
example (P: Prop) : (¬ P) = (P -> False) := by
  rfl

/-- Pと ¬Pを当時に仮定すると矛盾する -/
example (P: Prop) (hnp : ¬ P) (hp : P) : False := by
  -- ¬PはP -> Falseに等しいので、Pを示せばよい
  apply hnp

  -- 仮定 hp : Pがあるので、証明終わり
  exact hp

/-- 対偶が元の命題と同値になることの、片方のケース -/
example (P Q : Prop) (h : P → ¬Q) : Q → ¬P := by
  -- Qならば ¬Pを示したいのでQであったと仮定する
  intro hq

  -- ¬PはP -> Falseに等しいので
  -- さらにPであったと仮定する
  intro hp

  --仮定h:P→Q→Falseに適用してFalseが得られる
  exact h hp hq

example (P : Prop) (hnp : ¬P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  -- 矛盾を示せばよい
  exfalso

  -- 仮定に矛盾があるので証明終わり
  contradiction

-- 同値性
#eval True ↔ True

#eval True ↔ False

#eval False ↔ True

#eval False ↔ False

example(P Q : Prop) (h1 : P → Q)(h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example(P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  -- 両方向を示すことで証明する
  constructor

  -- まず左から右を示す
  case mp =>
    intro h
    exact h hq

  -- 右から左を示す
  case mpr =>
    intro hp hq
    exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h

  case mp =>
    exact h hq

  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P ↔ Qが仮定にあるので、Pの代わりにQを示せばよい
  rw [h]

  -- 仮定hq : Qがあるので、照明終わり
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw[← h]
  exact hp

/-- 同値な命題は等しい -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

#eval True ∧ True

#eval True ∧ False

#eval False ∧ True

#eval False ∧ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

-- 論理和
#eval True ∨ True

#eval True ∨ False

#eval False ∨ True

#eval False ∨ False

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) : (¬P ∨ Q) → (P → Q) := by
  intro h
  intro p
  cases h with
  | inl np =>
      contradiction
  | inr q =>
      exact q

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h1
  · constructor <;> intro h2
    · apply h1
      left
      exact h2
    · apply h1
      right
      exact h2
  · intro hpq
    cases hpq with
    | inl hp =>
        exact h1.1 hp
    | inr hq =>
        exact h1.2 hq
