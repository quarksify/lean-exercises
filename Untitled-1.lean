variables p q r s : Prop

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
assume hpq : p ∧ q,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
show q ∧ p, from and.intro hq hp

theorem or_commutative (p q : Prop) : p ∨ q → q ∨ p :=
assume hpq : p ∨ q,
show q ∨ p,
from or.elim hpq
    (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
    (assume hq: q,
    show q ∨ p, from or.intro_left p hq)

theorem and_associ (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
have hpq : p ∧ q, from and.left h,
have hr : r, from and.right h,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
have hqr : q ∧ r, from and.intro hq hr,
show p ∧ (q ∧ r), from and.intro hp hqr

theorem or_associ (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) :=
show p ∨ (q ∨ r),
from or.elim h
    (assume hpq : p ∨ q,
    show p ∨ (q ∨ r), from
    or.elim hpq
        (assume hp : p, or.inl hp)
        (assume hq : q, or.inr (or.inl hq))
    )
    (assume hr : r,
    show p ∨ (q ∨ r), from
    or.intro_right p (or.intro_right q hr))

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    apply or.elim (and.right h),
      intro hq,
      apply or.inl,
      apply and.intro,
        exact and.left h,
      exact hq,
    intro hr,
    apply or.inr,
    apply and.intro,
      exact and.left h,
    exact hr,
  intro h,
  apply or.elim h,
    intro hpq,
    apply and.intro,
      exact and.left hpq,
    apply or.inl,
    exact and.right hpq,
  intro hpr,
  apply and.intro,
    exact and.left hpr,
  apply or.inr,
  exact and.right hpr
end

theorem and_associ_tac (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
begin
apply and.intro,
exact and.left (and.left h),
apply and.intro,
exact and.right (and.left h),
exact and.right h
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  assumption,
  assumption
end